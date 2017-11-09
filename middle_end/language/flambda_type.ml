(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

module F0 = Flambda0
module K = Flambda_kind
module Named = F0.Named

module Float = Numbers.Float
module Int = Numbers.Int
module Int32 = Numbers.Int32
module Int64 = Numbers.Int64

include F0.Flambda_type

let unknown_types_from_arity t =
  List.map (fun kind -> unknown kind Other) t

let unknown_like ~importer ~type_of_name t =
  let kind = kind ~importer ~type_of_name t in
  unknown kind Other

let rename_variables ~importer:_ _t ~f:_ =
  assert false
(* XXX need to fix [Flambda_type0.clean]
  clean ~importer t (fun var -> Available_different_name (f var))
*)

let unresolved_symbol sym =
  any_value Can_scan (Unresolved_value (Name (Name.symbol sym)))

let this_tagged_immediate_named n : Named.t * t =
  Simple (Simple.const (Tagged_immediate n)), this_tagged_immediate n

let this_tagged_bool_named b : Named.t * t =
  let imm =
    if b then Immediate.bool_true
    else Immediate.bool_false
  in
  Simple (Simple.const (Tagged_immediate imm)), this_tagged_immediate imm

let this_untagged_immediate_named n : Named.t * t =
  Simple (Simple.const (Untagged_immediate n)), this_naked_immediate n

let this_naked_float_named f : Named.t * t =
  Simple (Simple.const (Naked_float f)), this_naked_float f

let this_naked_int32_named n : Named.t * t =
  Simple (Simple.const (Naked_int32 n)), this_naked_int32 n

let this_naked_int64_named n : Named.t * t =
  Simple (Simple.const (Naked_int64 n)), this_naked_int64 n

let this_naked_nativeint_named n : Named.t * t =
  Simple (Simple.const (Naked_nativeint n)), this_naked_nativeint n

(*
let is_float_array t =
  match descr t with
  | Float_array _ -> true
  | Unknown _ | Bottom | Union _
  | Immutable_string _ | Mutable_string _
  | Sets_of_closures _ | Closure _ | Load_lazily _ | Boxed_number _
  | Unboxed_float _ | Unboxed_int32 _ | Unboxed_int64 _
  | Unboxed_nativeint _ -> false

let type_for_bound_var (set_of_closures : set_of_closures) var =
  try Var_within_closure.Map.find var set_of_closures.bound_vars
  with Not_found ->
    Misc.fatal_errorf "The set-of-closures type %a@ does not \
        bind the variable %a@.%s@."
      print_set_of_closures set_of_closures
      Var_within_closure.print var
      (Printexc.raw_backtrace_to_string (Printexc.get_callstack max_int))

let physically_same_values (types : t list) =
  match types with
  | [] | [_] | _ :: _ :: _ :: _ ->
    Misc.fatal_error "wrong number of arguments for equality"
  | [a1; a2] ->
    (* N.B. The following would be incorrect if the variables are not
       bound in the environment:
       match a1.var, a2.var with
       | Some v1, Some v2 when Variable.equal v1 v2 -> true
       | _ -> ...
    *)
    match a1.symbol, a2.symbol with
    | Some (s1, None), Some (s2, None) -> Symbol.equal s1 s2
    | Some (s1, Some f1), Some (s2, Some f2) -> Symbol.equal s1 s2 && f1 = f2
    | _ -> false

let physically_different_values (types : t list) =
  let rec definitely_different (arg1 : t) (arg2 : t) =
    let module Int = Numbers.Int in
    let module Immediate = Unionable.Immediate in
    let immediates_different s1 s2 =
      (* The frontend isn't precise about "int" and "const pointer", for
         example generating "(!= b/1006 0)" for a match against a bool, which
         is a "const pointer".  The same presumably might happen with "char".
         As such for we treat immediates whose runtime representations are
         the same as equal. *)
      let s1 =
        Immediate.Set.fold (fun imm s1 ->
            Int.Set.add (Immediate.represents imm) s1)
          s1 Int.Set.empty
      in
      let s2 =
        Immediate.Set.fold (fun imm s2 ->
            Int.Set.add (Immediate.represents imm) s2)
          s2 Int.Set.empty
      in
      Int.Set.is_empty (Int.Set.inter s1 s2)
    in
    let blocks_different b1 b2 =
      let tags1 = Tag.Scannable.Map.keys b1 in
      let tags2 = Tag.Scannable.Map.keys b2 in
      let overlapping_tags = Tag.Scannable.Set.inter tags1 tags2 in
      Tag.Scannable.Set.exists (fun tag ->
          let fields1 = Tag.Scannable.Map.find tag b1 in
          let fields2 = Tag.Scannable.Map.find tag b2 in
          Array.length fields1 <> Array.length fields2
            || Misc.Stdlib.Array.exists2 definitely_different fields1 fields2)
        overlapping_tags
    in
    match arg1.descr, arg2.descr with
    | Unknown _, _ | _, Unknown _
    (* CR mshinwell: Should [Load_lazily] be an error here?  What about for the
       reification functions below?  [invalid_to_mutate] above has an
       assertion failure for this. *)
    | Load_lazily _, _ | _, Load_lazily _
    | Bottom, _ | _, Bottom -> false
    | Union (Immediates s1), Union (Immediates s2) ->
      immediates_different s1 s2
    | Union (Blocks b1), Union (Blocks b2) ->
      blocks_different b1 b2
    | Union (Blocks_and_immediates (b1, imms1)),
      Union (Blocks_and_immediates (b2, imms2)) ->
      immediates_different imms1 imms2 || blocks_different b1 b2
    | Union _, Union _ -> false
    | Union _, _ | _, Union _ -> true
    | Unboxed_float fs1, Unboxed_float fs2 ->
      Float.Set.is_empty (Float.Set.inter fs1 fs2)
    | Unboxed_float _, _ | _, Unboxed_float _ -> true
    | Unboxed_int32 ns1, Unboxed_int32 ns2 ->
      Int32.Set.is_empty (Int32.Set.inter ns1 ns2)
    | Unboxed_int32 _, _ | _, Unboxed_int32 _ -> true
    | Unboxed_int64 ns1, Unboxed_int64 ns2 ->
      Int64.Set.is_empty (Int64.Set.inter ns1 ns2)
    | Unboxed_int64 _, _ | _, Unboxed_int64 _ -> true
    | Unboxed_nativeint ns1, Unboxed_nativeint ns2 ->
      Nativeint.Set.is_empty (Nativeint.Set.inter ns1 ns2)
    | Unboxed_nativeint _, _ | _, Unboxed_nativeint _ -> true
    | Boxed_number (kind1, t1), Boxed_number (kind2, t2) ->
      (not (Boxed_number_kind.equal kind1 kind2))
        || definitely_different t1 t2
    | Boxed_number _, _ | _, Boxed_number _ -> true
    | Sets_of_closures _, Sets_of_closures _ -> false
    | Sets_of_closures _, _ | _, Sets_of_closures _ -> true
    | Closure _, Closure _ -> false
    | Closure _, _ | _, Closure _ -> true
    | Immutable_string s1, Immutable_string s2 -> String.compare s1 s2 <> 0
    | Immutable_string _, _ | _, Immutable_string _ -> true
    | Mutable_string _, Mutable_string _ -> false
    | Mutable_string _, _ | _, Mutable_string _ -> true
    | Float_array { contents = contents1; size = size1; },
      Float_array { contents = contents2; size = size2; } ->
      size1 <> size2
        || begin match contents1, contents2 with
           | Contents ts1, Contents ts2 ->
             Misc.Stdlib.Array.exists2 definitely_different ts1 ts2
           | Contents _, Unknown_or_mutable
           | Unknown_or_mutable, Contents _
           | Unknown_or_mutable, Unknown_or_mutable -> false
           end
  in
  match types with
  | [] | [_] | _ :: _ :: _ :: _ ->
    Misc.fatal_error "Wrong number of arguments for physical inequality"
  | [a1; a2] -> definitely_different a1 a2
*)

(*

let reify_as_unboxed_float_array (fa : float_array) : float list option =
  match fa.contents with
  | Unknown_or_mutable -> None
  | Contents contents ->
    Array.fold_right (fun elt acc ->
        match acc, descr elt with
        | Some acc, Unboxed_float fs ->
          begin match Float.Set.get_singleton fs with
          | None -> None
          | Some f -> Some (f :: acc)
          end
        | None, _
        | Some _, _ -> None)
      contents (Some [])

let reify_as_string t : string option =
  match descr t with
  | Immutable_string str -> Some str
  | Union _ | Boxed_number _ | Unboxed_float _ | Unboxed_int32 _
  | Unboxed_int64 _ | Unboxed_nativeint _ | Unknown _ | Mutable_string _
  | Float_array _ | Bottom | Sets_of_closures _ | Closure _
  | Load_lazily _ -> None
*)

type 'a or_wrong =
  | Ok of 'a
  | Wrong

module Or_not_all_values_known = struct
  type 'a t =
    | Exactly of 'a
    | Not_all_values_known

  let join join_contents t1 t2 : _ t or_wrong =
    match t1, t2 with
    | Exactly e1, Exactly e2 ->
      begin match join_contents e1 e2 with
      | Ok e -> Ok (Exactly e)
      | Wrong -> Wrong
      end
    | Exactly _, Not_all_values_known
    | Not_all_values_known, Exactly _
    | Not_all_values_known, Not_all_values_known -> Ok Not_all_values_known

  let meet meet_contents t1 t2 : _ t or_wrong =
    match t1, t2 with
    | Exactly e1, Exactly e2 ->
      begin match meet_contents e1 e2 with
      | Ok e -> Ok (Exactly e)
      | Wrong -> Wrong
      end
    | Exactly _, Not_all_values_known -> Ok t1
    | Not_all_values_known, Exactly _ -> Ok t2
    | Not_all_values_known, Not_all_values_known -> Ok Not_all_values_known

  let print f ppf t =
    match t with
    | Exactly thing -> f ppf thing
    | Not_all_values_known -> Format.pp_print_string ppf "Not_all_values_known"
end

type get_field_result =
  | Ok of t
  | Invalid

module Blocks : sig
  type t

  val empty : t

  val is_empty : t -> bool

  val create_singleton : Tag.Scannable.t -> ty_value array -> t

  val get_field
     : (t
    -> field_index:int
    -> expected_result_kind:K.t
    -> get_field_result) type_accessor

  val unique_tag_and_size : t -> (Tag.Scannable.t * int) option

  val join : (t -> t -> t or_wrong) type_accessor

  val meet : (t -> t -> t or_wrong) type_accessor

  val print : Format.formatter -> t -> unit
end = struct
  type t = ty_value array Tag.Scannable.Map.t

  let print ppf t =
    Tag.Scannable.Map.print print_ty_value_array ppf t

  let empty = Tag.Scannable.Map.empty

  let is_empty t = Tag.Scannable.Map.is_empty t

  let create_singleton tag fields =
    Tag.Scannable.Map.add tag fields Tag.Scannable.Map.empty

  let join ~importer ~type_of_name t1 t2 : t or_wrong =
    let exception Same_tag_different_arities in
    try
      let map =
        Tag.Scannable.Map.union (fun _tag fields1 fields2 ->
            if Array.length fields1 <> Array.length fields2 then
              raise Same_tag_different_arities
            else
              let fields =
                Array.map2 (fun ty_value1 ty_value2 ->
                    join_ty_value ~importer ~type_of_name ty_value1 ty_value2)
                  fields1 fields2
              in
              Some fields)
          t1 t2
      in
      Ok map
    with Same_tag_different_arities -> Wrong

  let meet ~importer ~type_of_name t1 t2 : t or_wrong =
    let exception Same_tag_different_arities in
    try
      let map =
        Tag.Scannable.Map.union (fun _tag fields1 fields2 ->
            if Array.length fields1 <> Array.length fields2 then
              raise Same_tag_different_arities
            else
              let fields =
                Array.map2 (fun ty_value1 ty_value2 ->
                    meet_ty_value ~importer ~type_of_name ty_value1 ty_value2)
                  fields1 fields2
              in
              Some fields)
          t1 t2
      in
      Ok map
    with Same_tag_different_arities -> Wrong

  let unique_tag_and_size t =
    match Tag.Scannable.Map.get_singleton t with
    | None -> None
    | Some (tag, fields) -> Some (tag, Array.length fields)

  let get_field ~importer ~type_of_name t ~field_index ~expected_result_kind
        : get_field_result =
    match Tag.Scannable.Map.get_singleton t with
    | None -> Invalid
    | Some (_tag, fields) ->
      if field_index < 0 || field_index >= Array.length fields then
        Invalid
      else
        let ty = fields.(field_index) in
        let scanning = scanning_ty_value ~importer ~type_of_name ty in
        let actual_kind = K.value scanning in
        if not (K.compatible actual_kind ~if_used_at:expected_result_kind)
        then begin
          Misc.fatal_errorf "Expected field %d of block with the following \
              type to have kind %a, but it has kind %a: %a"
            field_index
            K.print expected_result_kind
            K.print actual_kind
            print t
        end;
        Ok (t_of_ty_value ty)
end

module Evaluated_first_stage = struct
  (* We use a set-theoretic model that enables us to keep track of joins
     right until the end (unlike meets, joins cannot be "evaluated early":
     consider "({ 4 } join { 6 }) meet ({ 4 } join { 5 })").

     Having dealt with all of the meets without losing any information about
     joins, the "second stage" of evaluation (producing [Evaluated.t]) then
     flattens certain unions (in particular for closures etc). *)

  type t_values =
    | Unknown
    | Bottom
    | Blocks_and_tagged_immediates of
        (Blocks.t * Immediate.Set.t) Or_not_all_values_known.t
    | Boxed_floats of Float.Set.t Or_not_all_values_known.t
    | Boxed_int32s of Int32.Set.t Or_not_all_values_known.t
    | Boxed_int64s of Int64.Set.t Or_not_all_values_known.t
    | Boxed_nativeints of Targetint.Set.t Or_not_all_values_known.t
    | Closures of Closure.t list Or_not_all_values_known.t
    | Sets_of_closures of Set_of_closures.t list Or_not_all_values_known.t
    (* CR-someday mshinwell: Improve the [Float_array] case when we end up with
       immutable float arrays at the user level. *)
    | Strings of String_info.Set.t Or_not_all_values_known.t
    | Float_arrays of { lengths : Int.Set.t Or_not_all_values_known.t; }

  type t_naked_immediates = Immediate.Set.t Or_not_all_values_known.t
  type t_naked_floats = Float.Set.t Or_not_all_values_known.t
  type t_naked_int32s = Int32.Set.t Or_not_all_values_known.t
  type t_naked_int64s = Int64.Set.t Or_not_all_values_known.t
  type t_naked_nativeints = Targetint.Set.t Or_not_all_values_known.t

  type t =
    | Values of t_values
    | Naked_immediates of t_naked_immediates
    | Naked_floats of t_naked_floats
    | Naked_int32s of t_naked_int32s
    | Naked_int64s of t_naked_int64s
    | Naked_nativeints of t_naked_nativeints

  module Join_or_meet (P : sig
    val is_join : bool

    val combine_or_not_all_values_known
       : ('a -> 'a -> 'a or_wrong)
      -> 'a Or_not_all_values_known.t
      -> 'a Or_not_all_values_known.t
      -> 'a Or_not_all_values_known.t or_wrong

    val combine_blocks
       : (Blocks.t
      -> Blocks.t
      -> Blocks.t or_wrong) type_accessor

    val combine_int_sets
       : Int.Set.t
      -> Int.Set.t
      -> Int.Set.t

    val combine_immediate_sets
       : Immediate.Set.t
      -> Immediate.Set.t
      -> Immediate.Set.t

    val combine_float_sets
       : Float.Set.t
      -> Float.Set.t
      -> Float.Set.t

    val combine_int32_sets
       : Int32.Set.t
      -> Int32.Set.t
      -> Int32.Set.t

    val combine_int64_sets
       : Int64.Set.t
      -> Int64.Set.t
      -> Int64.Set.t

    val combine_targetint_sets
       : Targetint.Set.t
      -> Targetint.Set.t
      -> Targetint.Set.t

    val combine_string_info_sets
       : String_info.Set.t
      -> String_info.Set.t
      -> String_info.Set.t
  end) = struct
    let absorbing_element_for_values : t_values =
      if P.is_join then Unknown else Bottom

    let combine_values ~importer ~type_of_name
          (t1 : t_values) (t2 : t_values) : t_values =
      match t1, t2 with
      | Unknown, _ -> if P.is_join then Unknown else t2
      | _, Unknown -> if P.is_join then Unknown else t1
      | Bottom, _ -> if P.is_join then t2 else Bottom
      | _, Bottom -> if P.is_join then t1 else Bottom
      | Blocks_and_tagged_immediates variant1,
          Blocks_and_tagged_immediates variant2 ->
        begin match
          P.combine_or_not_all_values_known
            (fun (b1, imms1) (b2, imms2) : _ or_wrong ->
              let blocks = P.combine_blocks ~importer ~type_of_name b1 b2 in
              match blocks with
              | Ok blocks ->
                let imms = P.combine_immediate_sets imms1 imms2 in
                Ok (blocks, imms)
              | Wrong -> Wrong)
            variant1 variant2
        with
        | Ok (Exactly (blocks, imms)) ->
          Blocks_and_tagged_immediates (Exactly (blocks, imms))
        | Ok Not_all_values_known ->
          Blocks_and_tagged_immediates Not_all_values_known
        | Wrong ->
          (* Two tags with mismatching arities: irrespective of the
             immediates and whether we are doing a meet or join, this is
             bottom. *)
          Bottom
        end
      | Boxed_floats fs1, Boxed_floats fs2 ->
        (* CR mshinwell: add new meet and join functions in
           [Or_not_all_values_known] to remove these "assert false"s *)
        begin match
          P.combine_or_not_all_values_known
            (fun fs1 fs2 : Float.Set.t or_wrong ->
              Ok (P.combine_float_sets fs1 fs2))
            fs1 fs2
        with
        | Ok fs -> Boxed_floats fs
        | Wrong -> assert false
        end
      | Boxed_int32s is1, Boxed_int32s is2 ->
        begin match
          P.combine_or_not_all_values_known
            (fun is1 is2 : Int32.Set.t or_wrong ->
              Ok (P.combine_int32_sets is1 is2))
            is1 is2
        with
        | Ok is -> Boxed_int32s is
        | Wrong -> assert false
        end
      | Boxed_int64s is1, Boxed_int64s is2 ->
        begin match
          P.combine_or_not_all_values_known
            (fun is1 is2 : Int64.Set.t or_wrong ->
              Ok (P.combine_int64_sets is1 is2))
            is1 is2
        with
        | Ok is -> Boxed_int64s is
        | Wrong -> assert false
        end
      | Boxed_nativeints is1, Boxed_nativeints is2 ->
        begin match
          P.combine_or_not_all_values_known
            (fun is1 is2 : Targetint.Set.t or_wrong ->
              Ok (P.combine_targetint_sets is1 is2))
            is1 is2
        with
        | Ok is -> Boxed_nativeints is
        | Wrong -> assert false
        end
      | Closures closures1, Closures closures2 ->
        let closures =
          P.combine_or_not_all_values_known
            (fun closures1 closures2 : _ or_wrong ->
              Ok (closures1 @ closures2))
            closures1 closures2
        in
        begin match closures with
        | Ok (Exactly closures) -> Closures (Exactly closures)
        | Ok Not_all_values_known -> Closures Not_all_values_known
        | Wrong -> assert false
        end
      | Sets_of_closures set1, Sets_of_closures set2 ->
        let sets_of_closures =
          P.combine_or_not_all_values_known
            (fun sets_of_closures1 sets_of_closures2 : _ or_wrong ->
              Ok (sets_of_closures1 @ sets_of_closures2))
            set1 set2
        in
        begin match sets_of_closures with
        | Ok (Exactly sets_of_closures) ->
          Sets_of_closures (Exactly sets_of_closures)
        | Ok Not_all_values_known ->
          Sets_of_closures Not_all_values_known
        | Wrong -> assert false
        end
      | Strings strings1, Strings strings2 ->
        let strings =
          P.combine_or_not_all_values_known
            (fun strings1 strings2 : _ or_wrong ->
              Ok (P.combine_string_info_sets strings1 strings2))
            strings1 strings2
        in
        begin match strings with
        | Ok (Exactly strings) -> Strings (Exactly strings)
        | Ok Not_all_values_known -> Strings Not_all_values_known
        | Wrong -> assert false
        end
      | Float_arrays { lengths = lengths1; },
          Float_arrays { lengths = lengths2; } ->
        let lengths =
          P.combine_or_not_all_values_known
            (fun lengths1 lengths2 : _ or_wrong ->
              Ok (P.combine_int_sets lengths1 lengths2))
            lengths1 lengths2
        in
        begin match lengths with
        | Ok (Exactly lengths) ->
          Float_arrays { lengths = Exactly lengths; }
        | Ok Not_all_values_known ->
          Float_arrays { lengths = Not_all_values_known; }
        | Wrong -> assert false
        end
      | (Blocks_and_tagged_immediates _
        | Boxed_floats _
        | Boxed_int32s _
        | Boxed_int64s _
        | Boxed_nativeints _
        | Closures _
        | Sets_of_closures _
        | Strings _
        | Float_arrays { lengths = _; }), _ ->
          absorbing_element_for_values

    let combine_naked_immediates ~importer:_ ~type_of_name:_
          (t1 : t_naked_immediates) (t2 : t_naked_immediates)
          : t_naked_immediates =
      begin match
        P.combine_or_not_all_values_known (fun is1 is2 : _ or_wrong ->
            Ok (P.combine_immediate_sets is1 is2))
          t1 t2
      with
      | Ok is -> is
      | Wrong -> assert false
      end

    let combine_naked_floats ~importer:_ ~type_of_name:_
          (t1 : t_naked_floats) (t2 : t_naked_floats)
          : t_naked_floats =
      begin match
        P.combine_or_not_all_values_known (fun fs1 fs2 : _ or_wrong ->
            Ok (P.combine_float_sets fs1 fs2))
          t1 t2
      with
      | Ok fs -> fs
      | Wrong -> assert false
      end

    let combine_naked_int32s ~importer:_ ~type_of_name:_
          (t1 : t_naked_int32s) (t2 : t_naked_int32s)
          : t_naked_int32s =
      begin match
        P.combine_or_not_all_values_known (fun is1 is2 : _ or_wrong ->
            Ok (P.combine_int32_sets is1 is2))
          t1 t2
      with
      | Ok is -> is
      | Wrong -> assert false
      end

    let combine_naked_int64s ~importer:_ ~type_of_name:_
          (t1 : t_naked_int64s) (t2 : t_naked_int64s)
          : t_naked_int64s =
      begin match
        P.combine_or_not_all_values_known (fun is1 is2 : _ or_wrong ->
            Ok (P.combine_int64_sets is1 is2))
          t1 t2
      with
      | Ok is -> is
      | Wrong -> assert false
      end

    let combine_naked_nativeints ~importer:_ ~type_of_name:_
          (t1 : t_naked_nativeints) (t2 : t_naked_nativeints)
          : t_naked_nativeints =
      begin match
        P.combine_or_not_all_values_known (fun is1 is2 : _ or_wrong ->
            Ok (P.combine_targetint_sets is1 is2))
          t1 t2
      with
      | Ok is -> is
      | Wrong -> assert false
      end
  end

  module Join = Join_or_meet (struct
    let is_join = true

    let combine_or_not_all_values_known = Or_not_all_values_known.join
    let combine_blocks = Blocks.join
    let combine_int_sets = Int.Set.union
    let combine_immediate_sets = Immediate.Set.union
    let combine_float_sets = Float.Set.union
    let combine_int32_sets = Int32.Set.union
    let combine_int64_sets = Int64.Set.union
    let combine_targetint_sets = Targetint.Set.union
    let combine_string_info_sets = String_info.Set.union
  end)

  module Meet = Join_or_meet (struct
    let is_join = false

    let combine_or_not_all_values_known = Or_not_all_values_known.meet
    let combine_blocks = Blocks.meet
    let combine_int_sets = Int.Set.inter
    let combine_immediate_sets = Immediate.Set.inter
    let combine_float_sets = Float.Set.inter
    let combine_int32_sets = Int32.Set.inter
    let combine_int64_sets = Int64.Set.inter
    let combine_targetint_sets = Targetint.Set.inter
    let combine_string_info_sets = String_info.Set.inter
  end)

  let evaluate_ty (type singleton) (type result) ~importer
        ~importer_this_kind ~type_of_name ~force_to_kind ~unknown_payload
        ~(join : (result -> result -> result) type_accessor)
        ~(meet : (result -> result -> result) type_accessor)
        ~(eval_singleton : singleton -> result)
        ~(unknown : result) ~(bottom : result)
        (ty : (singleton, _) ty) : result * (Name.t option) =
    let rec evaluate (ty : (singleton, _) ty) : result * (Name.t option) =
      let resolved_ty, canonical_name =
        resolve_aliases_and_squash_unresolved_names_on_ty ~importer_this_kind
          ~force_to_kind ~type_of_name ~unknown_payload ty
      in
      match resolved_ty with
      | Unknown _ -> unknown, canonical_name
      | Bottom -> bottom, canonical_name
      | Ok or_combination ->
        begin match or_combination with
        | Singleton singleton ->
          eval_singleton singleton, canonical_name
        | Combination (op, ty1, ty2) ->
          let ty1 : (singleton, _) ty = combination_component_to_ty ty1 in
          let ty2 : (singleton, _) ty = combination_component_to_ty ty2 in
          let eval1, canonical_name1 = evaluate ty1 in
          let eval2, canonical_name2 = evaluate ty2 in
          let eval =
            match op with
            | Union -> join ~importer ~type_of_name eval1 eval2
            | Intersection -> meet ~importer ~type_of_name eval1 eval2
          in
          let canonical_name =
            match canonical_name1, canonical_name2 with
            | Some name1, Some name2 when Name.equal name1 name2 ->
              canonical_name1
            | _, _ -> None
          in
          eval, canonical_name
        end
    in
    evaluate ty

  let rec evaluate_ty_value ~importer ~type_of_name (ty : ty_value)
        : t_values * Name.t option =
    let module I = (val importer : Importer) in
    let eval_singleton (singleton : of_kind_value) : t_values =
      match singleton with
      | Tagged_immediate ty ->
        let t_naked_immediates, _canonical_name =
          evaluate_ty_naked_immediate ~importer ~type_of_name ty
        in
        begin match t_naked_immediates with
        | Exactly imms ->
          Blocks_and_tagged_immediates (Exactly (Blocks.empty, imms))
        | Not_all_values_known ->
          Blocks_and_tagged_immediates Not_all_values_known
        end
      | Boxed_float ty ->
        let t_naked_floats, _canonical_name =
          evaluate_ty_naked_float ~importer ~type_of_name ty
        in
        Boxed_floats t_naked_floats
      | Boxed_int32 ty ->
        let t_naked_int32s, _canonical_name =
          evaluate_ty_naked_int32 ~importer ~type_of_name ty
        in
        Boxed_int32s t_naked_int32s
      | Boxed_int64 ty ->
        let t_naked_int64s, _canonical_name =
          evaluate_ty_naked_int64 ~importer ~type_of_name ty
        in
        Boxed_int64s t_naked_int64s
      | Boxed_nativeint ty ->
        let t_naked_nativeints, _canonical_name =
          evaluate_ty_naked_nativeint ~importer ~type_of_name ty
        in
        Boxed_nativeints t_naked_nativeints
      | Block (tag, fields) ->
        let blocks = Blocks.create_singleton tag fields in
        Blocks_and_tagged_immediates (Exactly (blocks, Immediate.Set.empty))
      | Closure closure -> Closures (Exactly [closure])
      | Set_of_closures set -> Sets_of_closures (Exactly [set])
      | String str -> Strings (Exactly (String_info.Set.singleton str))
      | Float_array fields ->
        let length = Array.length fields in
        Float_arrays { lengths = Exactly (Int.Set.singleton length); }
    in
    evaluate_ty ~importer
      ~importer_this_kind:
        I.import_value_type_as_resolved_ty_value
      ~type_of_name
      ~force_to_kind:force_to_kind_value
      ~unknown_payload:K.Must_scan
      ~join:Join.combine_values
      ~meet:Meet.combine_values
      ~eval_singleton
      ~unknown:Unknown
      ~bottom:Bottom
      ty

  and evaluate_ty_naked_immediate ~importer ~type_of_name
        (ty : ty_naked_immediate) : t_naked_immediates * Name.t option =
    let module I = (val importer : Importer) in
    let eval_singleton (singleton : of_kind_naked_immediate)
          : t_naked_immediates =
      match singleton with
      | Naked_immediate imm -> Exactly (Immediate.Set.singleton imm)
    in
    evaluate_ty ~importer
      ~importer_this_kind:
        I.import_naked_immediate_type_as_resolved_ty_naked_immediate
      ~type_of_name
      ~force_to_kind:force_to_kind_naked_immediate
      ~unknown_payload:()
      ~join:Join.combine_naked_immediates
      ~meet:Meet.combine_naked_immediates
      ~eval_singleton
      ~unknown:(Not_all_values_known : t_naked_immediates)
      ~bottom:((Exactly Immediate.Set.empty) : t_naked_immediates)
      ty

  and evaluate_ty_naked_float ~importer ~type_of_name
        (ty : ty_naked_float) : t_naked_floats * Name.t option =
    let module I = (val importer : Importer) in
    let eval_singleton (singleton : of_kind_naked_float)
          : t_naked_floats =
      match singleton with
      | Naked_float imm -> Exactly (Float.Set.singleton imm)
    in
    evaluate_ty ~importer
      ~importer_this_kind:
        I.import_naked_float_type_as_resolved_ty_naked_float
      ~type_of_name
      ~force_to_kind:force_to_kind_naked_float
      ~unknown_payload:()
      ~join:Join.combine_naked_floats
      ~meet:Meet.combine_naked_floats
      ~eval_singleton
      ~unknown:(Not_all_values_known : t_naked_floats)
      ~bottom:((Exactly Float.Set.empty) : t_naked_floats)
      ty

  and evaluate_ty_naked_int32 ~importer ~type_of_name
        (ty : ty_naked_int32) : t_naked_int32s * Name.t option =
    let module I = (val importer : Importer) in
    let eval_singleton (singleton : of_kind_naked_int32)
          : t_naked_int32s =
      match singleton with
      | Naked_int32 imm -> Exactly (Int32.Set.singleton imm)
    in
    evaluate_ty ~importer
      ~importer_this_kind:
        I.import_naked_int32_type_as_resolved_ty_naked_int32
      ~type_of_name
      ~force_to_kind:force_to_kind_naked_int32
      ~unknown_payload:()
      ~join:Join.combine_naked_int32s
      ~meet:Meet.combine_naked_int32s
      ~eval_singleton
      ~unknown:(Not_all_values_known : t_naked_int32s)
      ~bottom:((Exactly Int32.Set.empty) : t_naked_int32s)
      ty

  and evaluate_ty_naked_int64 ~importer ~type_of_name
        (ty : ty_naked_int64) : t_naked_int64s * Name.t option =
    let module I = (val importer : Importer) in
    let eval_singleton (singleton : of_kind_naked_int64)
          : t_naked_int64s =
      match singleton with
      | Naked_int64 imm -> Exactly (Int64.Set.singleton imm)
    in
    evaluate_ty ~importer
      ~importer_this_kind:
        I.import_naked_int64_type_as_resolved_ty_naked_int64
      ~type_of_name
      ~force_to_kind:force_to_kind_naked_int64
      ~unknown_payload:()
      ~join:Join.combine_naked_int64s
      ~meet:Meet.combine_naked_int64s
      ~eval_singleton
      ~unknown:(Not_all_values_known : t_naked_int64s)
      ~bottom:((Exactly Int64.Set.empty) : t_naked_int64s)
      ty

  and evaluate_ty_naked_nativeint ~importer ~type_of_name
        (ty : ty_naked_nativeint) : t_naked_nativeints * Name.t option =
    let module I = (val importer : Importer) in
    let eval_singleton (singleton : of_kind_naked_nativeint)
          : t_naked_nativeints =
      match singleton with
      | Naked_nativeint imm -> Exactly (Targetint.Set.singleton imm)
    in
    evaluate_ty ~importer
      ~importer_this_kind:
        I.import_naked_nativeint_type_as_resolved_ty_naked_nativeint
      ~type_of_name
      ~force_to_kind:force_to_kind_naked_nativeint
      ~unknown_payload:()
      ~join:Join.combine_naked_nativeints
      ~meet:Meet.combine_naked_nativeints
      ~eval_singleton
      ~unknown:(Not_all_values_known : t_naked_nativeints)
      ~bottom:((Exactly Targetint.Set.empty) : t_naked_nativeints)
      ty

  let create ~importer ~type_of_name (t : flambda_type)
        : t * (Name.t option) =
    match t with
    | Value ty ->
      let ty, canonical_name =
        evaluate_ty_value ~importer ~type_of_name ty
      in
      Values ty, canonical_name
    | Naked_immediate ty ->
      let ty, canonical_name =
        evaluate_ty_naked_immediate ~importer ~type_of_name ty
      in
      Naked_immediates ty, canonical_name
    | Naked_float ty ->
      let ty, canonical_name =
        evaluate_ty_naked_float ~importer ~type_of_name ty
      in
      Naked_floats ty, canonical_name
    | Naked_int32 ty ->
      let ty, canonical_name =
        evaluate_ty_naked_int32 ~importer ~type_of_name ty
      in
      Naked_int32s ty, canonical_name
    | Naked_int64 ty ->
      let ty, canonical_name =
        evaluate_ty_naked_int64 ~importer ~type_of_name ty
      in
      Naked_int64s ty, canonical_name
    | Naked_nativeint ty ->
      let ty, canonical_name =
        evaluate_ty_naked_nativeint ~importer ~type_of_name ty
      in
      Naked_nativeints ty, canonical_name
end

module Joined_closures : sig
  type t

  val create : (Closure.t list -> t) type_accessor

  val is_bottom : t -> bool

  val sets_of_closures : t -> ty_value Closure_id.Map.t

  val print : Format.formatter -> t -> unit

  val to_type : t -> flambda_type
end = struct
  type t = {
    sets_of_closures : ty_value Closure_id.Map.t;
  }

  let print ppf t =
    Format.fprintf ppf "@[(sets_of_closures@ %a)@]"
      (Closure_id.Map.print print_ty_value) t.sets_of_closures

  let sets_of_closures t = t.sets_of_closures

  let is_bottom t = Closure_id.Map.is_empty t.sets_of_closures

  let of_closure (closure : Closure.t) : t =
    let sets_of_closures =
      Closure_id.Map.add closure.closure_id closure.set_of_closures
        Closure_id.Map.empty
    in
    { sets_of_closures;
    }

  let join ~importer ~type_of_name t1 t2 =
    let sets_of_closures =
      Closure_id.Map.union (fun _closure_id ty_value1 ty_value2 ->
          Some (join_ty_value ~importer ~type_of_name ty_value1 ty_value2))
        t1.sets_of_closures
        t2.sets_of_closures
    in
    { sets_of_closures;
    }

  let create ~importer ~type_of_name (closures : Closure.t list) =
    let sets = List.map of_closure closures in
    match sets with
    | [] ->
      { sets_of_closures = Closure_id.Map.empty;
      }
    | set::sets ->
      List.fold_left (fun result t ->
          join ~importer ~type_of_name result t)
        set sets

  let to_type _t =
    assert false
end

module Joined_sets_of_closures : sig
  type t
  val create : (Set_of_closures.t list -> t) type_accessor
  val function_decls : t -> function_declaration Closure_id.Map.t
  val closure_elements : t -> ty_value Var_within_closure.Map.t
  val type_for_closure_id : t -> Closure_id.t -> flambda_type
  val to_type : t -> flambda_type
  val print : Format.formatter -> t -> unit
end = struct
  type t = {
    set_of_closures_id_and_origin :
      (Set_of_closures_id.t * Set_of_closures_origin.t)
        Or_not_all_values_known.t;
    function_decls : function_declaration Closure_id.Map.t;
    closure_elements : ty_value Var_within_closure.Map.t;
  }

  let function_decls t = t.function_decls
  let closure_elements t = t.closure_elements

  let print ppf t =
    Format.fprintf ppf "@[((function_decls %a)@ (closure_elements %a))@]"
      Closure_id.Set.print
      (Closure_id.Map.keys t.function_decls)
      Var_within_closure.Set.print
      (Var_within_closure.Map.keys t.closure_elements)

  let of_set_of_closures (set : Set_of_closures.t) : t =
    { set_of_closures_id_and_origin =
        Exactly (set.set_of_closures_id, set.set_of_closures_origin);
      function_decls = set.function_decls;
      closure_elements = set.closure_elements;
    }

  let type_for_closure_id _t _closure_id =
    (* CR mshinwell for pchambart: ... *)
    assert false

  let to_type t =
    match t.set_of_closures_id_and_origin with
    | Not_all_values_known -> any_value Must_scan Other
    | Exactly (set_of_closures_id, set_of_closures_origin) ->
      set_of_closures ~set_of_closures_id
        ~set_of_closures_origin
        ~function_decls:t.function_decls
        ~closure_elements:t.closure_elements

  let make_non_inlinable_function_declaration (f : function_declaration)
        : function_declaration =
    match f with
    | Inlinable decl ->
      let decl =
        create_non_inlinable_function_declaration ~result:decl.result
          ~direct_call_surrogate:decl.direct_call_surrogate
      in
      Non_inlinable decl
    | Non_inlinable _ -> f

  let join_and_make_all_functions_non_inlinable ~importer ~type_of_name
        (t1 : t) (t2 : t) : t =
    let join_results_and_make_non_inlinable (f1 : function_declaration)
          (f2 : function_declaration) : function_declaration =
      let f1_result =
        match f1 with
        | Inlinable f1 -> f1.result
        | Non_inlinable f1 -> f1.result
      in
      let f2_result =
        match f2 with
        | Inlinable f2 -> f2.result
        | Non_inlinable f2 -> f2.result
      in
      if List.length f1_result <> List.length f2_result then begin
        Misc.fatal_errorf "Function appears with two different return arities: \
            %a and %a"
          print t1
          print t2
      end;
      let result =
        List.map2 (join ~importer ~type_of_name) f1_result f2_result
      in
      let decl =
        create_non_inlinable_function_declaration ~result
          ~direct_call_surrogate:None
      in
      Non_inlinable decl
    in
    let function_decls =
      Closure_id.Map.union_both
        (fun f -> make_non_inlinable_function_declaration f)
        (fun f1 f2 -> join_results_and_make_non_inlinable f1 f2)
        t1.function_decls t2.function_decls
    in
    let closure_elements =
      Var_within_closure.Map.union_both
        (fun ty ->
          let scanning = scanning_ty_value ~importer ~type_of_name ty in
          any_value_as_ty_value scanning Other)
        (fun ty1 ty2 -> join_ty_value ~importer ~type_of_name ty1 ty2)
        t1.closure_elements t2.closure_elements
    in
    { set_of_closures_id_and_origin = Not_all_values_known;
      function_decls;
      closure_elements;
    }

  let join ~importer ~type_of_name (t1 : t) (t2 : t) : t =
    let set_of_closures_id_and_origin =
      Or_not_all_values_known.join (fun (id1, origin1) (id2, origin2) ->
          if Set_of_closures_id.equal id1 id2 then begin
            (* CR mshinwell: We should think more about [Set_of_closures_id]
               particularly in the context of recursive cases vs. the previous
               version of a set of closures *)
            assert (Set_of_closures_origin.equal origin1 origin2);
            Ok (id1, origin1)
          end else begin
            Wrong
          end)
        t1.set_of_closures_id_and_origin
        t2.set_of_closures_id_and_origin
    in
    match set_of_closures_id_and_origin with
    | Ok ((Exactly _) as set_of_closures_id_and_origin) ->
      (* If the [set_of_closures_id]s are the same, the result is eligible for
         inlining, when the input function declarations are.

         The real constraint is that the union of two functions is inlinable
         if either of the two functions can be replaced by the other.  As such
         our behaviour here is conservative but hopefully not too restrictive in
         practice. *)
      (* CR pchambart: this is too strong, but should hold in general.
         It can be kept for now to help debugging *)
      assert (t1.function_decls == t2.function_decls);
      let closure_elements =
        Var_within_closure.Map.union_merge
          (join_ty_value ~importer ~type_of_name)
          t1.closure_elements t2.closure_elements
      in
      { set_of_closures_id_and_origin;
        function_decls = t1.function_decls;
        closure_elements;
      }
    | Ok Not_all_values_known | Wrong ->
      join_and_make_all_functions_non_inlinable ~importer ~type_of_name t1 t2

  let create ~importer ~type_of_name (sets : Set_of_closures.t list)
        : t =
    let sets = List.map of_set_of_closures sets in
    match sets with
    | [] ->
      { (* CR mshinwell: This is a bit strange: should there be a proper
           constructor for "bottom" here? *)
        set_of_closures_id_and_origin = Not_all_values_known;
        function_decls = Closure_id.Map.empty;
        closure_elements = Var_within_closure.Map.empty;
      }
    | set::sets ->
      List.fold_left (fun result t ->
          join ~importer ~type_of_name result t)
        set sets
end

module Evaluated = struct
  type t_values =
    | Unknown
    | Bottom
    | Blocks_and_tagged_immediates of
        (Blocks.t * Immediate.Set.t) Or_not_all_values_known.t
    | Tagged_immediates_only of Immediate.Set.t Or_not_all_values_known.t
    | Boxed_floats of Float.Set.t Or_not_all_values_known.t
    | Boxed_int32s of Int32.Set.t Or_not_all_values_known.t
    | Boxed_int64s of Int64.Set.t Or_not_all_values_known.t
    | Boxed_nativeints of Targetint.Set.t Or_not_all_values_known.t
    | Closures of Joined_closures.t Or_not_all_values_known.t
    | Sets_of_closures of Joined_sets_of_closures.t Or_not_all_values_known.t
    | Strings of String_info.Set.t Or_not_all_values_known.t
    | Float_arrays of { lengths : Int.Set.t Or_not_all_values_known.t; }

  type t =
    | Values of t_values
    | Naked_immediates of Immediate.Set.t Or_not_all_values_known.t
    | Naked_floats of Float.Set.t Or_not_all_values_known.t
    | Naked_int32s of Int32.Set.t Or_not_all_values_known.t
    | Naked_int64s of Int64.Set.t Or_not_all_values_known.t
    | Naked_nativeints of Targetint.Set.t Or_not_all_values_known.t

  let print_blocks_and_immediates ppf (blocks, imms) =
    Format.fprintf ppf "@[((blocks@ %a)@ (immediates@ %a))@]"
      Blocks.print blocks
      Immediate.Set.print imms

  let print_t_values ppf (t_values : t_values) =
    match t_values with
    | Unknown -> Format.pp_print_string ppf "Unknown"
    | Bottom -> Format.pp_print_string ppf "Bottom"
    | Blocks_and_tagged_immediates variant ->
      Format.fprintf ppf "@[(Blocks_and_tagged_immediates@ %a)@]"
        (Or_not_all_values_known.print print_blocks_and_immediates) variant
    | Tagged_immediates_only imms ->
      Format.fprintf ppf "@[(Tagged_immediates_only@ %a)@]"
        (Or_not_all_values_known.print Immediate.Set.print) imms
    | Boxed_floats fs ->
      Format.fprintf ppf "@[(Boxed_floats@ %a)@]"
        (Or_not_all_values_known.print Float.Set.print) fs
    | Boxed_int32s is ->
      Format.fprintf ppf "@[(Boxed_int32s@ %a)@]"
        (Or_not_all_values_known.print Int32.Set.print) is
    | Boxed_int64s is ->
      Format.fprintf ppf "@[(Boxed_int64s@ %a)@]"
        (Or_not_all_values_known.print Int64.Set.print) is
    | Boxed_nativeints is ->
      Format.fprintf ppf "@[(Boxed_nativeints@ %a)@]"
        (Or_not_all_values_known.print Targetint.Set.print) is
    | Closures closures ->
      Format.fprintf ppf "@[(Closures@ %a)@]"
        (Or_not_all_values_known.print Joined_closures.print) closures
    | Sets_of_closures sets ->
      Format.fprintf ppf "@[(Sets_of_closures@ %a)@]"
        (Or_not_all_values_known.print Joined_sets_of_closures.print) sets
    | Strings strs ->
      Format.fprintf ppf "@[(Strings@ %a)@]"
        (Or_not_all_values_known.print String_info.Set.print) strs
    | Float_arrays { lengths; } ->
      Format.fprintf ppf "@[(Float_arrays@ %a)@]"
        (Or_not_all_values_known.print Int.Set.print) lengths

  let print ppf (t : t) =
    match t with
    | Values t_values ->
      Format.fprintf ppf "@[(Values@ (%a))@]" print_t_values t_values
    | Naked_immediates imms ->
      Format.fprintf ppf "@[(Naked_immediates@ (%a))@]"
        (Or_not_all_values_known.print Immediate.Set.print)
        imms
    | Naked_floats fs ->
      Format.fprintf ppf "@[(Naked_floats@ (%a))@]"
        (Or_not_all_values_known.print Float.Set.print)
        fs
    | Naked_int32s is ->
      Format.fprintf ppf "@[(Naked_int32s@ (%a))@]"
        (Or_not_all_values_known.print Int32.Set.print)
        is
    | Naked_int64s is ->
      Format.fprintf ppf "@[(Naked_int64s@ (%a))@]"
        (Or_not_all_values_known.print Int64.Set.print)
        is
    | Naked_nativeints is ->
      Format.fprintf ppf "@[(Naked_nativeints@ (%a))@]"
        (Or_not_all_values_known.print Targetint.Set.print)
        is

  let invariant t =
    if !Clflags.flambda_invariant_checks then begin
      match t with
      | Values values ->
        begin match values with
        | Blocks_and_tagged_immediates (Exactly (blocks, _imms)) ->
          if Blocks.is_empty blocks then begin
            Misc.fatal_error "Use [Tagged_immediates_only] instead of \
              [Blocks_and_tagged_immediates] when there are no blocks: %a"
          end
        | Unknown
        | Bottom
        | Blocks_and_tagged_immediates Not_all_values_known
        | Tagged_immediates_only _
        | Boxed_floats _
        | Boxed_int32s _
        | Boxed_int64s _
        | Boxed_nativeints _
        | Closures _
        | Sets_of_closures _
        | Strings _
        | Float_arrays _ -> ()
        end
      | Naked_immediates _
      | Naked_floats _
      | Naked_int32s _
      | Naked_int64s _
      | Naked_nativeints _ -> ()
    end

  let kind (t : t) =
    match t with
    | Values values ->
      begin match values with
      | Bottom
      | Tagged_immediates_only _ -> K.value Can_scan
      | Unknown
      | Blocks_and_tagged_immediates _
      | Boxed_floats _
      | Boxed_int32s _
      | Boxed_int64s _
      | Boxed_nativeints _
      | Closures _
      | Sets_of_closures _
      | Strings _
      | Float_arrays _ ->
        (* CR mshinwell: For something like a statically-allocated set of
           closures we may not need to scan it, and maybe in some cases it
           might only be marked [Can_scan].  Are we at risk of this lub
           check failing in that case? *)
        K.value Must_scan
      end
    | Naked_immediates _ -> K.naked_immediate ()
    | Naked_floats _ -> K.naked_float ()
    | Naked_int32s _ -> K.naked_int32 ()
    | Naked_int64s _ -> K.naked_int64 ()
    | Naked_nativeints _ -> K.naked_nativeint ()

  let is_unknown (t : t) =
    match t with
    | Values values ->
      begin match values with
      | Unknown
      | Blocks_and_tagged_immediates Not_all_values_known
      | Tagged_immediates_only Not_all_values_known
      | Boxed_floats Not_all_values_known
      | Boxed_int32s Not_all_values_known
      | Boxed_int64s Not_all_values_known
      | Boxed_nativeints Not_all_values_known
      | Closures Not_all_values_known
      | Sets_of_closures Not_all_values_known
      | Strings Not_all_values_known
      | Float_arrays { lengths = Not_all_values_known; } -> true
      | Bottom
      | Blocks_and_tagged_immediates (Exactly _)
      | Tagged_immediates_only (Exactly _)
      | Boxed_floats (Exactly _)
      | Boxed_int32s (Exactly _)
      | Boxed_int64s (Exactly _)
      | Boxed_nativeints (Exactly _)
      | Closures (Exactly _)
      | Sets_of_closures (Exactly _)
      | Strings (Exactly _)
      | Float_arrays { lengths = Exactly _; } -> false
      end
    | Naked_immediates Not_all_values_known
    | Naked_floats Not_all_values_known
    | Naked_int32s Not_all_values_known
    | Naked_int64s Not_all_values_known
    | Naked_nativeints Not_all_values_known -> true
    | Naked_immediates (Exactly _)
    | Naked_floats (Exactly _)
    | Naked_int32s (Exactly _)
    | Naked_int64s (Exactly _)
    | Naked_nativeints (Exactly _) -> false

  let is_known t = not (is_unknown t)

  let is_bottom (t : t) =
    match t with
    | Values values ->
      begin match values with
      | Bottom -> true
      | Blocks_and_tagged_immediates (Exactly (blocks, imms)) ->
        assert (not (Blocks.is_empty blocks));  (* cf. [invariant]. *)
        Immediate.Set.is_empty imms
      | Tagged_immediates_only (Exactly imms) -> Immediate.Set.is_empty imms
      | Boxed_floats (Exactly fs) -> Float.Set.is_empty fs
      | Boxed_int32s (Exactly is) -> Int32.Set.is_empty is
      | Boxed_int64s (Exactly is) -> Int64.Set.is_empty is
      | Boxed_nativeints (Exactly is) -> Targetint.Set.is_empty is
      | Closures (Exactly closures) -> Joined_closures.is_bottom closures
      | Strings (Exactly strs) -> String_info.Set.is_empty strs
      | Float_arrays { lengths = Exactly lengths; } -> Int.Set.is_empty lengths
      | Unknown
      | Blocks_and_tagged_immediates Not_all_values_known
      | Tagged_immediates_only Not_all_values_known
      | Boxed_floats Not_all_values_known
      | Boxed_int32s Not_all_values_known
      | Boxed_int64s Not_all_values_known
      | Boxed_nativeints Not_all_values_known
      | Closures Not_all_values_known
      | Sets_of_closures _
      | Strings Not_all_values_known
      | Float_arrays { lengths = Not_all_values_known; } -> false
      end
    | Naked_immediates (Exactly is) -> Immediate.Set.is_empty is
    | Naked_floats (Exactly fs) -> Float.Set.is_empty fs
    | Naked_int32s (Exactly is) -> Int32.Set.is_empty is
    | Naked_int64s (Exactly is) -> Int64.Set.is_empty is
    | Naked_nativeints (Exactly is) -> Targetint.Set.is_empty is
    | Naked_immediates Not_all_values_known
    | Naked_floats Not_all_values_known
    | Naked_int32s Not_all_values_known
    | Naked_int64s Not_all_values_known
    | Naked_nativeints Not_all_values_known -> false

  let is_non_bottom t = not (is_bottom t)

  let is_useful t = is_known t && is_non_bottom t

  let of_evaluated_first_stage ~importer ~type_of_name
        (evaluated_first_stage : Evaluated_first_stage.t) : t =
    let t : t =
      match evaluated_first_stage with
      | Values values ->
        let values : t_values =
          match values with
          | Unknown -> Unknown
          | Bottom -> Bottom
          | Blocks_and_tagged_immediates Not_all_values_known ->
            Blocks_and_tagged_immediates Not_all_values_known
          | Blocks_and_tagged_immediates (Exactly (blocks, imms)) ->
            if Blocks.is_empty blocks then
              Tagged_immediates_only (Exactly imms)
            else
              Blocks_and_tagged_immediates (Exactly (blocks, imms))
          | Boxed_floats fs -> Boxed_floats fs
          | Boxed_int32s is -> Boxed_int32s is
          | Boxed_int64s is -> Boxed_int64s is
          | Boxed_nativeints is -> Boxed_nativeints is
          | Closures Not_all_values_known -> Closures Not_all_values_known
          | Closures (Exactly closures) ->
            let joined =
              Joined_closures.create ~importer ~type_of_name closures
            in
            Closures (Exactly joined)
          | Sets_of_closures Not_all_values_known ->
            Sets_of_closures Not_all_values_known
          | Sets_of_closures (Exactly sets) ->
            let joined =
              Joined_sets_of_closures.create ~importer ~type_of_name sets
            in
            Sets_of_closures (Exactly joined)
          | Strings strs -> Strings strs
          | Float_arrays { lengths; } -> Float_arrays { lengths; }
        in
        Values values
      | Naked_immediates is -> Naked_immediates is
      | Naked_floats fs -> Naked_floats fs
      | Naked_int32s is -> Naked_int32s is
      | Naked_int64s is -> Naked_int64s is
      | Naked_nativeints is -> Naked_nativeints is
    in
    invariant t;
    t

  let create ~importer ~type_of_name t : t * (Name.t option) =
    let t0, canonical_name =
      Evaluated_first_stage.create ~importer ~type_of_name t
    in
    let t = of_evaluated_first_stage ~importer ~type_of_name t0 in
    t, canonical_name

  let create_ignore_name ~importer ~type_of_name t =
    let t, _name = create ~importer ~type_of_name t in
    t
end

let is_bottom ~importer ~type_of_name t =
  Evaluated.is_bottom (Evaluated.create_ignore_name ~importer ~type_of_name t)

let is_known ~importer ~type_of_name t =
  Evaluated.is_known (Evaluated.create_ignore_name ~importer ~type_of_name t)

let is_useful ~importer ~type_of_name t =
  Evaluated.is_useful (Evaluated.create_ignore_name ~importer ~type_of_name t)

let all_not_useful ~importer ~type_of_name ts =
  List.for_all (fun t -> not (is_useful ~importer ~type_of_name t)) ts

type reification_result =
  | Term of Simple.t * t
  | Cannot_reify
  | Invalid

let reify ~importer ~type_of_name ~allow_free_variables ~expected_kind t
      : reification_result =
  let original_t = t in
  let t, _canonical_name = resolve_aliases ~importer ~type_of_name t in
  let t_evaluated, canonical_name =
    Evaluated.create ~importer ~type_of_name t
  in
  let try_name () : reification_result =
    match canonical_name with
    | None -> Cannot_reify
    | Some name ->
      match name with
      | Var _ when not allow_free_variables -> Cannot_reify
      | Var _ | Symbol _ -> Term (Simple.name name, t)
  in
  let result =
    match t_evaluated with
    | Values values ->
      begin match values with
      | Bottom -> Invalid
      | Tagged_immediates_only (Exactly imms) ->
        begin match Immediate.Set.get_singleton imms with
        | Some imm -> Term (Simple.const (Tagged_immediate imm), t)
        | None -> try_name ()
        end
      | Unknown
      | Blocks_and_tagged_immediates _
      | Tagged_immediates_only _
      | Boxed_floats _
      | Boxed_int32s _
      | Boxed_int64s _
      | Boxed_nativeints _
      | Closures _
      | Sets_of_closures _
      | Strings _
      | Float_arrays _ -> try_name ()
      end
    | Naked_immediates (Exactly is) ->
      begin match Immediate.Set.get_singleton is with
      | Some i -> Term (Simple.const (Untagged_immediate i), t)
      | None -> try_name ()
      end
    | Naked_floats (Exactly fs) ->
      begin match Float.Set.get_singleton fs with
      | Some f -> Term (Simple.const (Naked_float f), t)
      | None -> try_name ()
      end
    | Naked_int32s (Exactly is) ->
      begin match Int32.Set.get_singleton is with
      | Some i -> Term (Simple.const (Naked_int32 i), t)
      | None -> try_name ()
      end
    | Naked_int64s (Exactly is) ->
      begin match Int64.Set.get_singleton is with
      | Some i -> Term (Simple.const (Naked_int64 i), t)
      | None -> try_name ()
      end
    | Naked_nativeints (Exactly is) ->
      begin match Targetint.Set.get_singleton is with
      | Some i -> Term (Simple.const (Naked_nativeint i), t)
      | None -> try_name ()
      end
    | Naked_immediates Not_all_values_known
    | Naked_floats Not_all_values_known
    | Naked_int32s Not_all_values_known
    | Naked_int64s Not_all_values_known
    | Naked_nativeints Not_all_values_known -> try_name ()
  in
  let kind = Evaluated.kind t_evaluated in
  if not (Flambda_kind.compatible kind ~if_used_at:expected_kind) then begin
    Misc.fatal_errorf "Type %a, resolved to %a, cannot be used at kind %a"
      print original_t
      print t
      K.print expected_kind
  end;
  result

let get_field ~importer ~type_of_name t ~field_index
      ~(field_kind : Flambda_primitive.field_kind) : get_field_result =
  let t_evaluated, _canonical_name =
    Evaluated.create ~importer ~type_of_name t
  in
  let expected_result_kind =
    (* CR mshinwell: This should move to a new module called
       [Flambda_primitive.Field_kind] *)
    match field_kind with
    | Not_a_float -> K.value Must_scan
    | Float -> K.naked_float ()
  in
  match t_evaluated with
  | Values values ->
    begin match values with
    | Unknown -> Ok (unknown expected_result_kind Other)
    | Blocks_and_tagged_immediates (Exactly (blocks, imms)) ->
      if not (Immediate.Set.is_empty imms) then
        Invalid
      else
        Blocks.get_field ~importer ~type_of_name blocks ~field_index
          ~expected_result_kind
    | Float_arrays { lengths; } ->
      let if_used_at = Flambda_kind.naked_float () in
      (* CR mshinwell: If this check fails, maybe it's always a compiler bug?
         We need to check how the kind for [Block_load] is set in the frontend
         (i.e. Pfield / Pfloatfield). *)
      if not (Flambda_kind.compatible expected_result_kind ~if_used_at) then
        Invalid
      else
        let index_is_out_of_range_for_all_lengths =
          match lengths with
          | Not_all_values_known -> false
          | Exactly lengths ->
            Int.Set.for_all (fun length ->
                field_index < 0 || field_index >= length)
              lengths
        in
        if index_is_out_of_range_for_all_lengths then
          Invalid
        else
          Ok (unknown (Flambda_kind.naked_float ()) Other)
    | Bottom
    | Blocks_and_tagged_immediates _
    | Tagged_immediates_only _
    | Boxed_floats _
    | Boxed_int32s _
    | Boxed_int64s _
    | Boxed_nativeints _
    | Closures _
    | Sets_of_closures _
    | Strings _ -> Invalid
    end
  | Naked_immediates _
  | Naked_floats _
  | Naked_int32s _
  | Naked_int64s _
  | Naked_nativeints _ ->
    Misc.fatal_errorf "Cannot extract field %d from block with the following \
        type (invalid kind): %a"
      field_index
      print t

type boxed_float_proof =
  | Proved of Float.Set.t Or_not_all_values_known.t
  | Invalid

let prove_boxed_float ~importer ~type_of_name t : boxed_float_proof =
  let t_evaluated, _canonical_name =
    Evaluated.create ~importer ~type_of_name t
  in
  match t_evaluated with
  | Values values ->
    begin match values with
    | Unknown
    | Boxed_floats Not_all_values_known -> Proved Not_all_values_known
    | Boxed_floats (Exactly fs) ->
      if Float.Set.is_empty fs then Invalid
      else Proved (Exactly fs)
    | Blocks_and_tagged_immediates _
    | Bottom
    | Tagged_immediates_only _
    | Boxed_int32s _
    | Boxed_int64s _
    | Boxed_nativeints _
    | Closures _
    | Sets_of_closures _
    | Strings _
    | Float_arrays _ -> Invalid
    end
  | Naked_immediates _
  | Naked_floats _
  | Naked_int32s _
  | Naked_int64s _
  | Naked_nativeints _ ->
    Misc.fatal_errorf "Wrong kind for something claimed to be a boxed \
        float: %a"
      print t

type boxed_int32_proof =
  | Proved of Int32.Set.t Or_not_all_values_known.t
  | Invalid

let prove_boxed_int32 ~importer ~type_of_name t : boxed_int32_proof =
  let t_evaluated, _canonical_name =
    Evaluated.create ~importer ~type_of_name t
  in
  match t_evaluated with
  | Values values ->
    begin match values with
    | Unknown
    | Boxed_int32s Not_all_values_known -> Proved Not_all_values_known
    | Boxed_int32s (Exactly fs) ->
      if Int32.Set.is_empty fs then Invalid
      else Proved (Exactly fs)
    | Blocks_and_tagged_immediates _
    | Bottom
    | Tagged_immediates_only _
    | Boxed_floats _
    | Boxed_int64s _
    | Boxed_nativeints _
    | Closures _
    | Sets_of_closures _
    | Strings _
    | Float_arrays _ -> Invalid
    end
  | Naked_immediates _
  | Naked_floats _
  | Naked_int32s _
  | Naked_int64s _
  | Naked_nativeints _ ->
    Misc.fatal_errorf "Wrong kind for something claimed to be a boxed \
        int32: %a"
      print t

type boxed_int64_proof =
  | Proved of Int64.Set.t Or_not_all_values_known.t
  | Invalid

let prove_boxed_int64 ~importer ~type_of_name t : boxed_int64_proof =
  let t_evaluated, _canonical_name =
    Evaluated.create ~importer ~type_of_name t
  in
  match t_evaluated with
  | Values values ->
    begin match values with
    | Unknown
    | Boxed_int64s Not_all_values_known -> Proved Not_all_values_known
    | Boxed_int64s (Exactly fs) ->
      if Int64.Set.is_empty fs then Invalid
      else Proved (Exactly fs)
    | Blocks_and_tagged_immediates _
    | Bottom
    | Tagged_immediates_only _
    | Boxed_floats _
    | Boxed_int32s _
    | Boxed_nativeints _
    | Closures _
    | Sets_of_closures _
    | Strings _
    | Float_arrays _ -> Invalid
    end
  | Naked_immediates _
  | Naked_floats _
  | Naked_int32s _
  | Naked_int64s _
  | Naked_nativeints _ ->
    Misc.fatal_errorf "Wrong kind for something claimed to be a boxed \
        int64: %a"
      print t

type boxed_nativeint_proof =
  | Proved of Targetint.Set.t Or_not_all_values_known.t
  | Invalid

let prove_boxed_nativeint ~importer ~type_of_name t : boxed_nativeint_proof =
  let t_evaluated, _canonical_name =
    Evaluated.create ~importer ~type_of_name t
  in
  match t_evaluated with
  | Values values ->
    begin match values with
    | Unknown
    | Boxed_nativeints Not_all_values_known -> Proved Not_all_values_known
    | Boxed_nativeints (Exactly fs) ->
      if Targetint.Set.is_empty fs then Invalid
      else Proved (Exactly fs)
    | Blocks_and_tagged_immediates _
    | Bottom
    | Tagged_immediates_only _
    | Boxed_floats _
    | Boxed_int32s _
    | Boxed_int64s _
    | Closures _
    | Sets_of_closures _
    | Strings _
    | Float_arrays _ -> Invalid
    end
  | Naked_immediates _
  | Naked_floats _
  | Naked_int32s _
  | Naked_int64s _
  | Naked_nativeints _ ->
    Misc.fatal_errorf "Wrong kind for something claimed to be a boxed \
        nativeint: %a"
      print t

let prove_naked_float ~importer ~type_of_name t
      : Float.Set.t Or_not_all_values_known.t =
  let t_evaluated, _canonical_name =
    Evaluated.create ~importer ~type_of_name t
  in
  match t_evaluated with
  | Naked_floats fs -> fs
  | Values _
  | Naked_immediates _
  | Naked_int32s _
  | Naked_int64s _
  | Naked_nativeints _ ->
    Misc.fatal_errorf "Wrong kind for something claimed to be a naked \
        float: %a"
      print t

type tagged_immediate_proof =
  | Proved of Immediate.Set.t Or_not_all_values_known.t
  | Invalid

let prove_tagged_immediate ~importer ~type_of_name t =
  let t_evaluated, _canonical_name =
    Evaluated.create ~importer ~type_of_name t
  in
  match t_evaluated with
  | Values values ->
    begin match values with
    | Unknown
    | Tagged_immediates_only Not_all_values_known -> Proved Not_all_values_known
    | Tagged_immediates_only (Exactly is) -> Proved (Exactly is)
    | Boxed_nativeints _
    | Blocks_and_tagged_immediates _
    | Bottom
    | Boxed_floats _
    | Boxed_int32s _
    | Boxed_int64s _
    | Closures _
    | Sets_of_closures _
    | Strings _
    | Float_arrays _ -> Invalid
    end
  | Naked_immediates _
  | Naked_floats _
  | Naked_int32s _
  | Naked_int64s _
  | Naked_nativeints _ ->
    Misc.fatal_errorf "Wrong kind for something claimed to be a tagged \
        immediate: %a"
      print t

type string_proof =
  | Proved of String_info.Set.t Or_not_all_values_known.t
  | Invalid

let prove_string ~importer ~type_of_name t =
  let t_evaluated, _canonical_name =
    Evaluated.create ~importer ~type_of_name t
  in
  match t_evaluated with
  | Values values ->
    begin match values with
    | Unknown
    | Strings Not_all_values_known -> Proved Not_all_values_known
    | Strings (Exactly strs) -> Proved (Exactly strs)
    | Tagged_immediates_only _
    | Boxed_nativeints _
    | Blocks_and_tagged_immediates _
    | Bottom
    | Boxed_floats _
    | Boxed_int32s _
    | Boxed_int64s _
    | Closures _
    | Sets_of_closures _
    | Float_arrays _ -> Invalid
    end
  | Naked_immediates _
  | Naked_floats _
  | Naked_int32s _
  | Naked_int64s _
  | Naked_nativeints _ ->
    Misc.fatal_errorf "Wrong kind for something claimed to be a string: %a"
      print t

type lengths_of_arrays_or_blocks_proof =
  | Proved of Int.Set.t Or_not_all_values_known.t
  | Invalid

let lengths_of_arrays_or_blocks ~importer ~type_of_name t
      : lengths_of_arrays_or_blocks_proof =
  let result =
    let t_evaluated, _canonical_name =
      Evaluated.create ~importer ~type_of_name t
    in
    match t_evaluated with
    | Values values ->
      begin match values with
      | Unknown
      | Float_arrays { lengths =  Not_all_values_known; } ->
        Proved Not_all_values_known
      | Float_arrays { lengths = Exactly lengths; } ->
        Proved (Exactly lengths)
      | Blocks_and_tagged_immediates (Exactly (blocks, imms)) ->
        if not (Immediate.Set.is_empty imms) then
          Invalid
        else
          begin match Blocks.unique_tag_and_size blocks with
          | None -> Invalid
          | Some (_tag, size) -> Proved (Exactly (Int.Set.singleton size))
          end
      | Boxed_floats _
      | Bottom
      | Blocks_and_tagged_immediates _
      | Tagged_immediates_only _
      | Boxed_int32s _
      | Boxed_int64s _
      | Boxed_nativeints _
      | Closures _
      | Sets_of_closures _
      | Strings _ -> Invalid
      end
    | Naked_immediates _
    | Naked_floats _
    | Naked_int32s _
    | Naked_int64s _
    | Naked_nativeints _ ->
      Misc.fatal_errorf "Wrong kind for something claimed to be an array \
          or structured block: %a"
        print t
  in
  match result with
  | Invalid -> Invalid
  | Proved _ ->
    (* XXX [Obj.truncate] can only make blocks shorter, which is a fact we
       should be able to use *)
    if Config.ban_obj_dot_truncate then result
    else Proved Not_all_values_known

(* XXX Lengths of strings: for this, I think we can assume that Obj.truncate
   is always illegal here *)

type closures_proof =
  | Proved of Joined_closures.t Or_not_all_values_known.t
  | Invalid

let prove_closures ~importer ~type_of_name t : closures_proof =
  let t_evaluated, _canonical_name =
    Evaluated.create ~importer ~type_of_name t
  in
  match t_evaluated with
  | Values values ->
    begin match values with
    | Unknown
    | Closures Not_all_values_known -> Proved Not_all_values_known
    | Closures (Exactly set) -> Proved (Exactly set)
    | Bottom
    | Boxed_floats _
    | Blocks_and_tagged_immediates _
    | Tagged_immediates_only _
    | Boxed_int32s _
    | Boxed_int64s _
    | Boxed_nativeints _
    | Sets_of_closures _
    | Strings _
    | Float_arrays _ -> Invalid
    end
  | Naked_immediates _
  | Naked_floats _
  | Naked_int32s _
  | Naked_int64s _
  | Naked_nativeints _ ->
    Misc.fatal_errorf "Wrong kind for something claimed to be one or more \
        closures: %a"
      print t

type sets_of_closures_proof =
  | Proved of Joined_sets_of_closures.t Or_not_all_values_known.t
  | Invalid

let prove_sets_of_closures ~importer ~type_of_name t : sets_of_closures_proof =
  let t_evaluated, _canonical_name =
    Evaluated.create ~importer ~type_of_name t
  in
  match t_evaluated with
  | Values values ->
    begin match values with
    | Unknown -> Proved Not_all_values_known
    | Sets_of_closures set -> Proved set
    | Bottom
    | Boxed_floats _
    | Blocks_and_tagged_immediates _
    | Tagged_immediates_only _
    | Boxed_int32s _
    | Boxed_int64s _
    | Boxed_nativeints _
    | Closures _
    | Strings _
    | Float_arrays _ -> Invalid
    end
  | Naked_immediates _
  | Naked_floats _
  | Naked_int32s _
  | Naked_int64s _
  | Naked_nativeints _ ->
    Misc.fatal_errorf "Wrong kind for something claimed to be a set of \
        closures: %a"
      print t

(*
type proved_scannable_block =
  | Ok of Tag.Scannable.t * ty_value array
  | Can't_prove

let prove_scannable_block t : proved_scannable_block =
  match prove_unboxable_or_untaggable t with
  | Blocks_and_tagged_immediates (blocks, imms) ->
    if not (Immediate.Set.is_empty imms) then Wrong
    else
      begin match Tag.Scannable.Map.get_singleton blocks with
      | Some (tag, fields) -> Ok (tag, fields)
      | None -> Wrong
      end
  | Wrong
  | Tagged_immediates _
  | Boxed_floats _
  | Boxed_int32s _
  | Boxed_int64s _
  | Boxed_nativeints _ -> Wrong

let reify_as_tagged_immediate t =
  match prove_unboxable_or_untaggable t with
  | Blocks_and_tagged_immediates (blocks, imms) ->
    if not (Immediate.Set.is_empty blocks) then None
    else
      begin match imms with
      | Not_all_values_known -> None
      | Exactly imms -> Immediate.Set.get_singleton imms
      end
  | Boxed_floats _
  | Boxed_int32s _
  | Boxed_int64s _
  | Boxed_nativeints _
  | Wrong -> None
*)

type switch_branch_classification =
  | Cannot_be_taken
  | Can_be_taken
  | Must_be_taken

let classify_switch_branch ~importer ~type_of_name t ~scrutinee branch
      : switch_branch_classification =
  let t_evaluated, _canonical_name =
    Evaluated.create ~importer ~type_of_name t
  in
  match t_evaluated with
  | Values values ->
    begin match values with
    | Unknown
    | Tagged_immediates_only Not_all_values_known -> Can_be_taken
    | Tagged_immediates_only (Exactly all_possible_values) ->
      let all_possible_values =
        Immediate.set_to_targetint_set all_possible_values
      in
      if Targetint.Set.mem branch all_possible_values then Must_be_taken
      else Cannot_be_taken
    | Bottom
    | Blocks_and_tagged_immediates _
    | Boxed_floats _
    | Boxed_int32s _
    | Boxed_int64s _
    | Boxed_nativeints _
    | Closures _
    | Sets_of_closures _
    | Strings _
    | Float_arrays _ -> Cannot_be_taken
    end
  | Naked_immediates _
  | Naked_floats _
  | Naked_int32s _
  | Naked_int64s _
  | Naked_nativeints _ ->
    Misc.fatal_errorf "Switch on %a has wrong kind: the scrutinee must have \
        kind [Value]"
      Name.print scrutinee

let as_or_more_precise _t ~than:_ =
  Misc.fatal_error "not yet implemented"

let strictly_more_precise _t ~than:_ =
  Misc.fatal_error "not yet implemented"

module No_importing = struct
  let import_export_id _ = None
  let import_symbol _ = None
end

module Null_importer = Make_importer (No_importing)

let null_importer = (module Null_importer : Importer)
