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

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module F0 = Flambda0
module Named = F0.Named

module Float = Numbers.Float
module Int32 = Numbers.Int32
module Int64 = Numbers.Int64

include F0.Flambda_type

let unknown_types_from_arity t =
  List.map (fun kind -> unknown kind Other) t

(*
let ty_value_is_bottom (ty : ty_value) =
  match maybe_import_value_type ~import_type ty with
  | Ok Bottom -> true
  | Ok Unknown | Ok (Ok _) | Treat_as_unknown -> false
*)

let rename_variables ~importer t ~f =
  clean ~importer t (fun var -> Available_different_name (f var))

let unresolved_symbol sym =
  any_value Must_scan (Unresolved_value (Symbol sym))

let this_tagged_immediate_named n : Named.t * t =
  Const (Tagged_immediate n), this_tagged_immediate n

let this_tagged_bool_named b : Named.t * t =
  let imm =
    if b then Immediate.bool_true
    else Immediate.bool_false
  in
  Const (Tagged_immediate imm), this_tagged_immediate imm

(*
let this_boxed_float_named f dbg : Named.t * t =
  Prim (Unary (Box_number Naked_float), this_boxed_float f

let this_boxed_int32_named n dbg : Named.t * t =
  Allocated_const (Boxed_int32 n), this_boxed_int32 n

let this_boxed_int64_named n dbg : Named.t * t =
  Allocated_const (Boxed_int64 n), this_boxed_int64 n

let this_boxed_nativeint_named n dbg : Named.t * t =
  Allocated_const (Boxed_nativeint n), this_boxed_nativeint n
*)

let this_untagged_immediate_named n : Named.t * t =
  Const (Untagged_immediate n), this_naked_immediate n

let this_naked_float_named f : Named.t * t =
  Const (Naked_float f), this_naked_float f

let this_naked_int32_named n : Named.t * t =
  Const (Naked_int32 n), this_naked_int32 n

let this_naked_int64_named n : Named.t * t =
  Const (Naked_int64 n), this_naked_int64 n

let this_naked_nativeint_named n : Named.t * t =
  Const (Naked_nativeint n), this_naked_nativeint n

(*
let is_boxed_float t =
  match descr t with
  | Boxed_number (Float, t) ->
    begin match descr t with
    | Unboxed_float _ -> true
    | _ -> false
    end
  | Float_array _ | Unknown _ | Bottom | Union _
  | Immutable_string _ | Mutable_string _
  | Set_of_closures _ | Closure _ | Load_lazily _ | Boxed_number _
  | Unboxed_float _ | Unboxed_int32 _ | Unboxed_int64 _
  | Unboxed_nativeint _ -> false

let is_float_array t =
  match descr t with
  | Float_array _ -> true
  | Unknown _ | Bottom | Union _
  | Immutable_string _ | Mutable_string _
  | Set_of_closures _ | Closure _ | Load_lazily _ | Boxed_number _
  | Unboxed_float _ | Unboxed_int32 _ | Unboxed_int64 _
  | Unboxed_nativeint _ -> false

let invalid_to_mutate t =
  match descr t with
  | Union unionable -> Unionable.invalid_to_mutate unionable
  | Mutable_string _
  (* CR mshinwell: Split Float_array into Immutable and Mutable? *)
  | Float_array { contents = Contents _; size = _; } -> false
  | Unknown _ | Bottom | Immutable_string _
  | Float_array { contents = Unknown_or_mutable; size = _; }
  | Set_of_closures _ | Closure _ | Load_lazily _ | Boxed_number _
  | Unboxed_float _ | Unboxed_int32 _ | Unboxed_int64 _
  | Unboxed_nativeint _ -> true

let type_for_bound_var (set_of_closures : set_of_closures) var =
  try Var_within_closure.Map.find var set_of_closures.bound_vars
  with Not_found ->
    Misc.fatal_errorf "The set-of-closures type %a@ does not \
        bind the variable %a@.%s@."
      print_set_of_closures set_of_closures
      Var_within_closure.print var
      (Printexc.raw_backtrace_to_string (Printexc.get_callstack max_int))

(* Given a set-of-closures type and a closure ID, apply any
   freshening specified in the type to the closure ID, and return
   that new closure ID.  A fatal error is produced if the new closure ID
   does not correspond to a function declaration in the given type. *)
let freshen_and_check_closure_id (set_of_closures : set_of_closures)
      (closure_id : Closure_id.Set.t) =
  let closure_id =
    Freshening.Project_var.apply_closure_ids
      set_of_closures.freshening closure_id
  in
  Closure_id.Set.iter (fun closure_id ->
    try
      ignore (F0.Function_declarations.find closure_id
        set_of_closures.function_decls)
    with Not_found ->
      Misc.fatal_error (Format.asprintf
        "Function %a not found in the set of closures@ %a@.%a@."
        Closure_id.print closure_id
        print_set_of_closures set_of_closures
        F0.Function_declarations.print set_of_closures.function_decls))
    closure_id;
  closure_id

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
    | Set_of_closures _, Set_of_closures _ -> false
    | Set_of_closures _, _ | _, Set_of_closures _ -> true
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

type get_field_result =
  | Ok of t
  | Invalid _

let get_field t ~field_index:i : get_field_result =
  match descr t with
  | Union union ->
    begin match Unionable.flatten union with
    | Ok (Block (_tag, fields)) ->
      if i >= 0 && i < Array.length fields then begin
        Ok fields.(i)
      end else begin
        (* This (unfortunately) cannot be a fatal error; it can happen if a
           .cmx file is missing or with GADT code.  However for debugging the
           compiler this can be a useful point to put a [Misc.fatal_errorf]. *)
        Invalid _
      end
    | Ok (Int _ | Char _ | Constptr _) ->
      (* Something seriously wrong is happening: either the user is doing
         something exceptionally unsafe, or it is an unreachable branch.
         We consider this as unreachable and mark the result accordingly. *)
      Invalid _
    | Bottom -> Invalid _
    | Unknown -> Ok (unknown (Flambda_kind.value ()) Other)
    end
  (* CR-someday mshinwell: This should probably return Invalid _ in more
     cases.  I added a couple more. *)
  | Bottom -> Invalid _
  | Float_array _ ->
    (* For the moment we return "unknown" even for immutable arrays, since
       it isn't possible for user code to project from an immutable array. *)
    (* CR-someday mshinwell: If Leo's array's patch lands, then we can
       change this, although it's probably not Pfield that is used to
       do the projection. *)
    Ok (unknown (Flambda_kind.value ()) Other)
  | Unboxed_float _ | Unboxed_int32 _ | Unboxed_int64 _ | Unboxed_nativeint _
  | Immutable_string _ | Mutable_string _ | Boxed_number _ ->
    (* The user is doing something unsafe. *)
    Invalid _
  | Set_of_closures _ | Closure _
    (* These are used by [CamlinternalMod]. *)
  | Load_lazily _ ->
    (* These should have been resolved.
       Note that the contents of blocks must always be of kind [Value]. *)
    Ok (unknown (Flambda_kind.value ()) Other)
  | Unknown (_block_kind, reason) ->
    Ok (unknown (Flambda_kind.value ()) reason)

let length_of_array t =
  match descr t with
  | Union union -> Unionable.size_of_block union
  | Float_array { contents = Contents floats; _ } -> Some (Array.length floats)
  | _ -> None  (* Could be improved later if required. *)
*)

let follow_variable_equality t ~is_present_in_env =
  match var t with
  | Some var when is_present_in_env var -> Some var
  | _ -> None

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
  | Float_array _ | Bottom | Set_of_closures _ | Closure _
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
end

module Blocks = struct
  type t = ty_value array Tag.Scannable.Map.t

  let is_bottom t = Tag.Scannable.Map.is_empty t

  let join ~importer t1 t2 : t or_wrong =
    let exception Same_tag_different_arities in
    try
      let map =
        Tag.Scannable.Map.union (fun _tag fields1 fields2 ->
            if Array.length fields1 <> Array.length fields2 then
              raise Same_tag_different_arities
            else
              let fields =
                Array.map2 (fun ty_value1 ty_value2 ->
                    join_ty_value ~importer ty_value1 ty_value2)
                  fields1 fields2
              in
              Some fields)
          t1 t2
      in
      Ok map
    with Same_tag_different_arities -> Wrong

  let meet ~importer t1 t2 : t or_wrong =
    let exception Same_tag_different_arities in
    try
      let map =
        Tag.Scannable.Map.union (fun _tag fields1 fields2 ->
            if Array.length fields1 <> Array.length fields2 then
              raise Same_tag_different_arities
            else
              let fields =
                Array.map2 (fun ty_value1 ty_value2 ->
                    meet_ty_value ~importer ty_value1 ty_value2)
                  fields1 fields2
              in
              Some fields)
          t1 t2
      in
      Ok map
    with Same_tag_different_arities -> Wrong
end

module Joined_set_of_closures : sig
  type t

  val create : Set_of_closures.Set.t -> t

  val function_decls : t -> function_declaration Closure_id.Map.t
  val closure_elements : t -> ty_value Var_within_closure.Map.t

  val to_type : t -> flambda_type
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

  let of_set_of_closures (set : set_of_closures) : t =
    { set_of_closures_id_and_origin =
        Exactly (set.set_of_closures_id, set.set_of_closures_origin);
      function_decls = set.function_decls;
      closure_elements = set.closure_elements;
    }

  let to_type t =
    match t.set_of_closures_id_and_origin with
    | Not_all_values_known -> any_value Must_scan Other
    | Exactly (set_of_closures_id, set_of_closures_origin) ->
      let set =
        create_set_of_closures ~set_of_closures_id
          ~set_of_closures_origin
          ~function_decls:t.function_decls
          ~closure_elements:t.closure_elements
      in
      set_of_closures set

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

  let join_and_make_all_functions_non_inlinable ~importer
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
      let result = List.map2 (join ~importer) f1_result f2_result in
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
        (fun ty -> any_value_as_ty_value (scanning_ty_value ~importer ty) Other)
        (fun ty1 ty2 -> join_ty_value ~importer ty1 ty2)
        t1.closure_elements t2.closure_elements
    in
    { set_of_closures_var = None;
      set_of_closures_id_and_origin = Not_all_values_known;
      function_decls;
      closure_elements;
    }

  let join ~importer (t1 : t) (t2 : t) : t =
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
        Var_within_closure.Map.union_merge (join_ty_value ~importer)
          t1.closure_elements t2.closure_elements
      in
      let set_of_closures_var =
        match t1.set_of_closures_var with
        | Some var -> Some var
        | None ->
          match t2.set_of_closures_var with
          | Some var -> Some var
          | None -> None
      in
      { set_of_closures_var;
        set_of_closures_id_and_origin;
        function_decls = t1.function_decls;
        closure_elements;
      }
    | Ok Not_all_values_known | Wrong ->
      join_and_make_all_functions_non_inlinable ~importer t1 t2

  let create ~importer (sets : set_of_closures list) : t =
    let sets = List.map of_set_of_closures sets in
    match sets with
    | [] ->
      (* CR mshinwell: This is a bit strange: should there be a proper
         constructor for "bottom" here? *)
      { set_of_closures_id_and_origin = None;
        function_decls = Closure_id.Map.empty;
        closure_elements = Var_within_closure.Map.empty;
      }
    | set::sets ->
      List.fold_left (fun result t -> join ~importer result t) set sets

  include Identifiable.Make (struct
    type nonrec t = t

    let print = print

    let compare t1 t2 =
      (* CR mshinwell for pchambart: Is this correct? *)
      Set_of_closures
  end)
end

module Make_with_name (T : Identifiable.S) = struct
  include Identifiable.Make (struct
    type t = T.t * Name.t

    let compare (t1, name1) (t2, name2) =
      let c = T.compare t1 t2 in
      if c <> 0 then c
      else Misc.Stdlib.Option.compare Name.compare name1 name2

    let equal t1 t2 =
      compare t1 t2 = 0

    let hash (t, name) =
      Hashtbl.hash (T.hash t, Misc.Stdlib.Option.hash Name.hash name)

    let print ppf (t, name) =
      match name with
      | None -> T.print ppf t
      | Some name -> Format.fprintf ppf "%a = %a" T.print t Name.print name
  end)
end

module Naked_immediate_with_name = Make_with_name (Naked_immediate)
module Float_with_name = Make_with_name (Float)
module Int32_with_name = Make_with_name (Int32)
module Int64_with_name = Make_with_name (Int64)
module Targetint_with_name = Make_with_name (Targetint)
module Closure_with_name = Make_with_name (Closure)
module Set_of_closures_with_name = Make_with_name (Set_of_closures)

module Evaluated = struct
  type t0 =
    | Unknown
    | Bottom
    | Blocks_and_tagged_immediates of
        (Blocks.With_names.t * Immediate.With_name.Set.t)
          Or_not_all_values_known.t
    | Boxed_floats of Float_with_name.Set.t Or_not_all_values_known.t
    | Boxed_int32s of Int32_with_name.Set.t Or_not_all_values_known.t
    | Boxed_int64s of Int64_with_name.Set.t Or_not_all_values_known.t
    | Boxed_nativeints of Targetint_with_name.Set.t Or_not_all_values_known.t
    | Naked_immediates of
        Naked_immediate_with_name.Set.t Or_not_all_values_known.t
    | Naked_floats of Float_with_name.Set.t Or_not_all_values_known.t
    | Naked_int32s of Int32_with_name.Set.t Or_not_all_values_known.t
    | Naked_int64s of Int64_with_name.Set.t Or_not_all_values_known.t
    | Naked_nativeints of Targetint_with_name.Set.t Or_not_all_values_known.t
    | Closures of Closure_with_name.Set.t Or_not_all_values_known.t
    | Set_of_closures of
        Set_of_closures_with_name.Set.t Or_not_all_values_known.t

  type t =
    | Unknown
    | Bottom
    | Blocks_and_tagged_immediates of
        (Blocks.With_names.t * Immediate.With_name.Set.t)
          Or_not_all_values_known.t
    | Boxed_floats of Float_with_name.Set.t Or_not_all_values_known.t
    | Boxed_int32s of Int32_with_name.Set.t Or_not_all_values_known.t
    | Boxed_int64s of Int64_with_name.Set.t Or_not_all_values_known.t
    | Boxed_nativeints of Targetint_with_name.Set.t Or_not_all_values_known.t
    | Naked_immediates of
        Naked_immediate_with_name.Set.t Or_not_all_values_known.t
    | Naked_floats of Float_with_name.Set.t Or_not_all_values_known.t
    | Naked_int32s of Int32_with_name.Set.t Or_not_all_values_known.t
    | Naked_int64s of Int64_with_name.Set.t Or_not_all_values_known.t
    | Naked_nativeints of Targetint_with_name.Set.t Or_not_all_values_known.t
    | Closures of
        Joined_set_of_closures.t Closure_id.t Or_not_all_values_known.t
    | Set_of_closures of Joined_set_of_closures.t Or_not_all_values_known.t

  let t_of_t0 (t0 : t0) : t =
    match t0 with
    | Unknown -> Unknown
    | Bottom -> Bottom
    | Blocks_and_tagged_immediates blocks ->
      Blocks_and_tagged_immediates blocks
    | Boxed_floats fs -> Boxed_floats fs
    | Boxed_int32s is -> Boxed_int32s is
    | Boxed_int64s is -> Boxed_int64s is
    | Boxed_nativeints is -> Boxed_nativeints is
    | Naked_floats fs -> Boxed_floats fs
    | Naked_int32s is -> Boxed_int32s is
    | Naked_int64s is -> Boxed_int64s is
    | Naked_nativeints is -> Boxed_nativeints is
    | Closures Not_all_values_known -> Closures Not_all_values_known
    | Closures (Exactly map) ->
      let map = Closure_id.Map.map Joined_set_of_closures.create map in
      Closures (Exactly map)
    | Set_of_closures Not_all_values_known ->
      Set_of_closures Not_all_values_known
    | Set_of_closures (Exactly sets) ->
      Set_of_closures (Exactly (Joined_set_of_closures.create sets))

  let is_unknown (t : t) =
    match t with
    | Unknown
    | Blocks_and_tagged_immediates Not_all_values_known
    | Boxed_floats Not_all_values_known
    | Boxed_int32s Not_all_values_known
    | Boxed_int64s Not_all_values_known
    | Boxed_nativeints Not_all_values_known
    | Naked_floats Not_all_values_known
    | Naked_int32s Not_all_values_known
    | Naked_int64s Not_all_values_known
    | Naked_nativeints Not_all_values_known
    | Closures Not_all_values_known
    | Set_of_closures Not_all_values_known -> true
    | Bottom
    | Blocks_and_tagged_immediates _
    | Boxed_floats (Exactly _)
    | Boxed_int32s (Exactly _)
    | Boxed_int64s (Exactly _)
    | Boxed_nativeints (Exactly _)
    | Naked_floats (Exactly _)
    | Naked_int32s (Exactly _)
    | Naked_int64s (Exactly _)
    | Naked_nativeints (Exactly _)
    | Closures (Exactly _)
    | Set_of_closures (Exactly _) -> false

  let is_known t = not (is_unknown t)

  let is_bottom (t : t) =
    match t with
    | Bottom
    | Blocks_and_tagged_immediates (Exactly (blocks, imms)) ->
      Blocks.is_bottom blocks && Immediate.Set.empty imms
    | Boxed_floats (Exactly fs) -> Float.Set.is_empty fs
    | Boxed_int32s (Exactly is) -> Int32.Set.is_empty is
    | Boxed_int64s (Exactly is) -> Int64.Set.is_empty is
    | Boxed_nativeints (Exactly is) -> Nativeint.Set.is_empty is
    | Naked_floats (Exactly fs) -> Float.Set.is_empty fs
    | Naked_int32s (Exactly is) -> Int32.Set.is_empty is
    | Naked_int64s (Exactly is) -> Int64.Set.is_empty is
    | Naked_nativeints (Exactly is) -> Nativeint.Set.is_empty is
    | Closures (Exactly map) -> Closure_id.Map.is_empty map
    | Unknown
    | Blocks_and_tagged_immediates Not_all_values_known
    | Boxed_floats Not_all_values_known
    | Boxed_int32s Not_all_values_known
    | Boxed_int64s Not_all_values_known
    | Boxed_nativeints Not_all_values_known
    | Naked_floats Not_all_values_known
    | Naked_int32s Not_all_values_known
    | Naked_int64s Not_all_values_known
    | Naked_nativeints Not_all_values_known
    | Closures Not_all_values_known
    | Set_of_closures _ -> false

  let is_non_bottom t = not (is_bottom t)

  let useful t = is_known t && is_non_bottom t

  let join ~importer ~type_of_name t1 t2 =
    let join_immediates =
      Or_not_all_values_known.join (fun imms1 imms2 : _ or_wrong ->
        Ok (Immediate.join_set imms1  imms2))
    in
    match t1, t2 with
    | Unknown, _ | _, Unknown -> Unknown
    | Bottom, _ -> t2
    | _, Bottom -> t1
    | Blocks_and_tagged_immediates (b1, imms1),
        Blocks_and_tagged_immediates (b2, imms2) ->
      let blocks_join = Blocks.join ~importer b1 b2 in
      let imms_join = join_immediates imms1 imms2 in
      begin match blocks_join, imms_join with
      | Ok blocks, Ok imms -> Blocks_and_tagged_immediates (blocks, imms)
      | Wrong, _ | _, Wrong -> Unknown
      end
    | Boxed_floats fs1, Boxed_floats fs2 ->
      begin match
        Or_not_all_values_known.join (fun fs1 fs2 : Float.Set.t or_wrong ->
           Ok (Float.Set.union fs1 fs2))
          fs1 fs2
      with
      | Ok fs -> Boxed_floats fs
      | Wrong -> Unknown
      end
    | Boxed_int32s is1, Boxed_int32s is2 ->
      begin match
        Or_not_all_values_known.join (fun is1 is2 : Int32.Set.t or_wrong ->
            Ok (Int32.Set.union is1 is2))
          is1 is2
      with
      | Ok is -> Boxed_int32s is
      | Wrong -> Unknown
      end
    | Boxed_int64s is1, Boxed_int64s is2 ->
      begin match
        Or_not_all_values_known.join (fun is1 is2 : Int64.Set.t or_wrong ->
            Ok (Int64.Set.union is1 is2))
          is1 is2
      with
      | Ok is -> Boxed_int64s is
      | Wrong -> Unknown
      end
    | Boxed_nativeints is1, Boxed_nativeints is2 ->
      begin match
        Or_not_all_values_known.join (fun is1 is2 : Targetint.Set.t or_wrong ->
            Ok (Targetint.Set.union is1 is2))
          is1 is2
      with
      | Ok is -> Boxed_nativeints is
      | Wrong -> Unknown
      end
    | Closures closures1, Closures closures2 ->
      begin match
        Or_not_all_values_known.join (fun map1 map2 : _ or_wrong ->
          let map =
            Closure_id.Map.union_merge (Set_of_closures.join ~importer)
              map1 map2
          in
          (* CR pchambart: Could this fail and not be a real error *)
          Ok map)
          closures1 closures2
      with
      | Ok closures -> Closures closures
      | Wrong -> Unknown
      end
    | Set_of_closures set1, Set_of_closures set2 ->
      begin match
        Or_not_all_values_known.join (fun set1 set2 : _ or_wrong ->
          Ok (Set_of_closures.join ~importer set1 set2))
          set1 set2
      with
      | Ok set_of_closures -> Set_of_closures set_of_closures
      | Wrong -> Unknown
      end
    | (Blocks_and_tagged_immediates _
      | Boxed_floats _
      | Boxed_int32s _
      | Boxed_int64s _
      | Boxed_nativeints _
      | Naked_floats _
      | Naked_int32s _
      | Naked_int64s _
      | Naked_nativeints _
      | Closures _
      | Set_of_closures _), _ -> Unknown

  let meet ~importer ~type_of_name t1 t2 =
    let meet_immediates =
      Or_not_all_values_known.meet (fun imms1 imms2 : _ or_wrong ->
        Ok (Immediate.meet_set imms1  imms2))
    in
    match t1, t2 with
    | Bottom, _ | _, Bottom -> Bottom
    | Unknown, _ -> t2
    | _, Unknown -> t1
    | Blocks_and_tagged_immediates (b1, imms1),
        Blocks_and_tagged_immediates (b2, imms2) ->
      let blocks_meet = Blocks.meet ~importer b1 b2 in
      let imms_meet = meet_immediates imms1 imms2 in
      begin match blocks_meet, imms_meet with
      | Ok blocks, Ok imms -> Blocks_and_tagged_immediates (blocks, imms)
      | Wrong, _ | _, Wrong -> Unknown
      end
    | Boxed_floats fs1, Boxed_floats fs2 ->
      begin match
        Or_not_all_values_known.meet (fun fs1 fs2 : Float.Set.t or_wrong ->
           Ok (Float.Set.inter fs1 fs2))
          fs1 fs2
      with
      | Ok fs -> Boxed_floats fs
      | Wrong -> Unknown
      end
    | Boxed_int32s is1, Boxed_int32s is2 ->
      begin match
        Or_not_all_values_known.meet (fun is1 is2 : Int32.Set.t or_wrong ->
            Ok (Int32.Set.inter is1 is2))
          is1 is2
      with
      | Ok is -> Boxed_int32s is
      | Wrong -> Unknown
      end
    | Boxed_int64s is1, Boxed_int64s is2 ->
      begin match
        Or_not_all_values_known.meet (fun is1 is2 : Int64.Set.t or_wrong ->
            Ok (Int64.Set.inter is1 is2))
          is1 is2
      with
      | Ok is -> Boxed_int64s is
      | Wrong -> Unknown
      end
    | Boxed_nativeints is1, Boxed_nativeints is2 ->
      begin match
        Or_not_all_values_known.meet (fun is1 is2 : Targetint.Set.t or_wrong ->
            Ok (Targetint.Set.inter is1 is2))
          is1 is2
      with
      | Ok is -> Boxed_nativeints is
      | Wrong -> Unknown
      end
    | Closures closures1, Closures closures2 ->
      begin match
        Or_not_all_values_known.meet (fun map1 map2 : _ or_wrong ->
          let map =
            Closure_id.Map.union_merge (Set_of_closures.meet ~importer)
              map1 map2
          in
          (* CR pchambart: Could this fail and not be a real error *)
          Ok map)
          closures1 closures2
      with
      | Ok closures -> Closures closures
      | Wrong -> Unknown
      end
    | Set_of_closures set1, Set_of_closures set2 ->
      begin match
        Or_not_all_values_known.meet (fun set1 set2 : _ or_wrong ->
          Ok (Set_of_closures.meet ~importer set1 set2))
          set1 set2
      with
      | Ok set_of_closures -> Set_of_closures set_of_closures
      | Wrong -> Unknown
      end
    | (Blocks_and_tagged_immediates _
      | Boxed_floats _
      | Boxed_int32s _
      | Boxed_int64s _
      | Boxed_nativeints _
      | Naked_floats _
      | Naked_int32s _
      | Naked_int64s _
      | Naked_nativeints _
      | Closures _
      | Set_of_closures _), _ -> Bottom
end

type 'a known_unknown_or_wrong =
  | Known of 'a
  | Unknown
  | Wrong

let prove_naked_immediate_from_ty_naked_immediate ~importer
      (ty : ty_naked_immediate) : _ known_unknown_or_wrong =
  let module I = (val importer : Importer) in
  let ty = I.import_naked_immediate_type_as_resolved_ty_naked_immediate ty in
  match ty.descr with
  | Unknown _ -> Unknown
  | Ok (Naked_immediate i) -> Known i
  | Bottom -> Wrong

let prove_naked_float_from_ty_naked_float ~importer
      (ty : ty_naked_float) : _ known_unknown_or_wrong =
  let module I = (val importer : Importer) in
  let ty = I.import_naked_float_type_as_resolved_ty_naked_float ty in
  match ty.descr with
  | Unknown _ -> Unknown
  | Ok (Naked_float f) -> Known f
  | Bottom -> Wrong

let prove_naked_int32_from_ty_naked_int32 ~importer
      (ty : ty_naked_int32) : _ known_unknown_or_wrong =
  let module I = (val importer : Importer) in
  let ty = I.import_naked_int32_type_as_resolved_ty_naked_int32 ty in
  match ty.descr with
  | Unknown _ -> Unknown
  | Ok (Naked_int32 i) -> Known i
  | Bottom -> Wrong

let prove_naked_int64_from_ty_naked_int64 ~importer
      (ty : ty_naked_int64) : _ known_unknown_or_wrong =
  let module I = (val importer : Importer) in
  let ty = I.import_naked_int64_type_as_resolved_ty_naked_int64 ty in
  match ty.descr with
  | Unknown _ -> Unknown
  | Ok (Naked_int64 i) -> Known i
  | Bottom -> Wrong

let prove_naked_nativeint_from_ty_naked_nativeint ~importer
      (ty : ty_naked_nativeint) : _ known_unknown_or_wrong =
  let module I = (val importer : Importer) in
  let ty = I.import_naked_nativeint_type_as_resolved_ty_naked_nativeint ty in
  match ty.descr with
  | Unknown _ -> Unknown
  | Ok (Naked_nativeint i) -> Known i
  | Bottom -> Wrong

let eval ~importer ~type_of_name (t : t) : Evaluated.t =
  let module I = (val importer : Importer) in
  let eval ~importer_this_kind ~force_to_kind
        ~(eval_singleton : _ -> Evaluated.t0) ty =
    let resolved_ty_value, canonical_name =
      resolve_aliases_and_squash_unresolved_names
        ~importer_this_kind:I.import_value_type_as_resolved_ty_value
        ~force_to_kind:force_to_kind_value
        ~type_of_name
        ty
    in
    begin match resolved_ty_value with
    | Unknown _ -> Unknown
    | Bottom -> Bottom
    | Ok or_combination ->
      begin match or_combination with
      | Singleton singleton -> eval_singleton singleton ~canonical_name
      | Combination (Union, ty1, ty2) ->
        let t1 : t = Normal ty1 in
        let t2 : t = Normal ty2 in
        let eval1 = eval ~importer ~type_of_name t1 in
        let eval2 = eval ~importer ~type_of_name t2 in
        (* XXX does anything need to happen with [canonical_name]? *)
        Evaluated.join eval1 eval2
      | Combination (Intersection, ty1, ty2) ->
        let t1 : t = Normal ty1 in
        let t2 : t = Normal ty2 in
        let eval1 = eval ~importer ~type_of_name t1 in
        let eval2 = eval ~importer ~type_of_name t2 in
        Evaluated.meet eval1 eval2
      end
  in
  let t0 : Evaluated.t0 =
    match t with
    | Value ty ->
      let eval_singleton (o : of_kind_value) ~canonical_name : Evaluated.t0 =
        match o with
        | Tagged_immediate ty ->
          begin match
            prove_naked_immediate_from_ty_naked_immediate ~importer ty
          with
          | Wrong -> Unknown
          | Unknown ->
            Blocks_and_tagged_immediates (
              Tag.Scannable.Map.empty, Not_all_values_known)
          | Known i ->
            let i = Immediate_with_name.create i canonical_name in
            Blocks_and_tagged_immediates (
              Tag.Scannable.Map.empty,
              Exactly (Immediate_with_name.Set.singleton i))
          end
        | Boxed_float ty ->
          begin match
            prove_naked_float_from_ty_naked_float ~importer ty
          with
          | Wrong -> Unknown
          | Unknown -> Boxed_floats Not_all_values_known
          | Known f ->
            let f = Float_with_name.create f canonical_name in
            Boxed_floats (Exactly (Float_with_name.Set.singleton f))
          end
        | Boxed_int32 ty ->
          begin match
            prove_naked_int32_from_ty_naked_int32 ~importer ty
          with
          | Wrong -> Unknown
          | Unknown -> Boxed_int32s Not_all_values_known
          | Known i ->
            let i = Int32_with_name.create i canonical_name in
            Boxed_int32s (Exactly (Int32_with_name.Set.singleton i))
          end
        | Boxed_int64 ty ->
          begin match
            prove_naked_int64_from_ty_naked_int64 ~importer ty
          with
          | Wrong -> Unknown
          | Unknown -> Boxed_int64s Not_all_values_known
          | Known i ->
            let i = Int64_with_name.create i canonical_name in
            Boxed_int64s (Exactly (Int64_with_name.Set.singleton i))
          end
        | Boxed_nativeint ty ->
          begin match
            prove_naked_nativeint_from_ty_naked_nativeint ~importer ty
          with
          | Wrong -> Unknown
          | Unknown -> Boxed_nativeints Not_all_values_known
          | Known i ->
            let i = Targetint_with_name.create i canonical_name in
            Boxed_nativeints (Exactly (Targetint_with_name.Set.singleton i))
          end
        | Block (tag, fields) ->
          let blocks =
            Tag.Scannable.Map.add tag fields Tag.Scannable.Map.empty
          in
          Blocks_and_tagged_immediates (blocks,
            Exactly Immediate_with_name.Set.empty)
        | Closure _ ->
          Unknown
            (* [@ppwarning "TODO"] *)
        | Set_of_closures set ->
          Set_of_closures (Exactly (
            Set_of_closures.create ~set_of_closures_var:resolved_ty_value.var
              set))
        | String _
        | Float_array _ -> Unknown
      in
      eval ~importer_this_kind:I.import_value_type_as_resolved_ty_value
        ~force_to_kind:force_to_kind_value
        ~eval_singleton
        ty
    | Naked_immediate ty ->
      let eval_singleton (o : of_kind_naked_immediate) ~canonical_name
            : Evaluated.t0 =
        match o with
        | Naked_immediate imm ->
          let imm = Naked_immediate_with_name.create imm canonical_name in
          Naked_immediates (Exactly (
            Naked_immediate_with_name.Set.singleton imm))
      in
      eval ~importer_this_kind:
          I.import_naked_immediate_type_as_resolved_ty_naked_immediate
        ~force_to_kind:force_to_kind_naked_immediate
        ~eval_singleton
        ty
    | Naked_float ty ->
      let eval_singleton (o : of_kind_naked_float) ~canonical_name
            : Evaluated.t0 =
        match o with
        | Naked_float f ->
          let f = Naked_float_with_name.create f canonical_name in
          Naked_floats (Exactly (
            Naked_float_with_name.Set.singleton f))
      in
      eval ~importer_this_kind:
          I.import_naked_float_type_as_resolved_ty_naked_float
        ~force_to_kind:force_to_kind_naked_float
        ~eval_singleton
        ty
    | Naked_int32 ty ->
      let eval_singleton (o : of_kind_naked_int32) ~canonical_name
            : Evaluated.t0 =
        match o with
        | Naked_int32 i ->
          let i = Naked_int32_with_name.create i canonical_name in
          Naked_int32s (Exactly (
            Naked_int32_with_name.Set.singleton i))
      in
      eval ~importer_this_kind:
          I.import_naked_int32_type_as_resolved_ty_naked_int32
        ~force_to_kind:force_to_kind_naked_int32
        ~eval_singleton
        ty
    | Naked_int64 ty ->
      let eval_singleton (o : of_kind_naked_int64) ~canonical_name
            : Evaluated.t0 =
        match o with
        | Naked_int64 i ->
          let i = Naked_int64_with_name.create i canonical_name in
          Naked_int64s (Exactly (
            Naked_int64_with_name.Set.singleton i))
      in
      eval ~importer_this_kind:
          I.import_naked_int64_type_as_resolved_ty_naked_int64
        ~force_to_kind:force_to_kind_naked_int64
        ~eval_singleton
        ty
    | Naked_nativeint ty ->
      let eval_singleton (o : of_kind_naked_nativeint) ~canonical_name
            : Evaluated.t0 =
        match o with
        | Naked_nativeint i ->
          let i = Naked_nativeint_with_name.create i canonical_name in
          Naked_nativeints (Exactly (
            Naked_nativeint_with_name.Set.singleton i))
      in
      eval ~importer_this_kind:
          I.import_naked_nativeint_type_as_resolved_ty_naked_nativeint
        ~force_to_kind:force_to_kind_naked_nativeint
        ~eval_singleton
        ty
  in
  Evaluated.t0_to_t t0

let is_bottom ~importer ~type_of_name t =
  Evaluated.is_bottom (eval ~importer ~type_of_name t)

let is_known ~importer ~type_of_name t =
  Evaluated.is_known (eval ~importer ~type_of_name t)

let is_useful ~importer ~type_of_name t =
  Evaluated.is_useful (eval ~importer ~type_of_name t)

let all_not_useful ~importer ts =
  List.for_all (fun t -> not (useful ~importer t)) ts

let reify ~importer t : Named.t option =
  let try_symbol () =
    match symbol t with
    | Some sym -> Some (Named.Symbol sym)
    | None -> None
  in
  match eval ~importer t with
  | Blocks_and_tagged_immediates (blocks, imms) ->
    begin match imms with
    | Exactly imms ->
      begin match Immediate.Set.get_singleton imms with
      | Some imm ->
        if Tag.Scannable.Map.is_empty blocks then
          Some (Named. (Tagged_immediate imm))
        else
          None
      | None -> None
      end
    | Not_all_values_known -> None
    end
  | Naked_floats (Exactly fs) ->
    begin match Float.Set.singleton fs with
    | Some f -> Some (Flambda.Named.Const (Naked_float f))
    | 
  | Naked_int32s _
  | Naked_int64s _
  | Naked_nativeints _
  | Bottom -> None
  | Unknown
  | Boxed_floats _
  | Boxed_int32s _
  | Boxed_int64s _
  | Boxed_nativeints _
  | Naked_floats Not_all_values_known
  | Naked_int32s Not_all_values_known
  | Naked_int64s Not_all_values_known
  | Naked_nativeints Not_all_values_known
  | Closures _
  | Set_of_closures _ -> try_symbol ()

let reify_using_env ~importer t ~is_present_in_env =
  match reify ~importer t with
  | None ->
    begin match var t with
    | Some var when is_present_in_env var -> Some (Flambda.Named.Var var)
    | _ -> None
    end
  | Some named -> Some named

let prove_set_of_closures ~importer t : _ known_unknown_or_wrong =
  match eval ~importer t with
  | Set_of_closures (Exactly set) -> Known set
  | Set_of_closures Not_all_values_known
  | Unknown -> Unknown
  | Bottom
  | Blocks_and_tagged_immediates _
  | Boxed_floats _
  | Boxed_int32s _
  | Boxed_int64s _
  | Boxed_nativeints _
  | Naked_floats _
  | Naked_int32s _
  | Naked_int64s _
  | Naked_nativeints _
  | Closures _ -> Wrong

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

let reify_as_boxed_float t =
  match prove_unboxable_or_untaggable t with
  | Boxed_floats fs -> Float.Set.get_singleton fs
  | Boxed_floats Not_all_values_known
  | Blocks_and_tagged_immediates _
  | Boxed_int32s _
  | Boxed_int64s _
  | Boxed_nativeints _
  | Wrong -> None

type strict_reified_as_set_of_closures =
  | Wrong
  | Ok of Variable.t option * set_of_closures

let strict_reify_as_set_of_closures t
      : strict_reified_as_set_of_closures =
  match reify_as_set_of_closures t with
  | Ok (var, value_set_of_closures) -> Ok (var, value_set_of_closures)
  | Wrong | Unresolved _ | Unknown -> Wrong

type reified_as_closure_allowing_unresolved =
  | Wrong
  | Unresolved of unresolved_value
  | Unknown
  | Ok of set_of_closures Closure_id.Map.t * Variable.t option * Symbol.t option

let reify_as_closure_allowing_unresolved t
      : reified_as_closure_allowing_unresolved =
  match descr t with
  | Closure closure -> begin
    match Closure_id.Map.get_singleton closure.potential_closures with
    | None -> begin
      try
        let closures =
          Closure_id.Map.map (fun (set_of_closures : t) ->
            match set_of_closures.descr with
            | Set_of_closures set_of_closures -> set_of_closures
            | Closure _ | Union _ | Boxed_number _ | Unboxed_float _
            | Unboxed_int32 _ | Unboxed_int64 _ | Unboxed_nativeint _
            | Unknown _ | Bottom | Load_lazily _ | Immutable_string _
            | Mutable_string _ | Float_array _  ->
              raise Exit)
            closure.potential_closures
        in
        Ok (closures, None, None)
      with Exit -> Wrong
      end
    | Some (closure_id, set_of_closures) ->
      match set_of_closures.descr with
      | Set_of_closures value_set_of_closures ->
        let symbol = match set_of_closures.symbol with
          | Some (symbol, None) -> Some symbol
          | None | Some (_, Some _) -> None
        in
        Ok (Closure_id.Map.singleton closure_id value_set_of_closures,
            set_of_closures.var, symbol)
      | Closure _ | Boxed_number _ | Unboxed_float _ | Unboxed_int32 _
      | Unboxed_int64 _ | Unboxed_nativeint _ | Unknown _ | Bottom
      | Load_lazily _ | Immutable_string _ | Mutable_string _ | Float_array _
      | Union _ -> Wrong
    end
  | Unknown (_, Unresolved_value value) -> Unresolved value
  | Set_of_closures _ | Union _ | Boxed_number _
  | Unboxed_float _ | Unboxed_int32 _ | Unboxed_int64 _ | Unboxed_nativeint _
  | Bottom | Load_lazily _ | Immutable_string _ | Mutable_string _
  | Float_array _  -> Wrong
  (* CR-soon mshinwell: This should be unwound once the reason for a value
     being unknown can be correctly propagated through the export info. *)
  | Unknown (_, Other) -> Unknown

type strict_reified_as_closure_singleton =
  | Wrong
  | Ok of Closure_id.t * Variable.t option * Symbol.t option * set_of_closures

let strict_reify_as_closure_singleton t
  : strict_reified_as_closure_singleton =
  match reify_as_closure_allowing_unresolved t with
  | Ok (closures, set_of_closures_var, set_of_closures_symbol) -> begin
    match Closure_id.Map.get_singleton closures with
    | None -> Wrong
    | Some (closure_id, value_set_of_closures) ->
      Ok (closure_id, set_of_closures_var, set_of_closures_symbol,
          value_set_of_closures)
    end
  | Wrong | Unknown | Unresolved _ -> Wrong

type strict_reified_as_closure =
  | Wrong
  | Ok of set_of_closures Closure_id.Map.t * Variable.t option * Symbol.t option

let strict_reify_as_closure t : strict_reified_as_closure =
  match reify_as_closure_allowing_unresolved t with
  | Ok (closures, set_of_closures_var, set_of_closures_symbol) ->
    Ok (closures, set_of_closures_var, set_of_closures_symbol)
  | Wrong | Unknown | Unresolved _ -> Wrong

type switch_branch_classification =
  | Cannot_be_taken
  | Can_be_taken
  | Must_be_taken

let classify_switch_branch t branch ~import_type
      : switch_branch_classification =
  match join_boxed_immediates t ~import_type with
  | Unknown Value -> Can_be_taken
  | Unknown _ | Bottom -> Cannot_be_taken
  | Ok all_possible_values ->
    if Targetint.Set.mem branch all_possible_values then Must_be_taken
    else Cannot_be_taken

let as_or_more_precise _t ~than:_ =
  Misc.fatal_error "not yet implemented"

let strictly_more_precise _t ~than:_ =
  Misc.fatal_error "not yet implemented"



let join_boxed_immediates t ~import_type : Immediate.Set.t fold_result =
  match join_unboxable t ~import_type with
  | Ok (Blocks_and_immediates { blocks; immediates; }) ->
    if Targetint.Set.is_empty blocks then Ok immediates
    else Bottom
  | Ok (Boxed_floats _ | Boxed_int32s _ | Boxed_int64s _
      | Boxed_nativeints _) ->
    Bottom
  | (Unknown _ | Bottom) as result -> result

let unique_boxed_immediate_in_join t ~import_type =
  match join_boxed_immediates t ~import_type with
  | Ok all_possible_values -> Immediate.Set.get_singleton all_possible_values
  | Unknown _ | Bottom -> None
*)
