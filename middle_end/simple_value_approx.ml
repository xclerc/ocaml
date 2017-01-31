(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

(* CR mshinwell: turn this off once namespacing issues sorted *)
[@@@ocaml.warning "-44-45"]

type unknown_because_of =
  | Unresolved_symbol of Symbol.t
  | Other

module rec T : sig
  type 'a boxed_int =
    | Int32 : int32 boxed_int
    | Int64 : int64 boxed_int
    | Nativeint : nativeint boxed_int

  type value_string = {
    (* CR-soon mshinwell: use variant *)
    contents : string option; (* None if unknown or mutable *)
    size : int;
  }

  type t = {
    descr : descr;
    var : Variable.t option;
    symbol : (Symbol.t * int option) option;
  }

  and descr =
    | Union of Unionable.t
    (* CR mshinwell: These next two should presumably go into [Union] so we
       can unbox them *)
    | Float of float option
    | Boxed_int : 'a boxed_int * 'a -> descr
    | Set_of_closures of value_set_of_closures
    | Closure of value_closure
    | String of value_string
    | Float_array of value_float_array
    | Unknown of unknown_because_of
    | Bottom
    | Extern of Export_id.t
    | Symbol of Symbol.t
    | Unresolved of Symbol.t

  and value_closure = {
    potential_closures : t Closure_id.Map.t;
  } [@@unboxed]

  and value_set_of_closures = {
    function_decls : Flambda.function_declarations;
    bound_vars : t Var_within_closure.Map.t;
    invariant_params : Variable.Set.t Variable.Map.t lazy_t;
    size : int option Variable.Map.t lazy_t;
    specialised_args : Flambda.specialised_args;
    freshening : Freshening.Project_var.t;
    direct_call_surrogates : Closure_id.t Closure_id.Map.t;
  }

  and value_float_array_contents =
    | Contents of t array
    | Unknown_or_mutable

  and value_float_array = {
    contents : value_float_array_contents;
    size : int;
  }

  val join : really_import_approx:(t -> t) -> t -> t -> t

  val equal_boxed_int : 'a boxed_int -> 'a -> 'b boxed_int -> 'b -> bool

  val print : Format.formatter -> t -> unit
  val print_descr : Format.formatter -> descr -> unit
  val print_value_set_of_closures
    : Format.formatter
    -> value_set_of_closures
    -> unit
end = struct
  include T

  let equal_boxed_int (type t1) (type t2)
        (bi1 : t1 boxed_int) (i1 : t1)
        (bi2 : t2 boxed_int) (i2 : t2) =
    match bi1, bi2 with
    | Int32, Int32 -> Int32.equal i1 i2
    | Int64, Int64 -> Int64.equal i1 i2
    | Nativeint, Nativeint -> Nativeint.equal i1 i2
    | _ -> false

  (* Closures and set of closures descriptions cannot be merged.

    let f x =
      let g y -> x + y in
      g
    in
    let v =
      if ...
      then f 1
      else f 2
    in
    v 3

    The approximation for [f 1] and [f 2] could both contain the
    description of [g]. But if [f] where inlined, a new [g] would
    be created in each branch, leading to incompatible description.
    And we must never make the descrition for a function less
    precise that it used to be: its information are needed for
    rewriting [Project_var] and [Project_closure] constructions
    in [Inline_and_simplify].
  *)
  let rec join_descr ~really_import_approx d1 d2 =
    match d1, d2 with
    | Union union1, Union union2 ->
      begin match Unionable.join union1 union2 ~really_import_approx with
      | Ok union -> Union union
      | Bottom -> Bottom
      end
    | Symbol s1, Symbol s2 when Symbol.equal s1 s2 -> d1
    | Extern e1, Extern e2 when Export_id.equal e1 e2 -> d1
    | Float i, Float j when i = j -> d1
    | Boxed_int (bi1, i1), Boxed_int (bi2, i2)
        when equal_boxed_int bi1 i1 bi2 i2 -> d1
    | Closure { potential_closures = map1 },
      Closure { potential_closures = map2 } ->
      let potential_closures =
        Closure_id.Map.union_merge
          (* CR pchambart:
            merging the closure value might loose information in the
            case of one branch having the approximation and the other
            having 'Unknown'. We could imagine such as

            {[if ... then M1.f else M2.f]}

            where M1 is where the function is defined and M2 is

            {[let f = M3.f]}

            and M3 is

            {[let f = M1.f]}

            with the cmx for M3 missing

            Since we know that the approximation comes from the same
            value, we know that both version provide additional
            information on the value. Hence what we really want is an
            approximation intersection, not an union (that this join
            is). *)
          (join ~really_import_approx)
          map1 map2
      in
      Closure { potential_closures }
    | _ -> Unknown Other

  and join ~really_import_approx a1 a2 =
    match a1, a2 with
    | { descr = Bottom }, a
    | a, { descr = Bottom } -> a
    | { descr = (Symbol _ | Extern _) }, _
    | _, { descr = (Symbol _ | Extern _) } ->
      join ~really_import_approx
        (really_import_approx a1) (really_import_approx a2)
    | _ ->
        let var =
          match a1.var, a2.var with
          | None, _ | _, None -> None
          | Some v1, Some v2 ->
            if Variable.equal v1 v2 then Some v1
            else None
        in
        let symbol =
          match a1.symbol, a2.symbol with
          | None, _ | _, None -> None
          | Some (v1, field1), Some (v2, field2) ->
            if Symbol.equal v1 v2 then
              match field1, field2 with
              | None, None -> a1.symbol
              | Some f1, Some f2 when f1 = f2 -> a1.symbol
              | _ -> None
            else None
        in
        { descr = join_descr ~really_import_approx a1.descr a2.descr;
          var;
          symbol;
        }

  let print_value_set_of_closures ppf
        { function_decls = { funs }; invariant_params; freshening; _ } =
    Format.fprintf ppf
      "(set_of_closures:@ %a invariant_params=%a freshening=%a)"
      (fun ppf -> Variable.Map.iter (fun id _ -> Variable.print ppf id)) funs
      (Variable.Map.print Variable.Set.print) (Lazy.force invariant_params)
      Freshening.Project_var.print freshening

  let rec print_descr ppf = function
    | Union union -> Unionable.print ppf union
    | Unknown reason ->
      begin match reason with
      | Unresolved_symbol symbol ->
        Format.fprintf ppf "?(due to unresolved symbol '%a')"
          Symbol.print symbol
      | Other -> Format.fprintf ppf "?"
      end;
    | Bottom -> Format.fprintf ppf "bottom"
    | Extern id -> Format.fprintf ppf "_%a_" Export_id.print id
    | Symbol sym -> Format.fprintf ppf "%a" Symbol.print sym
    | Closure { potential_closures } ->
      Format.fprintf ppf "(closure:@ @[<2>[@ ";
      Closure_id.Map.iter (fun closure_id set_of_closures ->
        Format.fprintf ppf "%a @[<2>from@ %a@];@ "
          Closure_id.print closure_id
          print set_of_closures)
        potential_closures;
      Format.fprintf ppf "]@])";
    | Set_of_closures set_of_closures ->
      print_value_set_of_closures ppf set_of_closures
    | Unresolved sym ->
      Format.fprintf ppf "(unresolved %a)" Symbol.print sym
    | Float (Some f) -> Format.pp_print_float ppf f
    | Float None -> Format.pp_print_string ppf "float"
    | String { contents; size } -> begin
        match contents with
        | None ->
            Format.fprintf ppf "string %i" size
        | Some s ->
            let s =
              if size > 10
              then String.sub s 0 8 ^ "..."
              else s
            in
            Format.fprintf ppf "string %i %S" size s
      end
    | Float_array float_array ->
      begin match float_array.contents with
      | Unknown_or_mutable ->
        Format.fprintf ppf "float_array %i" float_array.size
      | Contents _ ->
        Format.fprintf ppf "float_array_imm %i" float_array.size
      end
    | Boxed_int (t, i) ->
      match t with
      | Int32 -> Format.fprintf ppf "%li" i
      | Int64 -> Format.fprintf ppf "%Li" i
      | Nativeint -> Format.fprintf ppf "%ni" i

  and print ppf { descr; var; symbol; } =
    let print ppf = function
      | None -> Symbol.print_opt ppf None
      | Some (sym, None) -> Symbol.print ppf sym
      | Some (sym, Some field) ->
          Format.fprintf ppf "%a.(%i)" Symbol.print sym field
    in
    Format.fprintf ppf "{ descr=%a var=%a symbol=%a }"
      print_descr descr
      Variable.print_opt var
      print symbol
end and Unionable : sig
  module Immediate : sig
    type t = private
      | Int of int
      | Char of char
      | Constptr of int

    include Identifiable.S with type t := t
  end

  type blocks = T.t array Tag.Map.t

  (* Other representations are possible, but this one has two nice properties:
     1. It doesn't involve any comparison on values of type [T.t].
     2. It lines up with the classification of approximations required when
        unboxing (cf. [Unbox_one_variable]). *)
  type t =
    | Blocks of blocks
    | Blocks_and_immediates of blocks * Immediate.Set.t
    | Immediates of Immediate.Set.t

  val print : Format.formatter -> t -> unit

  val value_int : int -> t
  val value_char : char -> t
  val value_constptr : int -> t
  val value_block : Tag.t -> T.t array -> t

  val useful : t -> bool

  type 'a or_bottom =
    | Ok of 'a
    | Bottom

  val join : t -> t -> really_import_approx:(T.t -> T.t) -> t or_bottom

  type singleton = private
    | Block of Tag.t * T.t array
    | Int of int
    | Char of char
    | Constptr of int

  val flatten : t -> singleton or_bottom

  val maybe_is_immediate_value : t -> int -> bool
  val maybe_is_block_with_tag : t -> Tag.t -> bool
end = struct
  type 'a or_bottom =
    | Ok of 'a
    | Bottom

  module Immediate = struct
    type t =
      | Int of int
      | Char of char
      | Constptr of int

    include Identifiable.Make (struct
      type nonrec t = t

      let compare = Pervasives.compare
      let equal t1 t2 = (compare t1 t2 = 0)
      let hash = Hashtbl.hash

      let print ppf t =
        match t with
        | Int i -> Format.pp_print_int ppf i
        | Char c -> Format.fprintf ppf "%c" c
        | Constptr i -> Format.fprintf ppf "%ia" i

      let output _ _ = Misc.fatal_error "Not implemented"
    end)

    let join t1 t2 : t or_bottom =
      if equal t1 t2 then Ok t1
      else Bottom

    let join_set ts =
      let t = Set.choose ts in
      let ts = Set.remove t ts in
      Set.fold (fun t ts ->
          match ts with
          | Ok ts -> join t ts
          | Bottom -> Bottom)
        ts (Ok t)
  end

  type blocks = T.t array Tag.Map.t

  let print_blocks ppf (by_tag : blocks) =
    let print_binding ppf (tag, fields) =
      Format.fprintf ppf "@[[|%a: %a|]@]"
        Tag.print tag
        (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ")
          T.print)
        (Array.to_list fields)
    in
    Format.fprintf ppf "@[%a@]"
      (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf " U ")
        print_binding)
      (Tag.Map.bindings by_tag)

  type t =
    | Blocks of blocks
    | Blocks_and_immediates of blocks * Immediate.Set.t
    | Immediates of Immediate.Set.t

  let print ppf t =
    match t with
    | Blocks by_tag ->
      Format.fprintf ppf "@[(blocks (%a))@]"
        print_blocks by_tag
    | Blocks_and_immediates (by_tag, imms) ->
      Format.fprintf ppf "@[(blocks (%a)) U (immediates (%a))@]"
        print_blocks by_tag
        Immediate.Set.print imms
    | Immediates imms ->
      Format.fprintf ppf "@[(immediates (%a))@]"
        Immediate.Set.print imms

  let value_int i =
    Immediates (Immediate.Set.singleton (Int i))

  let value_char c =
    Immediates (Immediate.Set.singleton (Char c))

  let value_constptr p =
    Immediates (Immediate.Set.singleton (Constptr p))

  let value_block tag fields =
    Blocks (Tag.Map.add tag fields Tag.Map.empty)

  let maybe_is_immediate_value t i =
    match t with
    | Blocks _ -> false
    | Blocks_and_immediates (_, imms) | Immediates imms ->
      Immediate.Set.exists (fun (imm : Immediate.t) ->
          match imm with
          | Int i' when i = i' -> true
          | Int _ -> false
          | Char c when i = Char.code c -> true
          | Char _ -> false
          | Constptr p when i = p -> true
          | Constptr _ -> false)
        imms

  let maybe_is_block_with_tag t tag =
    match t with
    | Blocks by_tag | Blocks_and_immediates (by_tag, _) ->
      Tag.Map.exists (fun tag' _ -> Tag.equal tag tag') by_tag
    | Immediates _imms -> false

  let join (t1 : t) (t2 : t) ~really_import_approx : t or_bottom =
    let get_immediates t =
      match t with
      | Blocks _ -> Immediate.Set.empty
      | Blocks_and_immediates (_, imms) | Immediates imms -> imms
    in
    let immediates_t1 = get_immediates t1 in
    let immediates_t2 = get_immediates t2 in
    let immediates = Immediate.Set.union immediates_t1 immediates_t2 in
    let get_blocks t =
      match t with
      | Blocks by_tag | Blocks_and_immediates (by_tag, _) -> by_tag
      | Immediates _ -> Tag.Map.empty
    in
    let blocks_t1 = get_blocks t1 in
    let blocks_t2 = get_blocks t2 in
    let ill_typed_code = ref false in
    let blocks =
      Tag.Map.union (fun _tag fields1 fields2 ->
          if Array.length fields1 <> Array.length fields2 then begin
            (* Two blocks with the same tag but different sizes! *)
            ill_typed_code := true;
            None
          end else begin
            Some (Array.map2 (fun field existing_field ->
                T.join field existing_field ~really_import_approx)
              fields1 fields2)
          end)
        blocks_t1 blocks_t2
    in
    if !ill_typed_code then Bottom
    else if Immediate.Set.is_empty immediates then Ok (Blocks blocks)
    else if Tag.Map.is_empty blocks then Ok (Immediates immediates)
    else Ok (Blocks_and_immediates (blocks, immediates))

  let useful t =
    match t with
    | Blocks blocks -> not (Tag.Map.is_empty blocks)
    | Blocks_and_immediates (blocks, immediates) ->
      (not (Tag.Map.is_empty blocks))
        || (not (Immediate.Set.is_empty immediates))
    | Immediates immediates -> not (Immediate.Set.is_empty immediates)

  type singleton =
    | Block of Tag.t * T.t array
    | Int of int
    | Char of char
    | Constptr of int

  let rec flatten t : singleton or_bottom =
    match t with
    | Blocks by_tag ->
      begin match Tag.Map.bindings by_tag with
      | [tag, fields] -> Ok (Block (tag, fields))
      | _ -> Bottom
      end
    | Blocks_and_immediates (by_tag, imms) ->
      if Tag.Map.is_empty by_tag then flatten (Immediates imms)
      else if Immediate.Set.is_empty imms then flatten (Blocks by_tag)
      else Bottom
    | Immediates imms ->
      match Immediate.join_set imms with
      | Ok (Int i) -> Ok (Int i)
      | Ok (Char c) -> Ok (Char c)
      | Ok (Constptr p) -> Ok (Constptr p)
      | Bottom -> Bottom
end

let equal_boxed_int = T.equal_boxed_int
let print_value_set_of_closures = T.print_value_set_of_closures
let print_descr = T.print_descr
let print = T.print
let join = T.join

(* CR mshinwell: Sort out all this namespacing crap *)

type 'a boxed_int = 'a T.boxed_int =
  | Int32 : int32 boxed_int
  | Int64 : int64 boxed_int
  | Nativeint : nativeint boxed_int

type value_string = T.value_string = {
  (* CR-soon mshinwell: use variant *)
  contents : string option; (* None if unknown or mutable *)
  size : int;
}

type t = T.t = {
  descr : descr;
  var : Variable.t option;
  symbol : (Symbol.t * int option) option;
}

and descr = T.descr =
  | Union of Unionable.t
  | Float of float option
  | Boxed_int : 'a T.boxed_int * 'a -> descr
  | Set_of_closures of value_set_of_closures
  | Closure of value_closure
  | String of T.value_string
  | Float_array of value_float_array
  | Unknown of unknown_because_of
  | Bottom
  | Extern of Export_id.t
  | Symbol of Symbol.t
  | Unresolved of Symbol.t
    (** No description was found for this symbol *)

and value_closure = T.value_closure = {
  potential_closures : t Closure_id.Map.t;
} [@@unboxed]

and value_set_of_closures = T.value_set_of_closures = {
  function_decls : Flambda.function_declarations;
  bound_vars : t Var_within_closure.Map.t;
  invariant_params : Variable.Set.t Variable.Map.t lazy_t;
  size : int option Variable.Map.t lazy_t;
  specialised_args : Flambda.specialised_args;
  freshening : Freshening.Project_var.t;
  direct_call_surrogates : Closure_id.t Closure_id.Map.t;
}

and value_float_array_contents = T.value_float_array_contents =
  | Contents of t array
  | Unknown_or_mutable

and value_float_array = T.value_float_array = {
  contents : value_float_array_contents;
  size : int;
}

let descr t = t.descr
let descrs ts = List.map (fun t -> t.descr) ts

let approx descr = { descr; var = None; symbol = None }

let augment_with_variable t var = { t with var = Some var }
let augment_with_symbol t symbol = { t with symbol = Some (symbol, None) }
let augment_with_symbol_field t symbol field =
  match t.symbol with
  | None -> { t with symbol = Some (symbol, Some field) }
  | Some _ -> t
let replace_description t descr = { t with descr }

let augment_with_kind t (kind:Lambda.value_kind) =
  match kind with
  | Pgenval -> t
  | Pfloatval ->
    begin match t.descr with
    | Float _ ->
      t
    | Unknown _ | Unresolved _ ->
      { t with descr = Float None }
    | Union _
    | Boxed_int _
    | Set_of_closures _
    | Closure _
    | String _
    | Float_array _
    | Bottom ->
      (* Unreachable *)
      { t with descr = Bottom }
    | Extern _ | Symbol _ ->
      (* We don't know yet *)
      t
    end
  | _ -> t

let augment_kind_with_approx t (kind:Lambda.value_kind) : Lambda.value_kind =
  match t.descr with
  | Float _ -> Pfloatval
  | Union union ->
    begin match Unionable.flatten union with
    | Ok (Int _) -> Pintval
    | _ -> kind
    end
  | Boxed_int (Int32, _) -> Pboxedintval Pint32
  | Boxed_int (Int64, _) -> Pboxedintval Pint64
  | Boxed_int (Nativeint, _) -> Pboxedintval Pnativeint
  | _ -> kind

let value_unknown reason = approx (Unknown reason)
let value_int i = approx (Union (Unionable.value_int i))
let value_char i = approx (Union (Unionable.value_char i))
let value_constptr i = approx (Union (Unionable.value_constptr i))
let value_float f = approx (Float (Some f))
let value_any_float = approx (Float None)
let value_boxed_int bi i = approx (Boxed_int (bi,i))

let value_closure ?closure_var ?set_of_closures_var ?set_of_closures_symbol
      closures =
  let approx_set_of_closures value_set_of_closures =
    { descr = Set_of_closures value_set_of_closures;
      var = set_of_closures_var;
      symbol = Misc.may_map (fun s -> s, None) set_of_closures_symbol;
    }
  in
  let potential_closures =
    Closure_id.Map.map approx_set_of_closures closures
  in
  { descr = Closure { potential_closures };
    var = closure_var;
    symbol = None;
  }

let create_value_set_of_closures
      ~(function_decls : Flambda.function_declarations) ~bound_vars
      ~invariant_params ~specialised_args ~freshening
      ~direct_call_surrogates =
  let size =
    lazy (
      let functions = Variable.Map.keys function_decls.funs in
      Variable.Map.map (fun (function_decl : Flambda.function_declaration) ->
          let params = Variable.Set.of_list function_decl.params in
          let free_vars =
            Variable.Set.diff
              (Variable.Set.diff function_decl.free_variables params)
              functions
          in
          let num_free_vars = Variable.Set.cardinal free_vars in
          let max_size =
            Inlining_cost.maximum_interesting_size_of_function_body
              num_free_vars
          in
          Inlining_cost.lambda_smaller' function_decl.body ~than:max_size)
        function_decls.funs)
  in
  { function_decls;
    bound_vars;
    invariant_params;
    size;
    specialised_args;
    freshening;
    direct_call_surrogates;
  }

let update_freshening_of_value_set_of_closures value_set_of_closures
      ~freshening =
  (* CR-someday mshinwell: We could maybe check that [freshening] is
     reasonable. *)
  { value_set_of_closures with freshening; }

let value_set_of_closures ?set_of_closures_var value_set_of_closures =
  { descr = Set_of_closures value_set_of_closures;
    var = set_of_closures_var;
    symbol = None;
  }

let value_block t b = approx (Union (Unionable.value_block t b))

let value_extern ex = approx (Extern ex)
let value_symbol sym =
  { (approx (Symbol sym)) with symbol = Some (sym, None) }
let value_bottom = approx Bottom
let value_unresolved sym = approx (Unresolved sym)

let value_string size contents = approx (String {size; contents })
let value_mutable_float_array ~size =
  approx (Float_array { contents = Unknown_or_mutable; size; } )
let value_immutable_float_array (contents:t array) =
  let size = Array.length contents in
  let contents =
    Array.map (fun t -> augment_with_kind t Pfloatval) contents
  in
  approx (Float_array { contents = Contents contents; size; } )

let make_const_int_named n : Flambda.named * t =
  Const (Int n), value_int n

let make_const_char_named n : Flambda.named * t =
  Const (Char n), value_char n

let make_const_ptr_named n : Flambda.named * t =
  Const (Const_pointer n), value_constptr n

let make_const_bool_named b : Flambda.named * t =
  make_const_ptr_named (if b then 1 else 0)

let make_const_float_named f : Flambda.named * t =
  Allocated_const (Float f), value_float f

let make_const_boxed_int_named (type bi) (t:bi boxed_int) (i:bi)
      : Flambda.named * t =
  let c : Allocated_const.t =
    match t with
    | Int32 -> Int32 i
    | Int64 -> Int64 i
    | Nativeint -> Nativeint i
  in
  Allocated_const c, value_boxed_int t i

type simplification_summary =
  | Nothing_done
  | Replaced_term

type simplification_result_named = Flambda.named * simplification_summary * t

let simplify_named t (named : Flambda.named) : simplification_result_named =
  if Effect_analysis.no_effects_named named then
    match t.descr with
    | Union union ->
      begin match Unionable.flatten union with
      | Ok (Block _) | Bottom ->
        named, Nothing_done, t
      | Ok (Int n) ->
        let const, approx = make_const_int_named n in
        const, Replaced_term, approx
      | Ok (Char n) ->
        let const, approx = make_const_char_named n in
        const, Replaced_term, approx
      | Ok (Constptr n) ->
        let const, approx = make_const_ptr_named n in
        const, Replaced_term, approx
      end
    | Float (Some f) ->
      let const, approx = make_const_float_named f in
      const, Replaced_term, approx
    | Boxed_int (t, i) ->
      let const, approx = make_const_boxed_int_named t i in
      const, Replaced_term, approx
    | Symbol sym ->
      Symbol sym, Replaced_term, t
    | String _ | Float_array _ | Float None
    | Set_of_closures _ | Closure _
    | Unknown _ | Bottom | Extern _ | Unresolved _ ->
      named, Nothing_done, t
  else
    named, Nothing_done, t

(* CR-soon mshinwell: bad name.  This function and its call site in
   [Inline_and_simplify] is also messy. *)
let simplify_var t : (Flambda.named * t) option =
  let try_symbol () : (Flambda.named * t) option =
    match t.symbol with
    | Some (sym, None) -> Some (Symbol sym, t)
    | Some (sym, Some field) -> Some (Read_symbol_field (sym, field), t)
    | None -> None
  in
  match t.descr with
  | Union union ->
    begin match Unionable.flatten union with
    | Ok (Block _) | Bottom -> try_symbol ()
    | Ok (Int n) -> Some (make_const_int_named n)
    | Ok (Char n) -> Some (make_const_char_named n)
    | Ok (Constptr n) -> Some (make_const_ptr_named n)
    end
  | Float (Some f) -> Some (make_const_float_named f)
  | Boxed_int (t, i) -> Some (make_const_boxed_int_named t i)
  | Symbol sym -> Some (Symbol sym, t)
  | String _ | Float_array _ | Float None
  | Set_of_closures _ | Closure _ | Unknown _ | Bottom | Extern _
  | Unresolved _ -> try_symbol ()

let join_summaries summary ~replaced_by_var_or_symbol =
  match replaced_by_var_or_symbol, summary with
  | true, Nothing_done
  | true, Replaced_term
  | false, Replaced_term -> Replaced_term
  | false, Nothing_done -> Nothing_done

let simplify_named_using_env t ~is_present_in_env named =
  let replaced_by_var_or_symbol, named =
    match t.var with
    | Some var when is_present_in_env var ->
      true, Flambda.Var var
    | _ ->
      match t.symbol with
      | Some (sym, None) -> true, (Flambda.Symbol sym:Flambda.named)
      | Some (sym, Some field) ->
        true, Flambda.Read_symbol_field (sym, field)
      | None -> false, named
  in
  let const, summary, approx = simplify_named t named in
  const, join_summaries summary ~replaced_by_var_or_symbol, approx

let simplify_var_to_var_using_env t ~is_present_in_env =
  match t.var with
  | Some var when is_present_in_env var -> Some var
  | _ -> None

let known t =
  match t.descr with
  | Unresolved _ | Unknown _ -> false
  | String _ | Float_array _ | Bottom | Union _ | Set_of_closures _ | Closure _
  | Extern _ | Float _ | Boxed_int _ | Symbol _ -> true

let useful t =
  match t.descr with
  | Unresolved _ | Unknown _ | Bottom -> false
  | Union union -> Unionable.useful union
  | String _ | Float_array _ | Set_of_closures _ | Float _ | Boxed_int _
  | Closure _ | Extern _ | Symbol _ -> true

let all_not_useful ts = List.for_all (fun t -> not (useful t)) ts

let is_definitely_immutable t =
  match t.descr with
  | String { contents = Some _ } | Union _ | Set_of_closures _ | Float _
  | Boxed_int _ | Closure _ -> true
  | String { contents = None } | Float_array _ | Unresolved _ | Unknown _
  | Bottom -> false
  | Extern _ | Symbol _ -> assert false

type get_field_result =
  | Ok of t
  | Unreachable

let get_field t ~field_index:i : get_field_result =
  match t.descr with
  | Union union ->
    begin match Unionable.flatten union with
    | Ok (Block (_tag, fields)) ->
      if i >= 0 && i < Array.length fields then begin
        Ok fields.(i)
      end else begin
        (* This (unfortunately) cannot be a fatal error; it can happen if a
           .cmx file is missing or with GADT code.  However for debugging the
           compiler this can be a useful point to put a [Misc.fatal_errorf]. *)
        Unreachable
      end
    | Ok (Int _ | Char _ | Constptr _) | Bottom ->
      (* Something seriously wrong is happening: either the user is doing
         something exceptionally unsafe, or it is an unreachable branch.
         We consider this as unreachable and mark the result accordingly. *)
      Unreachable
    end
  (* CR-someday mshinwell: This should probably return Unreachable in more
     cases.  I added a couple more. *)
  | Bottom -> Unreachable
  | Float_array _ ->
    (* For the moment we return "unknown" even for immutable arrays, since
       it isn't possible for user code to project from an immutable array. *)
    (* CR-someday mshinwell: If Leo's array's patch lands, then we can
       change this, although it's probably not Pfield that is used to
       do the projection. *)
    Ok (value_unknown Other)
  | String _ | Float _ | Boxed_int _ ->
    (* The user is doing something unsafe. *)
    Unreachable
  | Set_of_closures _ | Closure _
    (* This is used by [CamlinternalMod]. *)
  | Symbol _ | Extern _ ->
    (* These should have been resolved. *)
    Ok (value_unknown Other)
  | Unknown reason ->
    Ok (value_unknown reason)
  | Unresolved sym ->
    (* We don't know anything, but we must remember that it comes
       from another compilation unit in case it contains a closure. *)
    Ok (value_unresolved sym)

type checked_approx_for_block =
  | Wrong
  | Ok of Tag.t * t array

let check_approx_for_block t : checked_approx_for_block =
  match t.descr with
  | Union union ->
    begin match Unionable.flatten union with
    | Ok (Block (tag, fields)) -> Ok (tag, fields)
    | Ok (Int _ | Char _ | Constptr _) | Bottom -> Wrong
    end
  | Bottom | Float_array _ | String _ | Float _ | Boxed_int _
  | Set_of_closures _ | Closure _ | Symbol _ | Extern _
  | Unknown _ | Unresolved _ -> Wrong

type checked_approx_for_variant =
  | Wrong
  | Ok of Unionable.t

let check_approx_for_variant t : checked_approx_for_variant =
  match t.descr with
  | Union union -> Ok union
  | Bottom | Float_array _ | String _ | Float _ | Boxed_int _
  | Set_of_closures _ | Closure _ | Symbol _ | Extern _
  | Unknown _ | Unresolved _ -> Wrong

(* Given a set-of-closures approximation and a closure ID, apply any
   freshening specified in the approximation to the closure ID, and return
   that new closure ID.  A fatal error is produced if the new closure ID
   does not correspond to a function declaration in the given approximation. *)
let freshen_and_check_closure_id
      (value_set_of_closures : value_set_of_closures)
      (closure_id : Closure_id.Set.t) =
  let closure_id =
    Freshening.Project_var.apply_closure_ids
      value_set_of_closures.freshening closure_id
  in
  Closure_id.Set.iter (fun closure_id ->
    try
      ignore (Flambda_utils.find_declaration closure_id
      value_set_of_closures.function_decls)
    with Not_found ->
      Misc.fatal_error (Format.asprintf
        "Function %a not found in the set of closures@ %a@.%a@."
        Closure_id.print closure_id
        print_value_set_of_closures value_set_of_closures
        Flambda.print_function_declarations value_set_of_closures.function_decls))
    closure_id;
  closure_id

type checked_approx_for_set_of_closures =
  | Wrong
  | Unresolved of Symbol.t
  | Unknown
  | Unknown_because_of_unresolved_symbol of Symbol.t
  | Ok of Variable.t option * value_set_of_closures

let check_approx_for_set_of_closures t : checked_approx_for_set_of_closures =
  match t.descr with
  | Unresolved symbol -> Unresolved symbol
  | Unknown (Unresolved_symbol symbol) ->
    Unknown_because_of_unresolved_symbol symbol
  | Set_of_closures value_set_of_closures ->
    (* Note that [var] might be [None]; we might be reaching the set of
       closures via approximations only, with the variable originally bound
       to the set now out of scope. *)
    Ok (t.var, value_set_of_closures)
  | Closure _ | Union _ | Float _ | Boxed_int _ | Unknown _ | Bottom
  | Extern _ | String _ | Float_array _ | Symbol _ -> Wrong

type strict_checked_approx_for_set_of_closures =
  | Wrong
  | Ok of Variable.t option * value_set_of_closures

let strict_check_approx_for_set_of_closures t
      : strict_checked_approx_for_set_of_closures =
  match check_approx_for_set_of_closures t with
  | Ok (var, value_set_of_closures) -> Ok (var, value_set_of_closures)
  | Wrong | Unresolved _ | Unknown | Unknown_because_of_unresolved_symbol _ ->
    Wrong

type checked_approx_for_closure_allowing_unresolved =
  | Wrong
  | Unresolved of Symbol.t
  | Unknown
  | Unknown_because_of_unresolved_symbol of Symbol.t
  | Ok of value_set_of_closures Closure_id.Map.t * Variable.t option
      * Symbol.t option

let check_approx_for_closure_allowing_unresolved t
      : checked_approx_for_closure_allowing_unresolved =
  match t.descr with
  | Closure value_closure -> begin
    match Closure_id.Map.get_singleton value_closure.potential_closures with
    | None -> begin
      try
        let closures =
          Closure_id.Map.map (fun set_of_closures ->
            match set_of_closures.descr with
            | Set_of_closures value_set_of_closures ->
              value_set_of_closures
            | Unresolved _
            | Closure _ | Union _ | Float _ | Boxed_int _ | Unknown _
            | Bottom | Extern _ | String _ | Float_array _ | Symbol _ ->
              raise Exit)
            value_closure.potential_closures
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
      | Unresolved _
      | Closure _ | Float _ | Boxed_int _ | Unknown _ | Bottom | Extern _
      | String _ | Float_array _ | Symbol _ | Union _ -> Wrong
    end
  | Unknown (Unresolved_symbol symbol) ->
    Unknown_because_of_unresolved_symbol symbol
  | Unresolved symbol -> Unresolved symbol
  | Set_of_closures _ | Union _ | Float _ | Boxed_int _ | Bottom | Extern _
  | String _ | Float_array _ | Symbol _ -> Wrong
  (* CR-soon mshinwell: This should be unwound once the reason for a value
     being unknown can be correctly propagated through the export info. *)
  | Unknown Other -> Unknown

type checked_approx_for_closure =
  | Wrong
  | Ok of value_set_of_closures Closure_id.Map.t
          * Variable.t option * Symbol.t option

let check_approx_for_closure t : checked_approx_for_closure =
  match check_approx_for_closure_allowing_unresolved t with
  | Ok (value_closures, set_of_closures_var, set_of_closures_symbol) ->
    Ok (value_closures, set_of_closures_var, set_of_closures_symbol)
  | Wrong | Unknown | Unresolved _ | Unknown_because_of_unresolved_symbol _ ->
    Wrong

type checked_approx_for_closure_singleton =
  | Wrong
  | Ok of Closure_id.t * Variable.t option
          * Symbol.t option * value_set_of_closures

let check_approx_for_closure_singleton t
  : checked_approx_for_closure_singleton =
  match check_approx_for_closure_allowing_unresolved t with
  | Ok (value_closures, set_of_closures_var, set_of_closures_symbol) -> begin
    match Closure_id.Map.get_singleton value_closures with
    | None -> Wrong
    | Some (closure_id, value_set_of_closures) ->
      Ok (closure_id, set_of_closures_var, set_of_closures_symbol,
          value_set_of_closures)
    end
  | Wrong | Unknown | Unresolved _ | Unknown_because_of_unresolved_symbol _ ->
    Wrong

let approx_for_bound_var value_set_of_closures var =
  try Var_within_closure.Map.find var value_set_of_closures.bound_vars
  with Not_found ->
    Misc.fatal_errorf "The set-of-closures approximation %a@ does not \
        bind the variable %a@.%s@."
      print_value_set_of_closures value_set_of_closures
      Var_within_closure.print var
      (Printexc.raw_backtrace_to_string (Printexc.get_callstack max_int))

let check_approx_for_float t : float option =
  match t.descr with
  | Float f -> f
  | Union _ | Unresolved _ | Unknown _ | String _ | Float_array _ | Bottom
  | Set_of_closures _ | Closure _ | Extern _ | Boxed_int _ | Symbol _ -> None

let float_array_as_constant (t:value_float_array) : float list option =
  match t.contents with
  | Unknown_or_mutable -> None
  | Contents contents ->
    Array.fold_right (fun elt acc ->
        match acc, elt.descr with
        | Some acc, Float (Some f) ->
          Some (f :: acc)
        | None, _
        | Some _,
          (Float None | Unresolved _ | Unknown _ | String _ | Float_array _
            | Bottom | Union _ | Set_of_closures _ | Closure _ | Extern _
            | Boxed_int _ | Symbol _)
          -> None)
      contents (Some [])

let check_approx_for_string t : string option =
  match t.descr with
  | String { contents } -> contents
  | Union _ | Float _ | Unresolved _ | Unknown _ | Float_array _ | Bottom
  | Set_of_closures _ | Closure _ | Extern _ | Boxed_int _ | Symbol _ -> None

type switch_branch_selection =
  | Cannot_be_taken
  | Can_be_taken
  | Must_be_taken

let potentially_taken_const_switch_branch t branch =
  match t.descr with
  | Union union ->
    let must_be_taken =
      match Unionable.flatten union with
      | Bottom -> false
      | Ok (Block _) -> false
      | Ok (Int i) | Ok (Constptr i) -> i = branch
      | Ok (Char c) -> Char.code c = branch
    in
    if must_be_taken then Must_be_taken
    else if Unionable.maybe_is_immediate_value union branch then Can_be_taken
    else Cannot_be_taken
  | Unresolved _ | Unknown _ | Extern _ | Symbol _ ->
    (* In theory symbols cannot contain integers but this shouldn't
       matter as this will always be an imported approximation *)
    Can_be_taken
  | Float _ | Float_array _ | String _ | Closure _ | Set_of_closures _
  | Boxed_int _ | Bottom -> Cannot_be_taken

let potentially_taken_block_switch_branch_tag t tag =
  match t.descr with
  | Union union ->
    let tag = Tag.create_exn tag in
    let must_be_taken =
      match Unionable.flatten union with
      | Bottom -> false
      | Ok (Block (block_tag, _)) -> Tag.equal block_tag tag
      | Ok (Int _ | Char _ | Constptr _) -> false
    in
    if must_be_taken then Must_be_taken
    else if Unionable.maybe_is_block_with_tag union tag then Can_be_taken
    else Cannot_be_taken
  | (Unresolved _ | Unknown _ | Extern _ | Symbol _) -> Can_be_taken
  | Float _ when tag = Obj.double_tag -> Must_be_taken
  | Float_array _ when tag = Obj.double_array_tag -> Must_be_taken
  | String _ when tag = Obj.string_tag -> Must_be_taken
  | (Closure _ | Set_of_closures _)
      when tag = Obj.closure_tag || tag = Obj.infix_tag -> Can_be_taken
  | Boxed_int _ when tag = Obj.custom_tag -> Must_be_taken
  | Float _ | Set_of_closures _ | Closure _ | String _ | Float_array _
  | Boxed_int _ -> Cannot_be_taken | Bottom -> Cannot_be_taken

let potentially_taken_block_switch_branch_string t s =
  match t.descr with
  | Unresolved _ | Unknown _ | Extern _ | Symbol _ -> Can_be_taken
  | String { contents = Some s'; _ } when s = s' -> Must_be_taken
  | String { contents = Some _; _ } -> Cannot_be_taken
  | String { contents = None; } -> Can_be_taken
  | Union union ->
    (* This case seems unlikely, so we don't write the logic to determine
       [Must_be_taken]. *)
    let string_tag = Tag.create_exn Obj.string_tag in
    if Unionable.maybe_is_block_with_tag union string_tag then Can_be_taken
    else Cannot_be_taken
  | Float _ | Set_of_closures _ | Closure _
  | Float_array _ | Boxed_int _ | Bottom -> Cannot_be_taken

let potentially_taken_block_switch_branch t pattern =
  match (pattern : Ilambda.switch_block_pattern) with
  | Tag tag -> potentially_taken_block_switch_branch_tag t tag
  | String s -> potentially_taken_block_switch_branch_string t s
