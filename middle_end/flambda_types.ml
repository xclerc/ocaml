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

module T0 = Flambda_types0

type t =
  (Flambda.function_declarations, Freshening.Project_var.t) Flambda_types0.t

let descr = T0.descr
let descrs = T0.descrs
let create_set_of_closures = T0.create_set_of_closures
let update_freshening_of_set_of_closures =
  T0.update_freshening_of_set_of_closures
let unknown = T0.unknown
let int = T0.int
let char = T0.char
let boxed_float = T0.boxed_float
let any_float = T0.any_float
let any_unboxed_float = T0.any_unboxed_float
let any_unboxed_int32 = T0.any_unboxed_int32
let any_unboxed_int64 = T0.any_unboxed_int64
let any_unboxed_nativeint = T0.any_unboxed_nativeint
let unboxed_float = T0.unboxed_float
let unboxed_int32 = T0.unboxed_int32
let unboxed_int64 = T0.unboxed_int64
let unboxed_nativeint = T0.unboxed_nativeint
let boxed_float = T0.boxed_float
let boxed_int32 = T0.boxed_int32
let boxed_int64 = T0.boxed_int64
let boxed_nativeint = T0.boxed_nativeint
let mutable_float_array = T0.mutable_float_array
let immutable_float_array = T0.immutable_float_array
let string = T0.string
let boxed_int = T0.boxed_int
let constptr = T0.constptr
let block = T0.block
let extern = T0.extern
let symbol = T0.symbol
let bottom = T0.bottom
let unresolved = T0.unresolved
let closure = T0.closure
let set_of_closures = T0.set_of_closures
let make_const_int_named = T0.make_const_int_named
let make_const_char_named = T0.make_const_char_named
let make_const_ptr_named = T0.make_const_ptr_named
let make_const_bool_named = T0.make_const_bool_named
let make_const_float_named = T0.make_const_float_named
let make_const_boxed_int_named = T0.make_const_boxed_int_named
let augment_with_variable = T0.augment_with_variable
let augment_with_symbol = T0.augment_with_symbol
let augment_with_symbol_field = T0.augment_with_symbol_field
let replace_description = T0.replace_description
let augment_with_kind = T0.augment_with_kind
let augment_kind_with_approx = T0.augment_kind_with_approx

let make_const_int_named n : Flambda.named * t =
  Const (Int n), value_int n

let make_const_char_named n : Flambda.named * t =
  Const (Char n), value_char n

let make_const_ptr_named n : Flambda.named * t =
  Const (Const_pointer n), value_constptr n

let make_const_bool_named b : Flambda.named * t =
  make_const_ptr_named (if b then 1 else 0)

let make_const_boxed_float_named f : Flambda.named * t =
  Allocated_const (Float f), boxed_float f

let make_const_boxed_int32_named n : Flambda.named * t =
  Allocated_const (Int32 f), boxed_int32 f

let make_const_boxed_int64_named n : Flambda.named * t =
  Allocated_const (Int64 f), boxed_int64 f

let make_const_boxed_nativeint_named n : Flambda.named * t =
  Allocated_const (Nativeint f), boxed_nativeint f

let make_const_unboxed_float_named f : Flambda.named * t =
  Allocated_const (Float f), unboxed_float f

let make_const_unboxed_int32_named n : Flambda.named * t =
  Allocated_const (Int32 f), unboxed_int32 f

let make_const_unboxed_int64_named n : Flambda.named * t =
  Allocated_const (Int64 f), unboxed_int64 f

let make_const_unboxed_nativeint_named n : Flambda.named * t =
  Allocated_const (Nativeint f), unboxed_nativeint f

type simplification_summary =
  | Nothing_done
  | Replaced_term

type simplification_result_named = Flambda.named * simplification_summary * t

let reconstitute_term t : (Flambda.named * t) option =
  let try_symbol () : (Flambda.named * t) option =
    match t.symbol with
    | Some (sym, None) -> Some (Symbol sym, t)
    | Some (sym, Some field) -> Some (Read_symbol_field (sym, field), t)
    | None -> None
  in
  match t.descr with
  | Union union ->
    begin match Unionable.flatten union with
    | Ok (Block _) | Ill_typed_code | Anything -> try_symbol ()
    | Ok (Int n) -> Some (make_const_int_named n)
    | Ok (Char n) -> Some (make_const_char_named n)
    | Ok (Constptr n) -> Some (make_const_ptr_named n)
    end
  | Boxed_number (Float, { descr = Float fs; _ }) ->
    begin match Float.Set.get_singleton fs with
    | Some f -> Some (make_const_boxed_float_named f)
    | None -> try_symbol ()
    end
  | Boxed_number (Int32, { descr = Int32 ns; _ }) ->
    begin match Int32.Set.get_singleton ns with
    | Some n -> Some (make_const_boxed_int32_named n)
    | None -> try_symbol ()
    end
  | Boxed_number (Int64, { descr = Int64 ns; _ }) ->
    begin match Int64.Set.get_singleton ns with
    | Some n -> Some (make_const_boxed_int64_named n)
    | None -> try_symbol ()
    end
  | Boxed_number (Nativeint, { descr = Nativeint ns; _ }) ->
    begin match Nativeint.Set.get_singleton ns with
    | Some n -> Some (make_const_boxed_nativeint_named n)
    | None -> try_symbol ()
    end
  | Float fs ->
    begin match Float.Set.get_singleton fs with
    | Some f -> Some (make_const_unboxed_float_named f)
    | None -> try_symbol ()
    end
  | Int32 fs ->
    begin match Int32.Set.get_singleton fs with
    | Some f -> Some (make_const_unboxed_int32_named f)
    | None -> try_symbol ()
    end
  | Int64 fs ->
    begin match Int64.Set.get_singleton fs with
    | Some f -> Some (make_const_unboxed_int64_named f)
    | None -> try_symbol ()
    end
  | Nativeint fs ->
    begin match Nativeint.Set.get_singleton fs with
    | Some f -> Some (make_const_unboxed_nativeint_named f)
    | None -> try_symbol ()
    end
  | Symbol sym -> Some (Symbol sym, t)
  | Boxed_number _ | String _ | Float_array _ | Set_of_closures _
  | Closure _ | Unknown _ | Bottom | Extern _ | Unresolved _ -> try_symbol ()

let maybe_replace_term_with_reconstituted_term t (named : Flambda.named)
      : simplification_result_named =
  if Effect_analysis.no_effects_named named then
    match simplify_var t with
    | Some (named, t) ->
      named, Replaced_term, t
    | None ->
      named, Nothing_done, t
  else
    named, Nothing_done, t

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

let is_bottom t =
  match t.descr with
  | Bottom -> true
  | Unresolved _ | Unknown _ | String _ | Float_array _ | Union _
  | Set_of_closures _ | Closure _ | Extern _ | Boxed_number _
  | Float _ | Int32 _ | Int64 _ | Nativeint _ | Symbol _ -> false

let known t =
  match t.descr with
  | Unresolved _ | Unknown _ -> false
  | String _ | Float_array _ | Bottom | Union _ | Set_of_closures _ | Closure _
  | Extern _ | Boxed_number _ | Float _ | Int32 _ | Int64 _ | Nativeint _
  | Symbol _ -> true

let useful t =
  match t.descr with
  | Unresolved _ | Unknown _ | Bottom -> false
  | Union union -> Unionable.useful union
  | String _ | Float_array _ | Set_of_closures _ | Boxed_number _
  | Float _ | Int32 _ | Int64 _ | Nativeint _ | Closure _ | Extern _
  | Symbol _ -> true

let all_not_useful ts = List.for_all (fun t -> not (useful t)) ts

let invalid_to_mutate t =
  match t.descr with
  | Union unionable -> Unionable.invalid_to_mutate unionable
  | String { contents = Some _ } | Set_of_closures _ | Boxed_number _
  | Float _ | Int32 _ | Int64 _ | Nativeint _ | Closure _ -> true
  | String { contents = None } | Float_array _ | Unresolved _ | Unknown _
  | Bottom -> false
  | Extern _ | Symbol _ -> assert false

type get_field_result =
  | Ok of t
  | Unreachable

let get_field t ~field_index:i : get_field_result =
(*
Format.eprintf "get_field %d from %a\n%!" i print t;
*)
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
    | Ok (Int _ | Char _ | Constptr _) ->
      (* Something seriously wrong is happening: either the user is doing
         something exceptionally unsafe, or it is an unreachable branch.
         We consider this as unreachable and mark the result accordingly. *)
      Unreachable
    | Ill_typed_code -> Unreachable
    | Anything -> Ok (value_unknown Other)
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
  | Float _ | Int32 _ | Int64 _ | Nativeint _ | String _ | Boxed_number _ ->
    (* The user is doing something unsafe. *)
    Unreachable
  | Set_of_closures _ | Closure _
    (* This is used by [CamlinternalMod]. *)
  | Symbol _ | Extern _ ->
    (* These should have been resolved. *)
    Ok (value_unknown Other)
  | Unknown reason ->
    Ok (value_unknown reason)
  | Unresolved value ->
    (* We don't know anything, but we must remember that it comes
       from another compilation unit in case it contains a closure. *)
    Ok (value_unknown (Unresolved_value value))

let length_of_array t =
  match t.descr with
  | Union union -> Unionable.size_of_block union
  | Float_array { contents = Contents floats; _ } -> Some (Array.length floats)
  | _ -> None  (* Could be improved later if required. *)

type checked_approx_for_block =
  | Wrong
  | Ok of Tag.Scannable.t * t array

let check_approx_for_block t : checked_approx_for_block =
  match t.descr with
  | Union union ->
    begin match Unionable.flatten union with
    | Ok (Block (tag, fields)) -> Ok (tag, fields)
    | Ok (Int _ | Char _ | Constptr _) | Ill_typed_code | Anything -> Wrong
    end
  | Bottom | Float_array _ | String _ | Boxed_number _ | Float _ | Int32 _
  | Int64 _ | Nativeint _ | Set_of_closures _ | Closure _ | Symbol _ | Extern _
  | Unknown _ | Unresolved _ -> Wrong

type checked_approx_for_block_or_immediate =
  | Wrong
  | Immediate
  | Block

let check_approx_for_block_or_immediate t
      : checked_approx_for_block_or_immediate =
  match t.descr with
  | Union union ->
    begin match Unionable.flatten union with
    | Ill_typed_code | Anything -> Wrong
    | Ok (Block _) -> Block
    | Ok (Int _ | Char _ | Constptr _) -> Immediate
    end
  | Bottom | Float_array _ | String _ | Boxed_number _ | Float _ | Int32 _
  | Int64 _ | Nativeint _ | | Set_of_closures _ | Closure _ | Symbol _
  | Extern _ | Unknown _ | Unresolved _ -> Wrong

type checked_approx_for_variant =
  | Wrong
  | Ok of Unionable.t

let check_approx_for_variant t : checked_approx_for_variant =
  match t.descr with
  | Union union ->
    if Unionable.ok_for_variant union then Ok union
    else Wrong
  | Bottom | Float_array _ | String _ | Boxed_number _ | Float _ | Int32 _
  | Int64 _ | Nativeint _ | Set_of_closures _ | Closure _ | Symbol _ | Extern _
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
  | Unresolved of unresolved_value
  | Unknown
  | Unknown_because_of_unresolved_value of unresolved_value
  | Ok of Variable.t option * value_set_of_closures

let check_approx_for_set_of_closures t : checked_approx_for_set_of_closures =
  match t.descr with
  | Unresolved value -> Unresolved value
  | Unknown (Unresolved_value value) ->
    Unknown_because_of_unresolved_value value
  | Set_of_closures value_set_of_closures ->
    (* Note that [var] might be [None]; we might be reaching the set of
       closures via approximations only, with the variable originally bound
       to the set now out of scope. *)
    Ok (t.var, value_set_of_closures)
  | Closure _ | Union _ | Boxed_number _ | Float _ | Int32 _ | Int64 _
  | Nativeint _ | Unknown _ | Bottom
  | Extern _ | String _ | Float_array _ | Symbol _ -> Wrong

type strict_checked_approx_for_set_of_closures =
  | Wrong
  | Ok of Variable.t option * value_set_of_closures

let strict_check_approx_for_set_of_closures t
      : strict_checked_approx_for_set_of_closures =
  match check_approx_for_set_of_closures t with
  | Ok (var, value_set_of_closures) -> Ok (var, value_set_of_closures)
  | Wrong | Unresolved _ | Unknown | Unknown_because_of_unresolved_value _ ->
    Wrong

type checked_approx_for_closure_allowing_unresolved =
  | Wrong
  | Unresolved of unresolved_value
  | Unknown
  | Unknown_because_of_unresolved_value of unresolved_value
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
            | Closure _ | Union _ | Boxed_number _ | Float _ | Int32 _
            | Int64 _ | Nativeint _ | Unknown _
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
      | Closure _ | Boxed_number _ | Float _ | Int32 _ | Int64 _
      | Nativeint _ | Unknown _ | Bottom | Extern _
      | String _ | Float_array _ | Symbol _ | Union _ -> Wrong
    end
  | Unknown (Unresolved_value value) ->
    Unknown_because_of_unresolved_value value
  | Unresolved value -> Unresolved value
  | Set_of_closures _ | Union _ | Boxed_number _
  | Float _ | Int32 _ | Int64 _ | Nativeint _ | Bottom | Extern _
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
  | Wrong | Unknown | Unresolved _ | Unknown_because_of_unresolved_value _ ->
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
  | Wrong | Unknown | Unresolved _ | Unknown_because_of_unresolved_value _ ->
    Wrong

let approx_for_bound_var value_set_of_closures var =
  try Var_within_closure.Map.find var value_set_of_closures.bound_vars
  with Not_found ->
    Misc.fatal_errorf "The set-of-closures approximation %a@ does not \
        bind the variable %a@.%s@."
      print_value_set_of_closures value_set_of_closures
      Var_within_closure.print var
      (Printexc.raw_backtrace_to_string (Printexc.get_callstack max_int))

let check_approx_for_int t : int option =
  match t.descr with
  | Union unionable -> Unionable.as_int unionable
  | Boxed_number _ | Float _ | Int32 _ | Int64 _ | Nativeint _ | Unresolved _
  | Unknown _ | String _ | Float_array _ | Bottom | Set_of_closures _
  | Closure _ | Extern _ | Boxed_number _ | Symbol _ -> None

let check_approx_for_float t : float option =
  match t.descr with
  | Boxed_number f -> f
  | Union _ | Unresolved _ | Unknown _ | String _ | Float_array _ | Bottom
  | Set_of_closures _ | Closure _ | Extern _ | Boxed_number _ | Symbol _
  | Float _ | Int32 _ | Int64 _ | Nativeint _ -> None

let float_array_as_constant (t:value_float_array) : float list option =
  match t.contents with
  | Unknown_or_mutable -> None
  | Contents contents ->
    Array.fold_right (fun elt acc ->
        match acc, elt.descr with
        | Some acc, Boxed_float (Some f) ->
          Some (f :: acc)
        | None, _
        | Some _,
          (Boxed_float None | Unresolved _ | Unknown _ | String _ | Float_array _
            | Bottom | Union _ | Set_of_closures _ | Closure _ | Extern _
            | Boxed_int _ | Symbol _)
          -> None)
      contents (Some [])

let check_approx_for_string t : string option =
  match t.descr with
  | String { contents } -> contents
  | Union _ | Boxed_number _ | Float _ | Int32 _ | Int64 _ | Nativeint
  | Unresolved _ | Unknown _ | Float_array _ | Bottom | Set_of_closures _
  | Closure _ | Extern _ | Boxed_int _ | Symbol _ -> None

type switch_branch_selection =
  | Cannot_be_taken
  | Can_be_taken
  | Must_be_taken

let potentially_taken_const_switch_branch t branch =
  match t.descr with
  | Union union ->
    let must_be_taken =
      match Unionable.flatten union with
      | Ill_typed_code | Anything -> false
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
  | Boxed_number _ | Float_array _ | String _ | Closure _ | Set_of_closures _
  | Float | Int32 | Int64 | Nativeint | Bottom -> Cannot_be_taken

let physically_same_values (approxs:t list) =
  match approxs with
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

let is_known_to_be_some_kind_of_int (arg:descr) =
  match arg with
  | Union (Immediates _) -> true
  | Union (Blocks _ | Blocks_and_immediates _) | Boxed_number _
  | Float | Int32 | Int64 | Nativeint | Set_of_closures _
  | Closure _ | String _ | Float_array _
  | Boxed_int _ | Unknown _ | Extern _
  | Symbol _ | Unresolved _ | Bottom -> false

(* CR mshinwell: make name more precise.  Is this only for blocks with
   tag < No_scan_tag? *)
let is_known_to_be_some_kind_of_block (arg:descr) =
  match arg with
  | Union (Blocks _) | Boxed_number _ | Float_array _
  | Closure _ | String _ -> true
  | Set_of_closures _ | Union (Blocks_and_immediates _ | Immediates _)
  | Unknown _ | Float _ | Int32 _ | Int64 _ | Nativeint _ | Extern _ | Symbol _
  | Unresolved _ | Bottom -> false

let rec structurally_different (arg1:t) (arg2:t) =
  let module Int = Numbers.Int in
  let module Immediate = Unionable.Immediate in
  let immediates_structurally_different s1 s2 union1 union2 =
    Unionable.invariant union1;
    Unionable.invariant union2;
    (* The frontend isn't precise about "int" and "const pointer", for
       example generating "(!= b/1006 0)" for a match against a bool, which
       is a "const pointer".  The same presumably might happen with "char".
       As such for "structurally different" purposes we treat immediates whose
       runtime representations are the same as equal. *)
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
  match arg1.descr, arg2.descr with
  | Union ((Immediates s1) as union1), Union ((Immediates s2) as union2)
    when immediates_structurally_different s1 s2 union1 union2 -> true
  | Union (Blocks b1), Union (Blocks b2)
    when Tag.Scannable.Map.cardinal b1 = 1
      && Tag.Scannable.Map.cardinal b2 = 1 ->
    let tag1, fields1 = Tag.Scannable.Map.min_binding b1 in
    let tag2, fields2 = Tag.Scannable.Map.min_binding b2 in
    not (Tag.Scannable.equal tag1 tag2)
    || (Array.length fields1 <> Array.length fields2)
    || Misc.Stdlib.Array.exists2 structurally_different fields1 fields2
  | descr1, descr2 ->
    (* This is not very precise as this won't allow to distinguish
       blocks from strings for instance. This can be improved if it
       is deemed valuable. *)
    (is_known_to_be_some_kind_of_int descr1
     && is_known_to_be_some_kind_of_block descr2)
    || (is_known_to_be_some_kind_of_block descr1
        && is_known_to_be_some_kind_of_int descr2)

let physically_different_values (approxs:t list) =
  match approxs with
  | [] | [_] | _ :: _ :: _ :: _ ->
    Misc.fatal_error "wrong number of arguments for equality"
  | [a1; a2] ->
    structurally_different a1 a2
