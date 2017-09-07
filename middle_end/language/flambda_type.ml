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
module Nativeint = Numbers.Nativeint

include F0.Flambda_type

let var (t : t) = t.var
let projection (t : t) = t.projection
let symbol (t : t) = t.symbol
let descr (t : t) = t.descr
let descrs ts = List.map (fun (t : t) -> t.descr) ts

(* CR mshinwell: Shouldn't this just use [Flambda_kind].lambda_value_kind? *)
let refine_value_kind t (kind : Lambda.value_kind) : Lambda.value_kind =
  match descr t with
  | Boxed_number (Float, { descr = Unboxed_float _; _ }) -> Pfloatval
  | Boxed_number (Int32, { descr = Unboxed_int32 _; _ }) -> Pboxedintval Pint32
  | Boxed_number (Int64, { descr = Unboxed_int64 _; _ }) -> Pboxedintval Pint64
  | Boxed_number (Nativeint, { descr = Unboxed_nativeint _; _ }) ->
    Pboxedintval Pnativeint
  | Union union ->
    begin match Unionable.flatten union with
    | Ok (Int _) -> Pintval
    | _ -> kind
    end
  | _ -> kind

let rename_variables t ~f =
  clean t (fun var -> Available_different_name (f var))

let unresolved_symbol sym =
  (* CR mshinwell: check with Pierre about this comment *)
  (* We don't know anything, but we must remember that it comes
     from another compilation unit in case it contains a closure. *)
  unknown (Flambda_kind.value ()) (Unresolved_value (Symbol sym))

let make_const_int_named n : Named.t * t =
  Const (Int n), int n

let make_const_char_named n : Named.t * t =
  Const (Char n), char n

let make_const_ptr_named n : Named.t * t =
  Const (Const_pointer n), constptr n

let make_const_bool_named b : Named.t * t =
  make_const_ptr_named (if b then 1 else 0)

let make_const_boxed_float_named f : Named.t * t =
  Allocated_const (Float f), boxed_float f

let make_const_boxed_int32_named n : Named.t * t =
  Allocated_const (Int32 n), boxed_int32 n

let make_const_boxed_int64_named n : Named.t * t =
  Allocated_const (Int64 n), boxed_int64 n

let make_const_boxed_nativeint_named n : Named.t * t =
  Allocated_const (Nativeint n), boxed_nativeint n

let make_const_unboxed_float_named f : Named.t * t =
  Const (Unboxed_float f), unboxed_float f

let make_const_unboxed_int32_named n : Named.t * t =
  Const (Unboxed_int32 n), unboxed_int32 n

let make_const_unboxed_int64_named n : Named.t * t =
  Const (Unboxed_int64 n), unboxed_int64 n

let make_const_unboxed_nativeint_named n : Named.t * t =
  Const (Unboxed_nativeint n), unboxed_nativeint n

let is_bottom t =
  match descr t with
  | Bottom -> true
  | Unknown _ | Immutable_string _ | Mutable_string _ | Float_array _
  | Union _ | Set_of_closures _ | Closure _ | Load_lazily _ | Boxed_number _
  | Unboxed_float _ | Unboxed_int32 _ | Unboxed_int64 _
  | Unboxed_nativeint _ -> false

let known t =
  match descr t with
  | Unknown _ -> false
  | Bottom | Immutable_string _ | Mutable_string _ | Float_array _
  | Union _ | Set_of_closures _ | Closure _ | Load_lazily _ | Boxed_number _
  | Unboxed_float _ | Unboxed_int32 _ | Unboxed_int64 _
  | Unboxed_nativeint _ -> true

let useful t =
  match descr t with
  | Unknown _ | Bottom -> false
  | Union union -> Unionable.useful union
  | Immutable_string _ | Mutable_string _ | Float_array _
  | Set_of_closures _ | Closure _ | Load_lazily _ | Boxed_number _
  | Unboxed_float _ | Unboxed_int32 _ | Unboxed_int64 _
  | Unboxed_nativeint _ -> true

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

let all_not_useful ts = List.for_all (fun t -> not (useful t)) ts

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
  | Unreachable

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
        Unreachable
      end
    | Ok (Int _ | Char _ | Constptr _) ->
      (* Something seriously wrong is happening: either the user is doing
         something exceptionally unsafe, or it is an unreachable branch.
         We consider this as unreachable and mark the result accordingly. *)
      Unreachable
    | Bottom -> Unreachable
    | Unknown -> Ok (unknown (Flambda_kind.value ()) Other)
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
    Ok (unknown (Flambda_kind.value ()) Other)
  | Unboxed_float _ | Unboxed_int32 _ | Unboxed_int64 _ | Unboxed_nativeint _
  | Immutable_string _ | Mutable_string _ | Boxed_number _ ->
    (* The user is doing something unsafe. *)
    Unreachable
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

let follow_variable_equality t ~is_present_in_env =
  match var t with
  | Some var when is_present_in_env var -> Some var
  | _ -> None

let reify t : Named.t option =
  let try_symbol () =
    match symbol t with
    | Some (sym, None) -> Some (Named.Symbol sym)
    | Some (sym, Some field) -> Some (Named.Read_symbol_field (sym, field))
    | None -> None
  in
  match descr t with
  | Union union ->
    begin match Unionable.flatten union with
    | Ok (Block _) | Bottom | Unknown -> try_symbol ()
    | Ok (Int n) -> Some (fst (make_const_int_named n))
    | Ok (Char n) -> Some (fst (make_const_char_named n))
    | Ok (Constptr n) -> Some (fst (make_const_ptr_named n))
    end
  | Boxed_number (Float, { descr = Unboxed_float fs; _ }) ->
    begin match Float.Set.get_singleton fs with
    | Some f -> Some (fst (make_const_boxed_float_named f))
    | None -> try_symbol ()
    end
  | Boxed_number (Int32, { descr = Unboxed_int32 ns; _ }) ->
    begin match Int32.Set.get_singleton ns with
    | Some n -> Some (fst (make_const_boxed_int32_named n))
    | None -> try_symbol ()
    end
  | Boxed_number (Int64, { descr = Unboxed_int64 ns; _ }) ->
    begin match Int64.Set.get_singleton ns with
    | Some n -> Some (fst (make_const_boxed_int64_named n))
    | None -> try_symbol ()
    end
  | Boxed_number (Nativeint, { descr = Unboxed_nativeint ns; _ }) ->
    begin match Nativeint.Set.get_singleton ns with
    | Some n -> Some (fst (make_const_boxed_nativeint_named n))
    | None -> try_symbol ()
    end
  | Unboxed_float fs ->
    begin match Float.Set.get_singleton fs with
    | Some f -> Some (fst (make_const_unboxed_float_named f))
    | None -> try_symbol ()
    end
  | Unboxed_int32 fs ->
    begin match Int32.Set.get_singleton fs with
    | Some f -> Some (fst (make_const_unboxed_int32_named f))
    | None -> try_symbol ()
    end
  | Unboxed_int64 fs ->
    begin match Int64.Set.get_singleton fs with
    | Some f -> Some (fst (make_const_unboxed_int64_named f))
    | None -> try_symbol ()
    end
  | Unboxed_nativeint fs ->
    begin match Nativeint.Set.get_singleton fs with
    | Some f -> Some (fst (make_const_unboxed_nativeint_named f))
    | None -> try_symbol ()
    end
  | Boxed_number _ | Immutable_string _ | Mutable_string _ | Float_array _
  | Set_of_closures _ | Closure _ | Unknown _ | Bottom | Load_lazily _ ->
    try_symbol ()

let reify_using_env t ~is_present_in_env =
  let named =
    match var t with
    | Some var when is_present_in_env var -> Some (Named.Var var)
    | _ ->
      match symbol t with
      | Some (sym, None) -> Some (Named.Symbol sym)
      | Some (sym, Some field) -> Some (Named.Read_symbol_field (sym, field))
      | None -> None
  in
  match reify t with
  | None -> named
  | Some named -> Some named

let reify_as_int t : int option =
  match descr t with
  | Union unionable -> Unionable.as_int unionable
  | Boxed_number _ | Unboxed_float _ | Unboxed_int32 _ | Unboxed_int64 _
  | Unboxed_nativeint _ | Unknown _ | Immutable_string _ | Mutable_string _
  | Float_array _ | Bottom | Set_of_closures _ | Closure _ | Load_lazily _ ->
    None

let reify_as_boxed_float t : float option =
  match descr t with
  | Boxed_number (Float, t) ->
    begin match descr t with
    | Unboxed_float fs -> Float.Set.get_singleton fs
    | _ -> None
    end
  | Union _ | Unknown _ | Immutable_string _ | Mutable_string _
  | Float_array _ | Bottom | Set_of_closures _ | Closure _ | Load_lazily _
  | Boxed_number _ | Unboxed_float _ | Unboxed_int32 _ | Unboxed_int64 _
  | Unboxed_nativeint _ -> None

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

type reified_as_scannable_block =
  | Wrong
  | Ok of Tag.Scannable.t * t array

let reify_as_scannable_block t : reified_as_scannable_block =
  match descr t with
  | Union union ->
    begin match Unionable.flatten union with
    | Ok (Block (tag, fields)) -> Ok (tag, fields)
    | Ok (Int _ | Char _ | Constptr _) | Bottom | Unknown -> Wrong
    end
  | Bottom | Float_array _ | Immutable_string _ | Mutable_string _
  | Boxed_number _ | Unboxed_float _ | Unboxed_int32 _ | Unboxed_int64 _
  | Unboxed_nativeint _ | Set_of_closures _ | Closure _  | Load_lazily _
  | Unknown _ -> Wrong

type blocks = t array Tag.Scannable.Map.t
type immediates = Unionable.Immediate.Set.t

type reified_as_variant =
  | Wrong
  | Blocks of blocks
  | Blocks_and_immediates of blocks * immediates
  | Immediates of immediates

(* XXX do we want to return "unknown" cases too, giving the variable? *)
let reify_as_variant t : reified_as_variant =
  match descr t with
  | Union union ->
    begin match union with
    | Blocks blocks -> Blocks blocks
    | Blocks_and_immediates (blocks, imms) ->
      Blocks_and_immediates (blocks, imms)
    end
  | Boxed_or_encoded_number (Encoded Tagged_int, numbers) ->
    begin match descr numbers with
    | Naked_number (Int, imms) ->
      Immediates (Union.Immediate.Set.of_int_set imms)
    | Naked_number (Char, imms) ->
      Immediates (Union.Immediate.Set.of_char_set imms)
    | Naked_number (Constptr, imms) ->
      Immediates (Union.Immediate.Set.of_constptr_set imms)
    | Union _ | Boxed_or_encoded_number _ | Bottom | Float_array _
    | Immutable_string _ | Mutable_string _ | Set_of_closures _ | Closure _
    | Load_lazily _ | Unknown _ -> Wrong
    end
  | Boxed_or_encoded_number _ | Bottom | Float_array _ | Immutable_string _
  | Mutable_string _ | Naked_number _ | Set_of_closures _ | Closure _
  | Load_lazily _ | Unknown _ -> Wrong

type reified_as_scannable_block_or_immediate =
  | Wrong
  | Immediate
  | Scannable_block

let reify_as_scannable_block_or_immediate t
      : reified_as_scannable_block_or_immediate =
  match descr t with
  | Union union ->
    begin match Unionable.flatten union with
    | Bottom | Unknown -> Wrong
    | Ok (Block _) -> Scannable_block
    | Ok (Int _ | Char _ | Constptr _) -> Immediate
    end
  | Bottom | Float_array _ | Immutable_string _ | Mutable_string _
  | Boxed_number _ | Unboxed_float _ | Unboxed_int32 _ | Unboxed_int64 _
  | Unboxed_nativeint _ | Set_of_closures _ | Closure _ | Load_lazily _
  | Unknown _ -> Wrong

type reified_as_set_of_closures =
  | Wrong
  | Unresolved of unresolved_value
  | Unknown
  | Ok of Variable.t option * set_of_closures

let reify_as_set_of_closures t : reified_as_set_of_closures =
  match descr t with
  | Unknown (_, Unresolved_value reason) -> Unresolved reason
  | Set_of_closures value_set_of_closures ->
    (* Note that [var] might be [None]; we might be reaching the set of
       closures via Flambda types only, with the variable originally bound
       to the set now out of scope. *)
    Ok (var t, value_set_of_closures)
  | Closure _ | Union _ | Boxed_number _ | Unboxed_float _
  | Unboxed_int32 _ | Unboxed_int64 _ | Unboxed_nativeint _
  | Unknown _ | Bottom | Load_lazily _ | Immutable_string _
  | Mutable_string _ | Float_array _  -> Wrong

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
