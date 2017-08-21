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
  (Flambda.Function_declarations.t, Freshening.Project_var.t) Flambda_types0.t

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
let augment_kind_with_type = T0.augment_kind_with_type

let free_variables (t : t) =
  let rec free_variables (t : t) acc =
    let acc =
      match t.var with
      | None -> acc
      | Some var -> Variable.Set.add var acc
    in
    match t.descr with
    | Union unionable ->
      begin match unionable with
      | Blocks blocks
      | Blocks_and_immediates (blocks, _) ->
        Tag.Scannable.Map.fold (fun _tag t acc -> free_variables t acc)
          blocks acc
      | Immediates _ -> acc
      end
    | Unknown _
    | Unboxed_float _
    | Unboxed_int32 _
    | Unboxed_int64 _
    | Unboxed_nativeint _ -> acc
    | Boxed_number (_, t) -> free_variables t acc
    | Set_of_closures set_of_closures ->
      Var_within_closure.Map.fold (fun _var t acc -> free_variables t acc)
        set_of_closures.bound_vars
    | Closure { potential_closures; } ->
      Closure_id.Map.fold (fun _closure_id t acc -> free_variables t acc)
        potential_closures
    | Immutable_string _
    | Mutable_string _ -> acc
    | Float_array { contents; size = _; } ->
      begin match contents with
      | Contents ts -> Array.fold_left (fun acc t -> free_variables t acc) ts
      | Unknown_or_mutable -> acc
      end
    | Bottom
    | Load_lazily _ -> acc
  in
  free_variables t Variable.Set.empty

let kind_exn t =
  let really_import_approx t =
    let dummy_print_decls ppf _ =
      Format.fprintf ppf "<function declarations>"
    in
    Misc.fatal_errorf "With_free_variables.create_let_reusing_body: \
        Flambda type is not fully resolved: %a"
      (print dummy_print_decls) t
  in
  kind t ~really_import_approx

let refine_value_kind t (kind : Lambda.value_kind) : Lambda.value_kind =
  match t.descr with
  | Boxed_number (Float, { descr = Float _; _ }) -> Pfloatval
  | Boxed_number (Int32, { descr = Int32 _; _ }) -> Pboxedintval Pint32
  | Boxed_number (Int64, { descr = Int64 _; _ }) -> Pboxedintval Pint64
  | Boxed_number (Nativeint, { descr = Nativeint _; _ }) ->
    Pboxedintval Pnativeint
  | Union union ->
    begin match Unionable.flatten union with
    | Ok (Int _) -> Pintval
    | _ -> kind
    end
  | _ -> kind

let unresolved_symbol sym =
  (* CR mshinwell: check with Pierre about this comment *)
  (* We don't know anything, but we must remember that it comes
     from another compilation unit in case it contains a closure. *)
  unknown Value (Unresolved_value (Symbol sym))

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
  Const (Unboxed_float f), unboxed_float f

let make_const_unboxed_int32_named n : Flambda.named * t =
  Const (Unboxed_int32 n), unboxed_int32 f

let make_const_unboxed_int64_named n : Flambda.named * t =
  Const (Unboxed_int64 n), unboxed_int64 f

let make_const_unboxed_nativeint_named n : Flambda.named * t =
  Const (Unboxed_nativeint n), unboxed_nativeint f

let is_bottom t =
  match t.descr with
  | Bottom -> true
  | Unresolved _ | Unknown _ | String _ | Float_array _ | Union _
  | Set_of_closures _ | Closure _ | Load_lazily _ | Boxed_number _
  | Float _ | Int32 _ | Int64 _ | Nativeint _ -> false

let known t =
  match t.descr with
  | Unresolved _ | Unknown _ -> false
  | String _ | Float_array _ | Bottom | Union _ | Set_of_closures _ | Closure _
  | Load_lazily _ | Boxed_number _ | Float _ | Int32 _ | Int64 _
  | Nativeint _ -> true

let useful t =
  match t.descr with
  | Unresolved _ | Unknown _ | Bottom -> false
  | Union union -> Unionable.useful union
  | String _ | Float_array _ | Set_of_closures _ | Boxed_number _
  | Float _ | Int32 _ | Int64 _ | Nativeint _ | Closure _ | Load_lazily _ -> true

let all_not_useful ts = List.for_all (fun t -> not (useful t)) ts

let invalid_to_mutate t =
  match t.descr with
  | Union unionable -> Unionable.invalid_to_mutate unionable
  | String { contents = Some _ } | Set_of_closures _ | Boxed_number _
  | Float _ | Int32 _ | Int64 _ | Nativeint _ | Closure _ -> true
  | String { contents = None } | Float_array _ | Unresolved _ | Unknown _
  | Bottom -> false
  | Load_lazily _ -> assert false

let type_for_bound_var value_set_of_closures var =
  try Var_within_closure.Map.find var value_set_of_closures.bound_vars
  with Not_found ->
    Misc.fatal_errorf "The set-of-closures type %a@ does not \
        bind the variable %a@.%s@."
      print_value_set_of_closures value_set_of_closures
      Var_within_closure.print var
      (Printexc.raw_backtrace_to_string (Printexc.get_callstack max_int))

(* Given a set-of-closures type and a closure ID, apply any
   freshening specified in the type to the closure ID, and return
   that new closure ID.  A fatal error is produced if the new closure ID
   does not correspond to a function declaration in the given type. *)
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
          let fields1 = Tag.Scannable.Map.find tag tags1 in
          let fields2 = Tag.Scannable.Map.find tag tags2 in
          Array.length fields1 <> Array.length fields2
            || Misc.Stdlib.Array.exists2 definitely_different fields1 fields2)
    in
    match arg1.descr, arg2.descr with
    | Unknown _, _ | _, Unknown _
    (* CR mshinwell: Should [Load_lazily] be an error here?  What about for the
       reification functions below?  [invalid_to_mutate] above has an
       assertion failure for this. *)
    | Load_lazily _, _ | _, Load_lazily
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
    | String s1, String s2 -> String.compare s1 s2 <> 0
    | String _, _ | _, String -> true
    | Float_array { contents = contents1; size = size1; },
      Float_array { contents = contents2; size = size2; } ->
      size1 <> size2
        || begin match contents1, contents2 with
           | Contents ts1, Contents ts2 ->
             Array.exists definitely_different ts1 ts2
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
    (* These are used by [CamlinternalMod]. *)
  | Load_lazily _ ->
    (* These should have been resolved. *)
    (* CR mshinwell: Shouldn't this propagate the reason into
       the [Unknown] (which would require extending [unresolved_value] to
       have an [Export_id.t] case)?   (Also see comment above about
       what should happen in this [Load_lazily] case.) *)
    Ok (value_unknown Other)
  | Unknown reason ->
    Ok (value_unknown reason)

let length_of_array t =
  match t.descr with
  | Union union -> Unionable.size_of_block union
  | Float_array { contents = Contents floats; _ } -> Some (Array.length floats)
  | _ -> None  (* Could be improved later if required. *)

let follow_variable_equality t ~is_present_in_env =
  match t.var with
  | Some var when is_present_in_env var -> Some var
  | _ -> None

type cleaning_spec =
  | Available
  | Available_different_name of Variable.t
  | Unavailable

let rec clean t classify =
  let clean_var var_opt =
    match var_opt with
    | None -> None
    | Some var ->
      match classify var with
      | Available -> var_opt
      | Available_different_name new_var -> Some new_var
      | Unavailable -> None
  in
  let t = { t with var = clean_var var; } in
  match t.descr with
  | Union unionable ->
    let clean_blocks blocks =
      Tag.Scannable.Map.map (fun t -> clean t classify) blocks
    in
    let unionable =
      match unionable with
      | Blocks blocks -> Blocks (clean_blocks blocks)
      | Blocks_and_immediates (blocks, imms) ->
        Blocks_and_immediates (clean_blocks blocks, imms)
      | Immediates _ -> unionable
    in
    { t with descr = Union unionable; }
  | Unknown _
  | Unboxed_float _
  | Unboxed_int32 _
  | Unboxed_int64 _
  | Unboxed_nativeint _ -> t
  | Boxed_number (kind, contents) ->
    { t with descr = Boxed_number (kind, clean contents classify); }
  | Set_of_closures set_of_closures ->
    let bound_vars =
      Var_within_closure.Map.map (fun t -> clean t classify)
        set_of_closures.bound_vars
    in
    { t with descr = Set_of_closures { set_of_closures with bound_vars; }; }
  | Closure closure ->
    let potential_closures =
      Closure_id.Map.map (fun t -> clean t classify) closure.potential_closures
    in
    { t with descr = Closure { potential_closures; }; }
  | Immutable_string _
  | Mutable_string _
  | Float_array { contents; size; } ->
    let contents =
      match contents with
      | Contents ts -> Contents (Array.map (fun t -> clean t classify) ts)
      | Unknown_or_mutable -> Unknown_or_mutable
    in
    Float_array { contents; size; }
  | Bottom
  | Load_lazily _ -> acc

module Reification_summary = struct
  type t =
    | Nothing_done
    | Replaced_term

  let join t ~replaced_by_var_or_symbol =
    match replaced_by_var_or_symbol, t with
    | true, Nothing_done
    | true, Replaced_term
    | false, Replaced_term -> Replaced_term
    | false, Nothing_done -> Nothing_done
end

type reification_result = Flambda.named * reification_summary * t

let reify t : (Flambda.named * t) option =
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
  | Unboxed_float fs ->
    begin match Float.Set.get_singleton fs with
    | Some f -> Some (make_const_unboxed_float_named f)
    | None -> try_symbol ()
    end
  | Unboxed_int32 fs ->
    begin match Int32.Set.get_singleton fs with
    | Some f -> Some (make_const_unboxed_int32_named f)
    | None -> try_symbol ()
    end
  | Unboxed_int64 fs ->
    begin match Int64.Set.get_singleton fs with
    | Some f -> Some (make_const_unboxed_int64_named f)
    | None -> try_symbol ()
    end
  | Unboxed_nativeint fs ->
    begin match Nativeint.Set.get_singleton fs with
    | Some f -> Some (make_const_unboxed_nativeint_named f)
    | None -> try_symbol ()
    end
  | Symbol sym -> Some (Symbol sym, t)
  | Boxed_number _ | String _ | Float_array _ | Set_of_closures _
  | Closure _ | Unknown _ | Bottom | Load_lazily _ | Unresolved _ -> try_symbol ()

let maybe_replace_term_with_reified_term t (named : Flambda.named)
      : reification_result =
  if Effect_analysis.no_effects_named named then
    match reify t with
    | Some (named, t) ->
      named, Replaced_term, t
    | None ->
      named, Nothing_done, t
  else
    named, Nothing_done, t

let maybe_replace_term_with_reified_term_using_env t ~is_present_in_env named =
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
  let const, summary, ty = simplify_named t named in
  const, Reification_summary.join summary ~replaced_by_var_or_symbol, ty

let reify_as_int t : int option =
  match t.descr with
  | Union unionable -> Unionable.as_int unionable
  | Boxed_number _ | Float _ | Int32 _ | Int64 _ | Nativeint _ | Unresolved _
  | Unknown _ | String _ | Float_array _ | Bottom | Set_of_closures _
  | Closure _ | Load_lazily _ | Boxed_number _ -> None

let reify_as_boxed_float t : float option =
  match t.descr with
  | Boxed_number f -> f
  | Union _ | Unresolved _ | Unknown _ | String _ | Float_array _ | Bottom
  | Set_of_closures _ | Closure _ | Load_lazily _ | Boxed_number _
  | Float _ | Int32 _ | Int64 _ | Nativeint _ -> None

let reify_as_constant_float_array (t:value_float_array) : float list option =
  match t.contents with
  | Unknown_or_mutable -> None
  | Contents contents ->
    Array.fold_right (fun elt acc ->
        match acc, elt.descr with
        | Some acc, Boxed_float (Some f) ->
          Some (f :: acc)
        | None, _
        | Some _,
          (Boxed_float None | Unresolved _ | Unknown _ | String _
            | Float_array _
            | Bottom | Union _ | Set_of_closures _ | Closure _ | Load_lazily _)
          -> None)
      contents (Some [])

let reify_as_string t : string option =
  match t.descr with
  | String { contents } -> contents
  | Union _ | Boxed_number _ | Float _ | Int32 _ | Int64 _ | Nativeint
  | Unresolved _ | Unknown _ | Float_array _ | Bottom | Set_of_closures _
  | Closure _ | Load_lazily _ -> None

type reified_as_scannable_block =
  | Wrong
  | Ok of Tag.Scannable.t * t array

let reify_as_scannable_block t : reified_as_scannable_block =
  match t.descr with
  | Union union ->
    begin match Unionable.flatten union with
    | Ok (Block (tag, fields)) -> Ok (tag, fields)
    | Ok (Int _ | Char _ | Constptr _) | Ill_typed_code | Anything -> Wrong
    end
  | Bottom | Float_array _ | String _ | Boxed_number _ | Float _ | Int32 _
  | Int64 _ | Nativeint _ | Set_of_closures _ | Closure _  | Load_lazily _
  | Unknown _ | Unresolved _ -> Wrong

type reified_as_variant =
  | Wrong
  | Ok of Unionable.t

let reify_as_variant t : reified_as_variant =
  match t.descr with
  | Union union ->
    if Unionable.ok_for_variant union then Ok union
    else Wrong
  | Bottom | Float_array _ | String _ | Boxed_number _ | Float _ | Int32 _
  | Int64 _ | Nativeint _ | Set_of_closures _ | Closure _  | Load_lazily _
  | Unknown _ | Unresolved _ -> Wrong

type reified_as_scannable_block_or_immediate =
  | Wrong
  | Immediate
  | Block

let reify_as_scannable_block_or_immediate t
      : reified_as_scannable_block_or_immediate =
  match t.descr with
  | Union union ->
    begin match Unionable.flatten union with
    | Ill_typed_code | Anything -> Wrong
    | Ok (Block _) -> Block
    | Ok (Int _ | Char _ | Constptr _) -> Immediate
    end
  | Bottom | Float_array _ | String _ | Boxed_number _ | Float _ | Int32 _
  | Int64 _ | Nativeint _ | Set_of_closures _ | Closure _ 
  | Load_lazily _ | Unknown _ | Unresolved _ -> Wrong

type reified_as_set_of_closures =
  | Wrong
  | Unresolved of unresolved_value
  | Unknown
  | Unknown_because_of_unresolved_value of unresolved_value
  | Ok of Variable.t option * value_set_of_closures

let reify_as_set_of_closures t : reified_as_set_of_closures =
  match t.descr with
  | Unresolved value -> Unresolved value
  | Unknown (Unresolved_value value) ->
    Unknown_because_of_unresolved_value value
  | Set_of_closures value_set_of_closures ->
    (* Note that [var] might be [None]; we might be reaching the set of
       closures via Flambda types only, with the variable originally bound
       to the set now out of scope. *)
    Ok (t.var, value_set_of_closures)
  | Closure _ | Union _ | Boxed_number _ | Float _ | Int32 _ | Int64 _
  | Nativeint _ | Unknown _ | Bottom
  | Load_lazily _ | String _ | Float_array _  -> Wrong

type strict_reified_as_set_of_closures =
  | Wrong
  | Ok of Variable.t option * value_set_of_closures

let strict_reify_as_set_of_closures t
      : strict_reified_as_set_of_closures =
  match reify_as_set_of_closures t with
  | Ok (var, value_set_of_closures) -> Ok (var, value_set_of_closures)
  | Wrong | Unresolved _ | Unknown | Unknown_because_of_unresolved_value _ ->
    Wrong

type strict_reified_as_closure =
  | Wrong
  | Ok of value_set_of_closures Closure_id.Map.t
          * Variable.t option * Symbol.t option

let strict_reify_as_closure t : strict_reified_as_closure =
  match reify_as_closure_allowing_unresolved t with
  | Ok (value_closures, set_of_closures_var, set_of_closures_symbol) ->
    Ok (value_closures, set_of_closures_var, set_of_closures_symbol)
  | Wrong | Unknown | Unresolved _ | Unknown_because_of_unresolved_value _ ->
    Wrong

type strict_reified_as_closure_singleton =
  | Wrong
  | Ok of Closure_id.t * Variable.t option
      * Symbol.t option * value_set_of_closures

let strict_reify_as_closure_singleton t
  : strict_reified_as_closure_singleton =
  match reify_as_closure_allowing_unresolved t with
  | Ok (value_closures, set_of_closures_var, set_of_closures_symbol) -> begin
    match Closure_id.Map.get_singleton value_closures with
    | None -> Wrong
    | Some (closure_id, value_set_of_closures) ->
      Ok (closure_id, set_of_closures_var, set_of_closures_symbol,
          value_set_of_closures)
    end
  | Wrong | Unknown | Unresolved _ | Unknown_because_of_unresolved_value _ ->
    Wrong

type reified_as_closure_allowing_unresolved =
  | Wrong
  | Unresolved of unresolved_value
  | Unknown
  | Ok of value_set_of_closures Closure_id.Map.t * Variable.t option
      * Symbol.t option

let reify_as_closure_allowing_unresolved t
      : reified_as_closure_allowing_unresolved =
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
            | Bottom | Load_lazily _ | String _ | Float_array _  ->
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
      | Nativeint _ | Unknown _ | Bottom | Load_lazily _
      | String _ | Float_array _  | Union _ -> Wrong
    end
  | Unknown (Unresolved_value value) -> Unresolved value
  | Set_of_closures _ | Union _ | Boxed_number _
  | Float _ | Int32 _ | Int64 _ | Nativeint _ | Bottom | Load_lazily _
  | String _ | Float_array _  -> Wrong
  (* CR-soon mshinwell: This should be unwound once the reason for a value
     being unknown can be correctly propagated through the export info. *)
  | Unknown Other -> Unknown

type switch_branch_classification =
  | Cannot_be_taken
  | Can_be_taken
  | Must_be_taken

let switch_branch_classification t branch : switch_branch_classification =
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
  | Unresolved _ | Unknown _ | Load_lazily _  ->
    (* In theory symbols cannot contain integers but this shouldn't
       matter as this will always be an imported type. *)
    Can_be_taken
  | Boxed_number _ | Float_array _ | String _ | Closure _ | Set_of_closures _
  | Float | Int32 | Int64 | Nativeint | Bottom -> Cannot_be_taken
