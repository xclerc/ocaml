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

let simplify_primitive env r prim dbg =
  match prim with
  | Unary (prim, arg) ->
    Simplify_unary_primitive.simplify_unary_primitive env r prim arg dbg
  | Binary (prim, arg1, arg2) ->
    Simplify_binary_primitive.simplify_binary_primitive env r prim arg1 arg2 dbg
  | Ternary (prim, arg1, arg2, arg3) ->
    Simplify_ternary_primitive.simplify_ternary_primitive env r prim
      arg1 arg2 arg3 dbg
  | Variadic (prim, args) ->
    Simplify_variadic_primitive.simplify_variadic_primitive env r prim args dbg

(* Old code:
let simplify_primitive0 (p : Lambda.primitive) (args, approxs) expr dbg
      ~size_int ~big_endian : Named.t * T.t * Inlining_cost.Benefit.t =
  let fpc = !Clflags.float_const_prop in
  match p with
  | Pmakeblock(tag_int, Flambda.Immutable, shape) ->
    let tag = Tag.create_exn tag_int in
    let shape = match shape with
      | None -> List.map (fun _ -> Lambda.Pgenval) args
      | Some shape -> shape
    in
    let approxs = List.map2 T.augment_with_kind approxs shape in
    let shape = List.map2 T.augment_kind_with_approx approxs shape in
    Prim (Pmakeblock(tag_int, Flambda.Immutable, Some shape), args, dbg),
    T.value_block tag (Array.of_list approxs), C.Benefit.zero
  | Pmakearray(_, _) when approxs = [] ->
    Prim (Pmakeblock(0, Flambda.Immutable, Some []), [], dbg),
    T.value_block (Tag.create_exn 0) [||], C.Benefit.zero
  | Pmakearray (Pfloatarray, Mutable) ->
      let approx =
        T.value_mutable_float_array ~size:(List.length args)
      in
      expr, approx, C.Benefit.zero
  | Pmakearray (Pfloatarray, Immutable) ->
      let approx =
        T.value_immutable_float_array (Array.of_list approxs)
      in
      expr, approx, C.Benefit.zero
  | Pintcomp Ceq when T.phys_equal approxs ->
    S.const_bool_expr expr true
  | Pintcomp Cneq when T.phys_equal approxs ->
    S.const_bool_expr expr false
    (* N.B. Having [not (phys_equal approxs)] would not on its own tell us
       anything about whether the two values concerned are unequal.  To judge
       that, it would be necessary to prove that the approximations are
       different, which would in turn entail them being completely known.

       It may seem that in the case where we have two approximations each
       annotated with a symbol that we should be able to judge inequality
       even if part of the approximation description(s) are unknown.  This is
       unfortunately not the case.  Here is an example:

         let a = f 1
         let b = f 1
         let c = a, a
         let d = a, a

       If [Share_constants] is run before [f] is completely inlined (assuming
       [f] always generates the same result; effects of [f] aren't in fact
       relevant) then [c] and [d] will not be shared.  However if [f] is
       inlined later, [a] and [b] could be shared and thus [c] and [d] could
       be too.  As such, any intermediate non-aliasing judgement would be
       invalid. *)
  | Pintcomp Ceq when T.phys_different approxs ->
    S.const_bool_expr expr false
  | Pintcomp Cneq when T.phys_different approxs ->
    S.const_bool_expr expr true
    (* If two values are structurally different we are certain they can never
       be shared*)
  | _ ->
    match T.descrs approxs with
    | [Union union] ->
      begin match T.Unionable.flatten union with
      | Ok (Int x) ->
        begin match p with
        | Pidentity -> S.const_int_expr expr x
        | Pnot -> S.const_bool_expr expr (x = 0)
      | Pnegint -> S.const_int_expr expr (-x)
      | Pbswap16 -> S.const_int_expr expr (S.swap16 x)
      | Poffsetint y -> S.const_int_expr expr (x + y)
      | Pfloatofint Boxed when fpc -> S.const_float_expr expr (float_of_int x)
      | Pbintofint Pnativeint ->
        S.const_boxed_int_expr expr Nativeint (Nativeint.of_int x)
      | Pbintofint Pint32 -> S.const_boxed_int_expr expr Int32 (Int32.of_int x)
        | Pbintofint Pint64 -> S.const_boxed_int_expr expr Int64 (Int64.of_int x)
        | _ -> expr, T.value_unknown Other, C.Benefit.zero
        end
      | Ok (Constptr x) ->
        begin match p with
        (* [Pidentity] should probably never appear, but is here for
          completeness. *)
        | Pidentity -> S.const_ptr_expr expr x
        | Pnot -> S.const_bool_expr expr (x = 0)
        | Poffsetint y -> S.const_ptr_expr expr (x + y)
        | _ -> expr, T.value_unknown Other, C.Benefit.zero
        end
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [Union union1; Union union2] ->
      begin match T.Unionable.flatten union1, T.Unionable.flatten union2 with
      | Ok (Int x | Constptr x), Ok (Int y | Constptr y) ->
        let shift_precond = 0 <= y && y < 8 * size_int in
        begin match p with
        | Plslint when shift_precond -> S.const_int_expr expr (x lsl y)
        | Plsrint when shift_precond -> S.const_int_expr expr (x lsr y)
        | Pasrint when shift_precond -> S.const_int_expr expr (x asr y)
        | Pintcomp cmp -> S.const_comparison_expr expr cmp x y
        | Pisout -> S.const_bool_expr expr (y > x || y < 0)
        | _ -> expr, T.value_unknown Other, C.Benefit.zero
        end
      | Ok (Char x), Ok (Char y) ->
        begin match p with
        | Pintcomp cmp -> S.const_comparison_expr expr cmp x y
        | _ -> expr, T.value_unknown Other, C.Benefit.zero
        end
      | _, _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [Boxed_float (Some x)] when fpc ->
      begin match p with
      | Pintoffloat Boxed -> S.const_int_expr expr (int_of_float x)
      | Pnegfloat Boxed -> S.const_float_expr expr (-. x)
      | Pabsfloat Boxed -> S.const_float_expr expr (abs_float x)
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [Boxed_float (Some n1); Boxed_float (Some n2)] when fpc ->
      begin match p with
      | Paddfloat Boxed -> S.const_float_expr expr (n1 +. n2)
      | Psubfloat Boxed -> S.const_float_expr expr (n1 -. n2)
      | Pmulfloat Boxed -> S.const_float_expr expr (n1 *. n2)
      | Pdivfloat Boxed -> S.const_float_expr expr (n1 /. n2)
      | Pfloatcomp (c, Boxed)  -> S.const_comparison_expr expr c n1 n2
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [T.Boxed_int(T.Nativeint, n)] ->
      I.Simplify_boxed_nativeint.simplify_unop p Nativeint expr n
    | [T.Boxed_int(T.Int32, n)] ->
      I.Simplify_boxed_int32.simplify_unop p Int32 expr n
    | [T.Boxed_int(T.Int64, n)] ->
      I.Simplify_boxed_int64.simplify_unop p Int64 expr n
    | [T.Boxed_int(T.Nativeint, n1);
       T.Boxed_int(T.Nativeint, n2)] ->
      I.Simplify_boxed_nativeint.simplify_binop p Nativeint expr n1 n2
    | [T.Boxed_int(T.Int32, n1); T.Boxed_int(T.Int32, n2)] ->
      I.Simplify_boxed_int32.simplify_binop p Int32 expr n1 n2
    | [T.Boxed_int(T.Int64, n1); T.Boxed_int(T.Int64, n2)] ->
      I.Simplify_boxed_int64.simplify_binop p Int64 expr n1 n2
    | [T.Boxed_int(T.Nativeint, n1); Union union2] ->
      begin match T.Unionable.flatten union2 with
      | Ok (Int n2) ->
        I.Simplify_boxed_nativeint.simplify_binop_int p Nativeint expr n1 n2
          ~size_int
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [T.Boxed_int(T.Int32, n1); Union union2] ->
      begin match T.Unionable.flatten union2 with
      | Ok (Int n2) ->
        I.Simplify_boxed_int32.simplify_binop_int p Int32 expr n1 n2
          ~size_int
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [T.Boxed_int(T.Int64, n1); Union union2] ->
      begin match T.Unionable.flatten union2 with
      | Ok (Int n2) ->
        I.Simplify_boxed_int64.simplify_binop_int p Int64 expr n1 n2
          ~size_int
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [String { size }]
      when (p = Lambda.Pstringlength || p = Lambda.Pbyteslength) ->
      S.const_int_expr expr size
    | [String { size; contents = Some s }; Union union2] ->
      begin match T.Unionable.flatten union2 with
      | Ok (Int x) | Ok (Constptr x) when x >= 0 && x < size ->
        begin match p with
        | Pstringrefu
        | Pstringrefs
        | Pbytesrefu
        | Pbytesrefs ->
          S.const_char_expr (Prim(Pstringrefu, args, dbg)) s.[x]
        | _ -> expr, T.value_unknown Other, C.Benefit.zero
        end
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [String { size; contents = None }; Union union2] ->
      begin match T.Unionable.flatten union2 with
      | Ok (Int x) | Ok (Constptr x)
          when x >= 0 && x < size && p = Lambda.Pstringrefs ->
        Flambda.Prim (Pstringrefu, args, dbg),
          T.value_unknown Other,
          (* we improved it, but there is no way to account for that: *)
          C.Benefit.zero
      | Ok (Int x) | Ok (Constptr x)
          when x >= 0 && x < size && p = Lambda.Pbytesrefs ->
        Flambda.Prim (Pbytesrefu, args, dbg),
          T.value_unknown Other,
          (* we improved it, but there is no way to account for that: *)
          C.Benefit.zero
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [Float_array { size; contents }] ->
        begin match p with
        | Parraylength _ -> S.const_int_expr expr size
        | Pfloatfield i ->
          begin match contents with
          | T.Contents a when i >= 0 && i < size ->
            begin match T.check_approx_for_float a.(i) with
            | None -> expr, a.(i), C.Benefit.zero
            | Some v -> S.const_float_expr expr v
            end
          | Contents _ | Unknown_or_mutable ->
            expr, T.value_unknown Other, C.Benefit.zero
          end
        | _ -> expr, T.value_unknown Other, C.Benefit.zero
        end
    | _ ->
      match Semantics_of_primitives.return_type_of_primitive p with
      | Boxed_float ->
        expr, T.value_any_float, C.Benefit.zero
      | Unboxed_float ->
        expr, T.any_unboxed_float, C.Benefit.zero
      | Unboxed_int32 ->
        expr, T.any_unboxed_int32, C.Benefit.zero
      | Unboxed_int64 ->
        expr, T.any_unboxed_int64, C.Benefit.zero
      | Unboxed_nativeint ->
        expr, T.any_unboxed_nativeint, C.Benefit.zero
      | Other ->
        expr, T.value_unknown Other, C.Benefit.zero

let simplify_primitive env r prim args dbg : named_simplifier =
  let dbg = E.add_inlined_debuginfo env ~dbg in
  let args, args_tys = freshen_and_squash_aliases_list env args in
  let tree = Flambda.Prim (prim, args, dbg) in
  let projection : Projection.t = Prim (prim, args) in
  begin match E.find_projection env ~projection with
  | Some var ->
    (* CSE of pure primitives.
       The [Pisint] case in particular is also used when unboxing
       continuation parameters of variant type. *)
    let var, var_ty = freshen_and_squash_aliases env var in
    let r = R.map_benefit r (B.remove_projection projection) in
    [], Reachable (Var var), var_ty
  | None ->
    let default () : (Variable.t * Named.t) list
          * Named.t_reachable * R.t =
      let named, ty, benefit =
        (* CR mshinwell: if the primitive is pure, add it to the environment
           so CSE will work.  Need to be careful if the variable being
           bound is a continuation argument *)
        let module Backend = (val (E.backend env) : Backend_intf.S) in
        simplify_primitive0 prim (args, args_tys) tree dbg
          ~size_int:Backend.size_int ~big_endian:Backend.big_endian
      in
      let r = R.map_benefit r (B.(+) benefit) in
      let ty =
        match prim with
        | Popaque -> T.unknown Other
        | _ -> ty
      in
      [], Reachable (named, value_kind), ty
    in
    begin match prim, args, args_tys with
    | Pfield field_index, [arg], [arg_ty] ->
      let projection : Projection.t = Prim (Pfield field_index, [arg]) in
      begin match E.find_projection env ~projection with
      | Some var ->
        let var, var_ty = freshen_and_squash_aliases env var in
        let r = R.map_benefit r (B.remove_projection projection) in
        [], Reachable (Var var), var_ty
      | None ->
        begin match T.get_field arg_ty ~field_index with
        | Invalid _ ->
          [], Reachable.invalid (), r
        | Ok ty ->
          let tree, ty =
            match arg_ty.symbol with
            (* If the [Pfield] is projecting directly from a symbol, rewrite
                the expression to [Read_symbol_field]. *)
            | Some (symbol, None) ->
              let ty =
                T.augment_with_symbol_field ty symbol field_index
              in
              Flambda.Read_symbol_field (symbol, field_index), ty
            | None | Some (_, Some _ ) ->
              (* This [Pfield] is either not projecting from a symbol at
                 all, or it is the projection of a projection from a
                 symbol. *)
              let ty' = E.really_import_ty env ty in
              tree, ty'
          in
          simpler_equivalent_term env r tree ty
        end
      end
    | Pfield _, _, _ -> Misc.fatal_error "Pfield arity error"
    | (Parraysetu kind | Parraysets kind),
        [_block; _field; _value],
        [block_ty; field_ty; value_ty] ->
      if T.invalid_to_mutate block_ty then begin
        [], Reachable.invalid (), r
      end else begin
        let size = T.length_of_array block_ty in
        let index = T.reify_as_int field_ty in
        let bounds_check_definitely_fails =
          match size, index with
          | Some size, _ when size <= 0 ->
            assert (size = 0);  (* see [Simple_value_ty] *)
            true
          | Some size, Some index ->
            (* This is ok even in the presence of [Obj.truncate], since that
               can only make blocks smaller. *)
            index >= 0 && index < size
          | _, _ -> false
        in
        let convert_to_raise =
          match prim with
          | Parraysets _ -> bounds_check_definitely_fails
          | Parraysetu _ -> false
          | _ -> assert false  (* see above *)
        in
        if convert_to_raise then begin
          (* CR mshinwell: move to separate function *)
          let invalid_argument_var = Variable.create "invalid_argument" in
          let invalid_argument : Named.t =
            let module Backend = (val (E.backend env) : Backend_intf.S) in
            Symbol (Backend.symbol_for_global'
              Predef.ident_invalid_argument)
          in
          let msg_var = Variable.create "msg" in
          let msg : Named.t =
            Allocated_const (String "index out of bounds")
          in
          let exn_var = Variable.create "exn" in
          let exn : Named.t =
            Prim (Pmakeblock (0, Immutable, None),
              [invalid_argument_var; msg_var], dbg)
          in
          let bindings = [
              invalid_argument_var, invalid_argument;
              msg_var, msg;
              exn_var, exn;
            ]
          in
          bindings, Reachable (Prim (Praise Raise_regular, [exn_var], dbg)),
            T.bottom
        end else begin
          let kind =
            match T.is_float_array block_ty, T.is_boxed_float value_ty with
            | (true, _)
            | (_, true) ->
              begin match kind with
              | Pfloatarray | Pgenarray -> ()
              | Paddrarray | Pintarray ->
                (* CR pchambart: Do a proper warning here *)
                Misc.fatal_errorf "Assignment of a float to a specialised \
                                  non-float array: %a"
                  Named.print tree
              end;
              Lambda.Pfloatarray
              (* CR pchambart: This should be accounted by the benefit *)
            | _ ->
              kind
          in
          let prim : Lambda.primitive =
            match prim with
            | Parraysetu _ -> Parraysetu kind
            | Parraysets _ -> Parraysets kind
            | _ -> assert false
          in
          [], Reachable (Prim (prim, args, dbg)), ret r (T.unknown Other)
        end
      end
    | Psetfield _, _block::_, block_ty::_ ->
      if T.invalid_to_mutate block_ty then begin
        [], Reachable.invalid (), r
      end else begin
        [], Reachable tree, ret r (T.unknown Other)
      end
    | Parraylength _, [_arg], [arg_ty] ->
      begin match T.length_of_array arg_ty with
      | None -> default ()
      | Some length ->
        let r = R.map_benefit r B.remove_prim in
        let const_length = Variable.create "length" in
        [const_length, Const (Int length)], Reachable (Var const_length),
          ret r (T.int length)
      end
    end
  end
*)
