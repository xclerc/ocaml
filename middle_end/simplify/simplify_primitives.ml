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

module T = Flambda_types
module C = Inlining_cost
module I = Simplify_boxed_integer_ops
module S = Simplify_common

let primitive (p : Lambda.primitive) (args, approxs) expr dbg ~size_int
      ~big_endian : Flambda.Named.t * T.t * Inlining_cost.Benefit.t =
  let fpc = !Clflags.float_const_prop in
  match p with
  | Pmakeblock(tag_int, Asttypes.Immutable, shape) ->
    let tag = Tag.create_exn tag_int in
    let shape = match shape with
      | None -> List.map (fun _ -> Lambda.Pgenval) args
      | Some shape -> shape
    in
    let approxs = List.map2 T.augment_with_kind approxs shape in
    let shape = List.map2 T.augment_kind_with_approx approxs shape in
    Prim (Pmakeblock(tag_int, Asttypes.Immutable, Some shape), args, dbg),
    T.value_block tag (Array.of_list approxs), C.Benefit.zero
  | Praise _ ->
    expr, T.value_bottom, C.Benefit.zero
  | Pignore -> begin
      match args, T.descrs approxs with
      | [arg], [Union union] ->
        begin match T.Unionable.flatten union with
        | Ok (Int 0) | Ok (Constptr 0) ->
          S.const_ptr_expr (Flambda.Var arg) 0
        | _ -> S.const_ptr_expr expr 0
        end
      | _ -> S.const_ptr_expr expr 0
    end
  | Pmakearray(_, _) when approxs = [] ->
    Prim (Pmakeblock(0, Asttypes.Immutable, Some []), [], dbg),
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
    | [Union union] when p = Lambda.Pisint ->
      begin match T.Unionable.flatten union with
      | Ok (Int _ | Char _ | Constptr _) -> S.const_bool_expr expr true
      | Ok (Block _) -> S.const_bool_expr expr false
      | Ill_typed_code -> expr, T.value_bottom, C.Benefit.zero
      | Anything -> expr, T.value_unknown Other, C.Benefit.zero
      end
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
        | Pctconst c ->
          begin match c with
          | Big_endian -> S.const_bool_expr expr big_endian
          | Word_size -> S.const_int_expr expr (8*size_int)
          | Int_size -> S.const_int_expr expr (8*size_int - 1)
          | Max_wosize ->
            (* CR-someday mshinwell: this function should maybe not live here. *)
            S.const_int_expr expr ((1 lsl ((8*size_int) - 10)) - 1)
          | Ostype_unix -> S.const_bool_expr expr (Sys.os_type = "Unix")
          | Ostype_win32 -> S.const_bool_expr expr (Sys.os_type = "Win32")
          | Ostype_cygwin -> S.const_bool_expr expr (Sys.os_type = "Cygwin")
          | Backend_type ->
            S.const_ptr_expr expr 0 (* tag 0 is the same as Native *)
          end
        | _ -> expr, T.value_unknown Other, C.Benefit.zero
        end
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [Union union1; Union union2] ->
      begin match T.Unionable.flatten union1, A.Unionable.flatten union2 with
      | Ok (Int x | Constptr x), Ok (Int y | Constptr y) ->
        let shift_precond = 0 <= y && y < 8 * size_int in
        begin match p with
        | Paddint -> S.const_int_expr expr (x + y)
        | Psubint -> S.const_int_expr expr (x - y)
        | Pmulint -> S.const_int_expr expr (x * y)
        | Pdivint _ when y <> 0 -> S.const_int_expr expr (x / y)
        | Pmodint _ when y <> 0 -> S.const_int_expr expr (x mod y)
        | Pandint -> S.const_int_expr expr (x land y)
        | Porint -> S.const_int_expr expr (x lor y)
        | Pxorint -> S.const_int_expr expr (x lxor y)
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
    | [T.Boxed_int(A.Nativeint, n)] ->
      I.Simplify_boxed_nativeint.simplify_unop p Nativeint expr n
    | [T.Boxed_int(A.Int32, n)] ->
      I.Simplify_boxed_int32.simplify_unop p Int32 expr n
    | [T.Boxed_int(A.Int64, n)] ->
      I.Simplify_boxed_int64.simplify_unop p Int64 expr n
    | [T.Boxed_int(A.Nativeint, n1);
       T.Boxed_int(A.Nativeint, n2)] ->
      I.Simplify_boxed_nativeint.simplify_binop p Nativeint expr n1 n2
    | [T.Boxed_int(A.Int32, n1); A.Boxed_int(A.Int32, n2)] ->
      I.Simplify_boxed_int32.simplify_binop p Int32 expr n1 n2
    | [T.Boxed_int(A.Int64, n1); A.Boxed_int(A.Int64, n2)] ->
      I.Simplify_boxed_int64.simplify_binop p Int64 expr n1 n2
    | [T.Boxed_int(A.Nativeint, n1); Union union2] ->
      begin match T.Unionable.flatten union2 with
      | Ok (Int n2) ->
        I.Simplify_boxed_nativeint.simplify_binop_int p Nativeint expr n1 n2
          ~size_int
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [T.Boxed_int(A.Int32, n1); Union union2] ->
      begin match T.Unionable.flatten union2 with
      | Ok (Int n2) ->
        I.Simplify_boxed_int32.simplify_binop_int p Int32 expr n1 n2
          ~size_int
      | _ -> expr, T.value_unknown Other, C.Benefit.zero
      end
    | [T.Boxed_int(A.Int64, n1); Union union2] ->
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