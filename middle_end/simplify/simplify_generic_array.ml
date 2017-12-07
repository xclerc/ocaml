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

(* CR mshinwell: Finish this

module B = Inlining_cost.Benefit
module E = Simplify_env_and_result.Env
module K = Flambda_kind
module R = Simplify_env_and_result.Result
module T = Flambda_type

module Float_by_bit_pattern = Numbers.Float_by_bit_pattern
module Int = Numbers.Int
module Named = Flambda.Named
module Reachable = Flambda.Reachable

let simplify_block_set env r prim ~field
      (spec : Flambda_primitive.generic_array_specialisation)
      args =
  (* Try to specialise the access based on the type of the array. *)
  let block_proof = (E.type_accessor env T.prove_float_array) block_ty in
  match block_proof with
  | Proved 

  | Proved Not_all_values_known | Invalid ->

let simplify_make_block env r prim dbg
      (spec : Flambda_primitive.generic_array_specialisation)
      ~mutable_or_immutable args =
  match spec with
  | Full_of_naked_floats ->
    let proof =
      (E.type_accessor env T.prove_of_kind_naked_float_list) arg_tys
    in
    begin match proof with
    | Proved arg_tys ->
      let ty =
        match mutable_or_immutable with
        | Immutable ->
          T.immutable_float_array arg_tys
        | Mutable ->
          T.mutable_float_array ~size:(List.length arg_tys)
      in
      [], Reachable.reachable term, ty
    | Invalid -> invalid ()
    end
  | Full_of_immediates ->
    let proof =
      (E.type_accessor env T.prove_tagged_immediate_list) arg_tys
    in
    begin match proof with
    | Proved arg_tys ->
      let ty =
        ...
      in
      [], Reachable.reachable term, ty
    | Invalid -> invalid ()
    end
  | Full_of_arbitrary_values_but_not_floats ->


  | No_specialisation ->
    (* CR mshinwell: We should improve the efficiency of this code once we
       are sure the semantics are correct *)
    (* First try to specialise the generic array to a float array.  If that
       fails then try to specialise it to an array of element kind
       [Value Definitely_immediate] or [Value Unknown]. *)
    let boxed_float_proofs =
      List.map (fun arg ->
          (E.type_accessor env T.prove_boxed_float) arg)
        args
    in
    let invalid =
      List.exists (fun (proof : T.boxed_float_proof) ->
          match proof with
          | Invalid -> true
          | Proved _ | Unknown -> false)
        boxed_float_proofs
    in
    let at_least_one_boxed_float =
      List.exists (fun (proof : T.boxed_float_proof) ->
          match proof with
          | Proved _ -> true
          | Unknown | Invalid -> false)
        boxed_float_proofs
    in
    let can_turn_into_float_array =
      at_least_one_boxed_float && not invalid
    in
    if can_turn_into_float_array then begin
      (* The arguments to the primitive must be unboxed, since we're going
         to switch it to [Full_of_naked_floats]. *)
      let unboxed_args_with_bindings =
        List.map (fun arg ->
            let unboxed_arg = Simple.fresh_variable arg in
            let kind = Flambda_kind.naked_float () in
            let defining_expr : Named.t =
              Prim (Unary (Unbox_number Naked_float, arg), dbg)
            in
            unboxed_arg, defining_expr)
          args
      in
      let unboxed_args, _bindings = List.split unboxed_args_with_bindings in
      let term : Named.t =
        Prim (Variadic (
          Make_block (
            Generic_array Full_of_naked_floats, mutable_or_immutable),
          unboxed_args))
      in
      assert (List.compare_lengths boxed_float_proofs unboxed_args = 0);
      let field_tys =
        (* CR mshinwell: rewrite to avoid "assert false" *)
        List.map2 (fun (proof : T.boxed_float_proof) unboxed_arg ->
            match proof with
            | Proved unboxed_arg_ty -> unboxed_arg_ty
            | Unknown -> T.alias_as_ty_naked_float unboxed_arg
            | Invalid -> assert false)
          boxed_float_proofs
          unboxed_args
      in
      let ty =
        match mutable_or_immutable with
        | Immutable ->
          T.immutable_float_array (Array.of_list field_tys)
        | Mutable ->
          T.mutable_float_array ~size:(List.length field_tys)
      in
      unboxed_args_with_bindings, Reachable.reachable term, ty
    end else begin
      let definitely_immediate_proofs =
        (E.type_accessor env T.prove_of_kind_value_definitely_immediate_list)
        arg_tys
      in
      let all_definitely_immediate =
        List.exists (fun (proof : _ or_invalid) ->
            match proof with
            | Proved _ -> true
            | Invalid -> false)
          definitely_immediate_proofs
      in
      let turn_into_full_of_values ~proofs ~value_kind =
        let tag = Tag.Scannable.zero in
        let value_kind =
          List.init (List.length args)
            (fun _index : K.value_kind -> value_kind)
        in
        let term : Named.t =
          Prim (Variadic (
            Make_block (Full_of_values (tag, value_kind), mutable_or_immutable),
            args))
        in
        let field_tys =
          (* CR mshinwell: rewrite to avoid "assert false" *)
          List.map2 (fun (proof : T.ty_value T.or_invalid) arg ->
              match proof with
              | Proved arg_ty -> arg_ty
              | Invalid -> assert false)
            proofs
            args
        in
        let field_tys = Array.of_list field_tys in
        let field_tys =
          match mutable_or_immutable with
          | Immutable -> field_tys
          | Mutable -> T.unknown_like field_tys
        in
        [], Reachable.reachable term, T.block tag field_tys
      in
      if all_definitely_immediate then begin
        turn_into_full_of_values ~proofs:definitely_immediate_proofs
          ~value_kind:Definitely_immediate
      end else begin
        let not_a_float_proofs =
          (E.type_accessor env
            T.prove_of_kind_value_and_definitely_not_a_float_list)
          arg_tys
        in
        let all_not_a_float_and_definitely_no_floats =
          List.exists (fun (proof : _ or_invalid) ->
              match proof with
              | Proved _ -> true
              | Invalid -> false)
            not_a_float_proofs
        in
        if all_not_a_float_and_definitely_no_floats then begin
          turn_into_full_of_values ~proofs:not_a_float_proofs
            ~value_kind:not_a_float
        else begin
          let invalid =
            List.exists (fun (proof : _ or_invalid) ->
                match proof with
                | Proved _ -> false
                | Invalid -> true)
              not_a_float_proofs
          in
          if invalid then invalid ()
          else
            let type_if_normal_array =
              let field_tys =
                List.map (fun arg ->
                    T.alias (K.value not_a_float) arg)
                  args
              in
              T.block tag (Array.of_list field_tys)
            in
            let type_if_float_array =
              match mutable_or_immutable with
              | Immutable ->
                let field_tys =
                  List.map (fun _arg -> T.any_naked_float ()) args
                in
                T.immutable_float_array (Array.of_list field_tys)
              | Mutable ->
                T.mutable_float_array ~size:(List.length args)
            in
            let ty =
              (E.type_accessor env T.join)
                type_if_normal_array
                type_if_float_array
            in
            [], Reachable.reachable (original_term ()), ty
        end
      end
    end

*)
