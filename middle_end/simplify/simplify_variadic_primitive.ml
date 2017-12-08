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

module B = Inlining_cost.Benefit
module E = Simplify_env_and_result.Env
module K = Flambda_kind
module R = Simplify_env_and_result.Result
module T = Flambda_type

module Float_by_bit_pattern = Numbers.Float_by_bit_pattern
module Int = Numbers.Int
module Named = Flambda.Named
module Reachable = Flambda.Reachable

type 'a or_invalid = Ok of 'a | Invalid

let simplify_make_block env r prim dbg ~make_block_kind ~mutable_or_immutable
      args =
  let original_args = args in
  let args_with_tys = S.simplify_simple env args in
  let args, arg_tys = List.split args_with_tys in
  let original_term () : Named.t = Prim (Variadic (prim, args), dbg) in
  let invalid () = [], Reachable.invalid (), T.bottom (K.value Must_scan) in
  let new_bindings, term, ty =
    match make_block_kind with
    | Full_of_values (tag, value_kinds) ->
      if List.compare_lengths value_kinds args <> 0 then begin
        Misc.fatal_errorf "GC value_kind indications in [Make_block] don't \
            match up 1:1 with arguments: %a (%a)"
          Flambda_primitive.print prim
          Simple.List.print original_args
      end;
      let proofs =
        (E.type_accessor env T.prove_of_kind_value) arg_tys
      in
      assert (List.compare_lengths value_kinds arg_tys = 0);
      assert (List.compare_lengths proof arg_tys = 0);
      let arg_ty_and_value_kinds_rev =
        List.fold_left2 (fun (arg_ty_and_value_kinds_rev : _ or_invalid)
              (arg, (declared_value_kind : K.value_kind))
              (proof : T.of_kind_value T.or_invalid) : _ or_invalid ->
            match proof with
            | Invalid -> Invalid
            | Proved arg_ty ->
              match arg_tys_rev with
              | Invalid -> Invalid
              | Ok arg_tys_rev ->
                let actual_value_kind =
                  (E.type_accessor env T.value_kind_ty_value) arg_ty
                in
                let compatible =
                  K.compatible_value_kind actual_value_kind
                    ~if_used_at:declared_value_kind
                in
                let value_kind =
                  K.meet_value_kind actual_value_kind declared_value_kind
                in
                if not compatible then Invalid
                else Ok ((arg_ty, value_kind) :: arg_tys))
          (Ok [])
          proofs (List.combine args value_kinds)
      in
      begin match arg_ty_and_value_kinds_rev with
      | Invalid -> invalid ()
      | Ok arg_ty_and_value_kinds_rev ->
        let arg_tys_rev, value_kinds_rev =
          List.split arg_ty_and_value_kinds_rev
        in
        let arg_tys = Array.of_list (List.rev arg_tys_rev) in
        let value_kinds = List.rev value_kinds_rev in
        let term =
          Prim (Variadic (
            Make_block (Full_of_values (tag, value_kinds),
              mutable_or_immutable),
            args))
        in
        let ty =
          match mutable_or_immutable with
          | Immutable ->
            T.block tag arg_tys
          | Mutable ->
            let arg_tys = (E.type_accessor env T.unknown_like) arg_tys in
            T.block tag arg_tys
        in
        [], Reachable.reachable term, ty
      | Invalid -> invalid ()
      end
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
    | Generic_array _spec -> Misc.fatal_error "Not yet implemented"
    (* CR mshinwell: Finish off
      Simplify_generic_array.simplify_make_block env r prim dbg spec
        ~mutable_or_immutable args
    *)
  in
  new_bindings, term, ty, r

(* CR mshinwell: Could use [unit or_invalid] rather than [bool] *)
(* XXX this should be "for all" not "exists".  Also, take care: when the list
   is empty, this should return false *)
let bigarray_indexes_are_invalid env indexes =
  let index_proofs =
    List.map (fun index ->
        (E.type_accessor env T.prove_tagged_immediate) index)
      indexes
  in
  List.fold_left
    (fun (index_proof : T.tagged_immediate_proof) invalid ->
      if invalid then true
      else
        match index_proof with
        | Proved indexes ->
          List.fold_left (fun index invalid ->
              if invalid then true
              else
                let index = Immediate.to_targetint index in
                match layout with
                | Unknown | C ->
                  Targetint.OCaml.(<) index Targetint.OCaml.zero
                | Fortran ->
                  Targetint.OCaml.(<) index Targetint.OCaml.one)
            indexes
            false
        | Proved Not_all_values_known -> false
        | Invalid -> true)
    index_proofs
    false

(* XXX add "type_of_bigarray_kind" etc in this file. *)

let simplify_bigarray_set env r prim dbg ~num_dims ~kind ~layout ~args =
  let args_with_tys = S.simplify_simple env args in
  let args, _arg_tys = List.split args_with_tys in
  let original_term () : Named.t = Prim (Variadic (prim, args), dbg) in
  let element_kind = Flambda_primitive.kind_of_bigarray_kind kind in
  let result_kind = Flambda_kind.unit () in
  let invalid () = [], Reachable.invalid (), T.bottom result_kind, r in
  let wrong_number_of_args () =
    Misc.fatal_errorf "Wrong number of arguments for [Bigarray_set]: %a"
      Flambda_primitive.print prim
  in
  match args_with_tys with
  | (bigarray, bigarray_ty)::args_with_tys ->
    begin match List.first_n args_with_tys num_dims with
    | Some (indexes_with_tys, args_with_tys) ->
      begin match args_with_tys with
      | [new_value, new_value_ty] ->
        let bigarray_proof =
          (E.type_accessor env T.prove_of_kind_value_with_expected_value_kind
            Definitely_pointer) bigarray
        in
        begin match proof with
        | Proved _ ->
          let index_proofs =
            List.map (fun index ->
                (E.type_accessor env T.prove_tagged_immediate) index)
              indexes
          in
          let invalid = bigarray_indexes_are_invalid env indexes in
          if invalid then invalid ()
          else
            let new_value_proof =
              (E.type_accessor env T.prove_of_kind result_kind) new_value
            in
            begin match new_value_proof with
            | Proved _ ->
              [], Reachable.reachable (original_term ()),
                T.unknown result_kind Other, r
            | Invalid -> invalid ()
            end
        | Invalid -> invalid ()
        end
      | _ -> wrong_number_of_args ()
      end
    | None -> wrong_number_of_args ()
    end
  | [] -> wrong_number_of_args ()

let simplify_bigarray_load env r prim dbg ~num_dims
      ~(kind : Flambda_primitive.bigarray_kind)
      ~(layout : Flambda_primitive.bigarray_layout)
      args =
  let args_with_tys = S.simplify_simple env args in
  let args, arg_tys = List.split args_with_tys in
  let original_term () : Named.t = Prim (Variadic (prim, args), dbg) in
  let result_kind = Flambda_primitive.kind_of_bigarray_kind kind in
  let invalid () = [], Reachable.invalid (), T.bottom result_kind in
  let wrong_number_of_args () =
    Misc.fatal_errorf "Wrong number of arguments: %a"
      Flambda_primitive.print prim
  in
  match args_with_tys with
  | (bigarray, bigarray_ty)::args_with_tys ->
    begin match List.first_n args_with_tys num_dims with
    | Some (indexes_with_tys, args_with_tys) ->
      begin match args_with_tys with
      | [] ->
        let bigarray_proof =
          (E.type_accessor env T.prove_of_kind_value_with_expected_scanning
            Must_scan) bigarray
        in
        begin match proof with
        | Proved _ ->
          let index_proofs =
            List.map (fun index ->
                (E.type_accessor env T.prove_tagged_immediate) index)
              indexes
          in
          let invalid = bigarray_indexes_are_invalid env indexes in
          if invalid then invalid ()
          else
            [], Reachable.reachable (original_term ()),
              T.unknown result_kind Other, r
        | Invalid -> invalid ()
        end
      | _ -> wrong_number_of_args ()
      end
    | None -> wrong_number_of_args ()
    end
  | [] -> wrong_number_of_args ()

let simplify_variadic_primitive env r prim args dbg =
  match prim with
  | Make_block (make_block_kind, mutable_or_immutable) ->
    simplify_make_block env r prim dbg ~make_block_kind ~mutable_or_immutable
      args
  | Bigarray_set (num_dims, kind, layout) ->
    simplify_bigarray_set env r prim dbg ~num_dims ~kind ~layout ~args
  | Bigarray_load (num_dims, kind, layout) ->
    simplify_bigarray_load env r prim dbg ~num_dims ~kind ~layout args
