(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2017 OCamlPro SAS                                          *)
(*   Copyright 2017 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]
(*
(* CR-soon mshinwell: This is a crude implementation which should suffice
   for the moment.  We should maybe make [Invariant_params] work over
   both functions and continuations so we can share code (in particular
   when mutually-recursive continuations are permitted). *)
let unused_parameters ~cont ~(handler : Flambda.continuation_handler) =
  match handler.recursive with
  | Nonrecursive ->
    Variable.Set.diff (Variable.Set.of_list handler.params)
      (Flambda.free_variables handler.handler)
  | Recursive ->
    let invariant_params =
      Invariant_params.invariant_params_of_continuation ~cont ~handler
    in
    let fvs_ignoring_apply_cont =
      Flambda.free_variables ~ignore_uses_in_apply_cont:() handler.handler
    in
    let unused =
      ref (Variable.Set.diff invariant_params fvs_ignoring_apply_cont)
    in
    Flambda_iterators.iter_expr (fun (expr : Flambda.expr) ->
        match expr with
        | Apply_cont (cont', _trap_action, args)
            when Continuation.equal cont cont' ->
          assert (List.length handler.params = List.length args);
          (* This next bit follows from the simplistic behaviour of
             [Invariant_params] for continuations. *)
          let used = 
            Variable.Set.fold (fun param used ->
                let num_uses =
                  List.fold_left (fun num_uses arg ->
                      if Variable.equal param arg then num_uses + 1
                      else num_uses)
                    0
                    args
                in
                assert (num_uses >= 1);
                if num_uses > 1 then Variable.Set.add param used
                else used)
              !unused
              Variable.Set.empty
          in
          unused := Variable.Set.diff !unused used)
      handler.handler;
    !unused

let for_continuation ~cont ~body ~(handler : Flambda.continuation_handler)
      ~original =
  let unused = unused_parameters ~cont ~handler in
  if Variable.Set.empty unused then
    original
  else
    let remaining_params =
      List.filter (fun param -> not (Variable.Set.mem param unused))
        handler.params
    in
    let remaining_specialised_args =
      Flambda_utils.clean_specialised_args_projections (
        Variable.Map.filter (fun param _spec_to ->
            not (Variable.Set.mem param unused))
          handler.specialised_args)
    in
    let rewritten_original_handler = Continuation.create () in
    let wrapper_inside_handler = Continuation.create () in
    let expr =

(* Needs mutually recursive continuations to add the wrapper *)

    in
    Let_cont {
      name = rewritten_original_handler;
      handler = Handler {
        params = remaining_params;
        recursive = handler.recursive;
        stub = handler.stub;
        handler =
        specialised_args = remaining_specialised_args;
      };
      body =
        Let_
          Let_cont {
            name = wrapper_inside_handler;
            handler = Handler {
              params = wrapper_inside_handler_params;
              recursive = false;
              stub = true;
              handler =
                Apply ...;
              specialised_args = Variable.Map.empty;
            }
          };

let run program =
  Flambda_iterators.map_exprs_at_toplevel_of_program program
    ~f:(fun expr ->
      Flambda_iterators.map_expr (fun (expr : Flambda.expr) ->
          match expr with
          | Let_cont { name; body; handler = Handler handler; } ->
            for_continuation ~cont:name ~body ~handler ~original:expr
          | Let_cont { handler = Alias _; _ }
          | Let _ | Let_mutable _ | Apply _ | Apply_cont _ | Switch _
          | Proved_unreachable -> expr)
        expr)
*)

let run _program = assert false
