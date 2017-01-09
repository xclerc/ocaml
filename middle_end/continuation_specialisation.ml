(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2016 OCamlPro SAS                                          *)
(*   Copyright 2016 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module A = Simple_value_approx
module B = Inlining_cost.Benefit
module E = Inline_and_simplify_aux.Env
module R = Inline_and_simplify_aux.Result

type arg_action =
  | Cannot_specialise
  | Specialise_to of Variable.t

let find_specialisations r ~simplify =
  let module N = Num_continuation_uses in
  let module U = Inline_and_simplify_aux.Continuation_uses in
  (* For the moment, a very simple analysis: add specialised arguments to
     recursive continuations just when all of their application points have
     exactly the same variable as the given argument. *)
  (* CR mshinwell: [recursive] appears to be redundant with
     [approx.recursive] *)
  Continuation.Map.fold (fun cont (uses, approx, env, recursive)
        specialisations ->
      match (recursive : Asttypes.rec_flag) with
      | Nonrecursive -> specialisations
      | Recursive ->
        match Continuation_approx.handler approx with
        | None -> specialisations
        | Some handler ->
          (* Note that we don't need to check any non-inlinable application
              points in [uses], since continuations occurring in such places
              never have any arguments. *)
          let new_specialised_args =
            List.fold_left (fun specialised_args (use : U.Use.t) ->
                let params_with_approxs =
                  assert (List.length handler.params = List.length use.args);
                  List.map2 (fun param (arg, arg_approx) ->
                      param, arg_approx)
                    handler.params use.args
                in
                Variable.Map.union (fun (approx1 : A.t) (approx2 : A.t) ->
                    match approx1.var, approx2.var with
                    | None, None | None, Some _ | Some _, None ->
                      Some Cannot_specialise
                    | Some var1, Some var2 ->
                      if Variable.equal var1 var2 then
                        Some (Specialise_to var1)
                      else
                        Some Cannot_specialise)
                  specialised_args
                  params_with_approxs)
              definitions
              (U.inlinable_application_points uses)
          in
          let added_specialised_arg = ref false in
          let specialised_args =
            Variable.Map.fold (fun param (action : arg_action)
                    specialised_args ->
                match action with
                | Cannot_specialise -> specialised_args
                | Specialise_to var ->
                  match Variable.Map.find param specialised_args with
                  | exception Not_found ->
                    let spec_to : Flambda.specialised_to =
                      { var;
                        projection = None;
                      }
                    in
                    added_specialised_arg := true;
                    Variable.Map.add param spec_to specialised_args
                  | _spec_to ->
                    (* This parameter is already specialised. *)
                    specialised_args)
              new_specialised_args
              Variable.Map.empty
          in
          if not !added_specialised_arg then begin
            specialisations
          end else begin
            assert (not (Continuation.Map.mem cont specialisations));
            Continuation.Map.add cont specialised_args specialisations
          end)
    (R.continuation_definitions_with_uses r)
    Continuation_with_args.Map.empty
