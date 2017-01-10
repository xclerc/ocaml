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

type specialising_result =
  | Didn't_specialise
  | Specialised of Continuation.t * Flambda.continuation_handler

let try_specialising ~cont ~(old_handler : Flambda.continuation_handler)
      ~specialised_args ~env ~simplify =
  let freshening =
    List.map (fun param -> param, Variable.rename param) handler.params
  in
  let subst = Variable.Map.of_list freshening in
  let handler =
    Flambda_utils.toplevel_substitution subst handler.handler
  in
  let params = List.map snd freshening in

let find_specialisations r ~simplify =
  let module N = Num_continuation_uses in
  let module U = Inline_and_simplify_aux.Continuation_uses in
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
          let invariant_params =
            Invariant_params.invariant_params_of_continuation cont handler
          in
          let specialised_args, added_specialised_arg =
            Variable.Set.fold (fun param
                    ((specialised_args, added_specialised_arg) as acc) ->
                match Variable.Map.find param specialised_args with
                | exception Not_found ->
                  (* This parameter is to be a newly-specialised argument. *)
                  let spec_to : Flambda.specialised_to =
                    { var;
                      projection = None;
                    }
                  in
                  Variable.Map.add param spec_to specialised_args, true
                | _spec_to ->
                  (* This parameter is already specialised. *)
                  acc)
              invariant_params
              (Variable.Map.empty, false)
          in
          if not added_specialised_arg then begin
            specialisations
          end else begin
            assert (not (Continuation.Map.mem cont specialisations));
            match
              try_specialising ~cont ~handler ~specialised_args ~env ~simplify
            with
            | Didn't_specialise -> specialisations
            | Specialised (new_cont, handler) ->
              Continuation.Map.add cont (new_cont, handler) specialisations
          end)
    (R.continuation_definitions_with_uses r)
    Continuation_with_args.Map.empty

let insert_specialisations (expr : Flambda.expr) ~specialisations =
  Flambda_iterators.map_toplevel_expr (fun (expr : Flambda.t) ->
      match expr with
      | Let_cont { name; body; _ } ->
        begin match Continuation.Map.find name specialisations with
        | exception Not_found -> expr
        | (new_cont, handler) ->
          (* Note that the continuation called [name] may be elided, since
             we don't specialise unless all uses of a given continuation are
             eligible for specialisation. *)
          Let_cont {
            name = new_cont;
            body;
            handler;
          }
        end
      | Apply_cont (cont, trap_action, args) ->
        begin match Continuation.Map.find cont specialisations with
        | exception Not_found -> expr
        | (new_cont, _handler) ->
          assert (trap_action = None);
          Apply_cont (new_cont, None, args)
        end
      | Apply _ | Let _ | Let_mutable _ | Switch _ | Proved_unreachable -> expr)
    expr

let for_toplevel_expression expr r ~simplify =
  let specialisations = find_specialisations r ~simplify in
