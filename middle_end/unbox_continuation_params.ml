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

module H = Unbox_one_variable.How_to_unbox
module CAV = Invariant_params.Continuations.Continuation_and_variable
module R = Inline_and_simplify_aux.Result

let find_unboxings ~continuation_uses ~handlers =
  Continuation.Map.filter_map handlers
    ~f:(fun cont (handler : Flambda.continuation_handler) ->
      if handler.stub then
        None
      else
        match handler.params with
        | [] -> None
        | params ->
          match Continuation.Map.find cont continuation_uses with
          | exception Not_found ->
Format.eprintf "No definition for %a\n%!" Continuation.print cont;
            None
          | uses ->
            let num_params = List.length params in
            let args_approxs =
              Inline_and_simplify_aux.Continuation_uses.meet_of_args_approxs
                uses ~num_params
            in
            let params_to_approxs =
              Variable.Map.of_list (List.combine params args_approxs)
            in
            let unboxings =
              Variable.Map.filter_map params_to_approxs
                ~f:(fun param approx ->
                  Unbox_one_variable.how_to_unbox ~being_unboxed:param
                    ~being_unboxed_approx:approx)
            in
            if Variable.Map.is_empty unboxings then None
            else Some unboxings)

(* CR mshinwell: If we get everything using [Unbox_one_variable] then
   this function should be able to move to [Invariant_params] *)
let propagate_invariant_params_flow ~handlers ~backend ~unboxings_by_cont =
  let invariant_params_flow =
    Invariant_params.Continuations.invariant_param_sources handlers ~backend
  in
Format.eprintf "Invariant params:\n@;%a\n"
(Variable.Map.print
  Invariant_params.Continuations.Continuation_and_variable.Set.print)
  invariant_params_flow;
  let unboxings_by_cont' =
    Continuation.Map.fold (fun cont unboxings_by_param unboxings_by_cont' ->
        Variable.Map.fold (fun param unboxing unboxings_by_cont' ->
            match Variable.Map.find param invariant_params_flow with
            | exception Not_found -> unboxings_by_cont'
            | flow ->
              CAV.Set.fold (fun (target_cont, target_param)
                      unboxings_by_cont' ->
                  if Continuation.equal cont target_cont then
                    unboxings_by_cont'
                  else
                    let target_unboxings =
                      match
                        Continuation.Map.find target_cont unboxings_by_cont'
                      with
                      | exception Not_found -> Variable.Map.empty
                      | target_unboxings -> target_unboxings
                    in
                    Continuation.Map.add target_cont
                      (Variable.Map.add target_param unboxing
                        target_unboxings)
                      unboxings_by_cont')
                flow
                unboxings_by_cont')
          unboxings_by_param
          unboxings_by_cont')
      unboxings_by_cont
      Continuation.Map.empty
  in
  Continuation.Map.union (fun _cont unboxings1 unboxings2 ->
      Some (Variable.Map.disjoint_union unboxings1 unboxings2))
    unboxings_by_cont unboxings_by_cont'

let for_continuations r ~handlers ~backend =
Format.eprintf "Unbox_continuation_params starting with continuations %a\n%!"
  Continuation.Set.print (Continuation.Map.keys handlers);
  let continuation_uses = R.continuation_uses r in
  let unboxings_by_cont = find_unboxings ~continuation_uses ~handlers in
  if Continuation.Map.is_empty unboxings_by_cont then begin
    None
  end else begin
    let unboxings_by_cont =
      propagate_invariant_params_flow ~handlers ~backend ~unboxings_by_cont
    in
    let with_wrappers =
      Continuation.Map.fold (fun cont unboxings new_handlers ->
          let handler : Flambda.continuation_handler =
            match Continuation.Map.find cont handlers with
            | exception Not_found -> assert false
            | handler -> handler
          in
          let new_cont = Continuation.create () in
          let how_to_unbox = H.merge_variable_map unboxings in
          let _wrapper_params_map, wrapper_params, wrapper_specialised_args =
            Flambda_utils.create_wrapper_params ~params:handler.params
              ~specialised_args:handler.specialised_args
              ~freshening_already_assigned:(how_to_unbox.
                being_unboxed_to_wrapper_params_being_unboxed)
          in
          let specialised_args =
            Variable.Map.disjoint_union handler.specialised_args
              (H.new_specialised_args how_to_unbox)
          in
          let wrapper_body =
            let initial_body : Flambda.t =
              Apply_cont (new_cont, None,
                wrapper_params
                  @ how_to_unbox.new_arguments_for_call_in_wrapper)
            in
            how_to_unbox.add_bindings_in_wrapper initial_body
          in
          assert (not handler.is_exn_handler);
          let with_wrapper : Flambda_utils.with_wrapper =
            let params =
              handler.params
                @ (List.map (fun (param, _proj) -> param)
                  how_to_unbox.new_params)
            in
Format.eprintf "Unbox_continuation_params has unboxed:\n@;%a\n%!"
  Flambda.print_let_cont_handlers (Flambda.Recursive
    (Continuation.Map.add cont handler Continuation.Map.empty));
Format.eprintf "Unboxed version has \
    wrapper (params %a)\n@ %a = %a\n@ and new handler (params %a):\n@ %a = %a\n%!"
  Variable.print_list wrapper_params
  Continuation.print cont
  Flambda.print wrapper_body
  Variable.print_list params
  Continuation.print new_cont
  Flambda.print handler.handler;
            With_wrapper {
              new_cont;
              new_handler = {
                params;
                stub = handler.stub;
                is_exn_handler = false;
                handler = handler.handler;
                specialised_args;
              };
              wrapper_handler = {
                params = wrapper_params;
                stub = true;
                is_exn_handler = false;
                handler = wrapper_body;
                specialised_args = wrapper_specialised_args;
              };
            }
          in
          Continuation.Map.add cont with_wrapper new_handlers)
        unboxings_by_cont
        Continuation.Map.empty
    in
    Some with_wrappers
  end

let for_non_recursive_continuation r ~name ~handler ~backend
      : Flambda_utils.with_wrapper =
  let handlers =
    Continuation.Map.add name handler Continuation.Map.empty
  in
  let result = for_continuations r ~handlers ~backend in
  match result with
  | None -> Unchanged { handler; }
  | Some wrappers ->
    match Continuation.Map.bindings wrappers with
    | [name', with_wrapper] ->
      assert (Continuation.equal name name');
      with_wrapper
    | _ -> assert false

let for_recursive_continuations r ~handlers ~backend =
  let result = for_continuations r ~handlers ~backend in
  match result with
  | None ->
    Continuation.Map.map (fun handler : Flambda_utils.with_wrapper ->
          Unchanged { handler; })
      handlers
  | Some with_wrappers -> with_wrappers
