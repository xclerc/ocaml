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

(* CR-someday mshinwell: If we can get the types in [Flambda] to be uniform
   enough between functions and continuations then we can probably share
   code for doing remove-unused-parameters. *)

let remove_parameters ~cont ~(handler : Flambda.continuation_handler)
        ~to_remove =
(*
Format.eprintf "Removing parameters %a from continuation %a, handler %a\n%!"
  Variable.Set.print to_remove Continuation.print cont
  Flambda.print_let_cont_handlers (Flambda.Recursive (
    Continuation.Map.of_list [cont, handler]));
*)
  let freshened_params =
    List.map (fun param -> param, Variable.rename param) handler.params
  in
  let wrapper_params =
    List.map (fun (_param, freshened_param) -> freshened_param)
      freshened_params
  in
  let wrapper_params_not_unused =
    Misc.Stdlib.List.filter_map (fun (param, freshened_param) ->
        if Variable.Set.mem param to_remove then None
        else Some freshened_param)
      freshened_params
  in
  let new_params =
    List.filter (fun param -> not (Variable.Set.mem param to_remove))
      handler.params
  in
  let freshening = Variable.Map.of_list freshened_params in
  let freshen param =
    match Variable.Map.find param freshening with
    | param -> param
    | exception Not_found -> assert false
  in
  let new_specialised_args =
    Flambda_utils.clean_specialised_args_projections (
      Variable.Map.filter (fun param _spec_to ->
          not (Variable.Set.mem param to_remove))
        handler.specialised_args)
  in
  let wrapper_specialised_args =
    Variable.Map.fold (fun var (spec_to : Flambda.specialised_to)
            wrapper_specialised_args ->
        let var = freshen var in
        let projection =
          Misc.Stdlib.Option.map (fun projection ->
              Projection.map_projecting_from projection ~f:(fun from ->
                freshen from))
            spec_to.projection
        in
        let spec_to : Flambda.specialised_to =
          { var = spec_to.var;
            projection;
          }
        in
        Variable.Map.add var spec_to wrapper_specialised_args)
      handler.specialised_args
      Variable.Map.empty
  in
  let new_cont = Continuation.create () in
  let wrapper_handler : Flambda.continuation_handler =
    { params = wrapper_params;
      stub = true;
      is_exn_handler = false;
      handler = Apply_cont (new_cont, None, wrapper_params_not_unused);
      specialised_args = wrapper_specialised_args;
    }
  in
  assert (not handler.is_exn_handler);
  let new_handler =
    Variable.Set.fold (fun param body ->
        Flambda.create_let param (Const (Const_pointer 0)) body)
      to_remove
      handler.handler
  in
  let new_handler : Flambda.continuation_handler =
    { params = new_params;
      stub = handler.stub;
      is_exn_handler = false;
      handler = new_handler;
      specialised_args = new_specialised_args;
    }
  in
  Continuation.Map.add new_cont new_handler
    (Continuation.Map.add cont wrapper_handler Continuation.Map.empty)

let for_continuation ~body ~(handlers : Flambda.continuation_handlers)
      ~original ~backend : Flambda.expr =
  let unused =
    Invariant_params.Continuations.unused_arguments handlers ~backend
  in
  if Variable.Set.is_empty unused then
    original
  else
    let handlers =
      Continuation.Map.fold (fun cont
              (handler : Flambda.continuation_handler) handlers ->
          let to_remove =
            Variable.Set.inter unused (Variable.Set.of_list handler.params)
          in
          if Variable.Set.is_empty to_remove then
            Continuation.Map.add cont handler handlers
          else
            Continuation.Map.disjoint_union handlers
              (remove_parameters ~cont ~handler ~to_remove))
        handlers
        Continuation.Map.empty
    in
    (* Note that the worker-wrapper transformation always produces
       mutually-recursive continuations. *)
    Let_cont { body; handlers = Recursive handlers; }

let run program ~backend =
  Flambda_iterators.map_exprs_at_toplevel_of_program program ~f:(fun expr ->
    Flambda_iterators.map_expr (fun (expr : Flambda.expr) ->
        match expr with
        | Let_cont { body = _; handlers = Nonrecursive { name = _; handler = {
            is_exn_handler = true; _ }; }; } -> expr
        | Let_cont { body; handlers = Nonrecursive { name; handler; } } ->
          let handlers =
            Continuation.Map.add name handler Continuation.Map.empty
          in
          for_continuation ~body ~handlers ~original:expr ~backend
        | Let_cont { body; handlers = Recursive handlers; } ->
          for_continuation ~body ~handlers ~original:expr ~backend
        | Let_cont { handlers = Alias _; _ }
        | Let _ | Let_mutable _ | Apply _ | Apply_cont _ | Switch _
        | Proved_unreachable -> expr)
      expr)

