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

module CAV = Invariant_params.Continuations.Continuation_and_variable
module R = Inline_and_simplify_aux.Result

(* CR mshinwell: Once working, consider sharing code with
   [Unbox_specialised_args]. *)

let for_continuations r ~body ~handlers ~original ~backend =
  let definitions_with_uses = R.continuation_definitions_with_uses r in
  let projections_by_cont =
    Continuation.Map.filter_map handlers
      ~f:(fun cont (handler : Flambda.continuation_handler) ->
        if handler.stub then
          None
        else
          match handler.params with
          | [] -> None
          | _ ->
            match Continuation.Map.find cont definitions_with_uses with
            | exception Not_found -> None
            | (uses, _approx, _env, _recursive) ->
              Some (Extract_projections.from_continuation ~uses ~handler))
  in
  if Continuation.Map.is_empty projections_by_cont then begin
    original
  end else begin
(*
    Format.eprintf "Projections:\n@;%a\n"
      (Continuation.Map.print Projection.Set.print) projections_by_cont;
*)
    let invariant_params_flow =
      Invariant_params.Continuations.invariant_param_sources handlers ~backend
    in
(*
Format.eprintf "Invariant params:\n@;%a\n"
  (Variable.Map.print
    Invariant_params.Continuations.Continuation_and_variable.Set.print)
    invariant_params_flow;
*)
    let projections_by_cont' =
      Continuation.Map.fold (fun cont projections projections_by_cont' ->
          Projection.Set.fold (fun projection projections_by_cont' ->
              let projecting_from = Projection.projecting_from projection in
              match Variable.Map.find projecting_from invariant_params_flow with
              | exception Not_found -> projections_by_cont'
              | flow ->
                CAV.Set.fold (fun (target_cont, target_arg)
                          projections_by_cont' ->
                    if Continuation.equal cont target_cont then
                      projections_by_cont'
                    else
                      let projection =
                        Projection.map_projecting_from projection
                          ~f:(fun var ->
                            assert (Variable.equal var projecting_from);
                            target_arg)
                      in
                      let new_args =
                        match
                          Continuation.Map.find target_cont projections_by_cont'
                        with
                        | exception Not_found -> Projection.Set.empty
                        | new_args -> new_args
                      in
                      let new_args =
                        Projection.Set.add projection new_args
                      in
                      Continuation.Map.add target_cont new_args
                        projections_by_cont')
                  flow
                  projections_by_cont')
            projections
            projections_by_cont')
        projections_by_cont
        Continuation.Map.empty
    in
    let projections_by_cont =
      Continuation.Map.union (fun _cont projs1 projs2 ->
          Some (Projection.Set.union projs1 projs2))
        projections_by_cont projections_by_cont'
    in
    let handlers =
      Continuation.Map.fold (fun cont projections new_handlers ->
          let handler : Flambda.continuation_handler =
            match Continuation.Map.find cont handlers with
            | exception Not_found -> assert false
            | handler -> handler
          in
          let new_cont = Continuation.create () in
          let params_freshening =
            List.map (fun param -> param, Variable.rename param) handler.params
          in
          let wrapper_params = List.map fst params_freshening in
          let params_freshening = Variable.Map.of_list params_freshening in
          let freshen_param param =
              match Variable.Map.find param params_freshening with
              | exception Not_found -> assert false
              | param -> param
          in
          let unboxings, specialised_args =
            Projection.Set.fold (fun projection (unboxings, specialised_args) ->
                let param = Projection.projecting_from projection in
                let spec_to : Flambda.specialised_to =
                  { var = None;
                    projection = Some projection;
                  }
                in
                let new_param = Variable.rename ~append:"_unboxed" param in
                let unboxings = new_param::unboxings in
                let specialised_args =
                  Variable.Map.add new_param spec_to specialised_args
                in
                unboxings, specialised_args)
              projections
              ([], handler.specialised_args)
          in
          let wrapper_specialised_args =
            Variable.Map.fold (fun param (spec_to : Flambda.specialised_to)
                    wrapper_specialised_args ->
                let param = freshen_param param in
                let projection =
                  match spec_to.projection with
                  | None -> None
                  | Some projection ->
                    Some (Projection.map_projecting_from projection
                      ~f:(fun param -> freshen_param param))
                in
                let spec_to : Flambda.specialised_to =
                  { var = Misc.Stdlib.Option.map freshen_param spec_to.var;
                    projection;
                  }
                in
                Variable.Map.add param spec_to wrapper_specialised_args)
              specialised_args
              Variable.Map.empty
          in
          let wrapper_unboxings =
            Projection.Set.fold (fun projection wrapper_unboxings ->
                let param = Projection.projecting_from projection in
                let wrapper_unboxing =
                  Variable.rename ~append:"_unboxed" param
                in
                (projection, wrapper_unboxing)::wrapper_unboxings)
              projections
              []
          in
          let wrapper_body =
            let initial_body : Flambda.t =
              let wrapper_unboxings = List.map snd wrapper_unboxings in
              Apply_cont (new_cont, None, wrapper_params @ wrapper_unboxings)
            in
            List.fold_left (fun wrapper_body (projection, unboxing) ->
                let named = Flambda_utils.projection_to_named projection in
                Flambda.create_let unboxing named wrapper_body)
              initial_body
              wrapper_unboxings
          in
          let wrapper_handler : Flambda.continuation_handler =
            { params = wrapper_params;
              stub = true;
              is_exn_handler = false;
              handler = wrapper_body;
              specialised_args = wrapper_specialised_args;
            }
          in
          assert (not handler.is_exn_handler);
          let new_handler : Flambda.continuation_handler =
            { params = handler.params @ unboxings;
              stub = handler.stub;
              is_exn_handler = false;
              handler = handler.handler;
              specialised_args;
            }
          in
          Continuation.Map.add new_cont new_handler
            (Continuation.Map.add cont wrapper_handler new_handlers))
        projections_by_cont
        Continuation.Map.empty
    in
    (* CR mshinwell: make Nonrecursive when original handler was. *)
    let output : Flambda.expr =
    Let_cont {
      body;
      handlers = Recursive handlers;
    }
    in
    Format.eprintf "After unboxing:\n@;%a\n" Flambda.print output;
    output
  end

let run r expr ~backend =
Format.eprintf "Ready to unbox:\n@;%a\n" Flambda.print expr;
  Flambda_iterators.map_expr (fun (expr : Flambda.expr) ->
      match expr with
      | Let_cont { body = _; handlers = Nonrecursive { name = _; handler = {
          is_exn_handler = true; _ }; }; } -> expr
      | Let_cont { body; handlers = Nonrecursive { name; handler; } } ->
        let handlers =
          Continuation.Map.add name handler Continuation.Map.empty
        in
        for_continuations r ~body ~handlers ~original:expr ~backend
      | Let_cont { body; handlers = Recursive handlers; } ->
        for_continuations r ~body ~handlers ~original:expr ~backend
      | Let_cont { handlers = Alias _; _ }
      | Let _ | Let_mutable _ | Apply _ | Apply_cont _ | Switch _
      | Proved_unreachable -> expr)
    expr
