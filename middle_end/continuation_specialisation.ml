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

module Continuation_with_specialised_args = struct
  (* A continuation together with, for each of its specialised arguments, the
     variable corresponding to such argument in a particular application of
     that continuation.
  *)
  type t = Continuation.t * Flambda.specialised_args

  include Identifiable.Make (struct
    type nonrec t = t

    let compare t1 t2 =
      let c = Continuation.compare (fst t1) (fst t2) in
      if c <> 0 then c
      else
        (Variable.Map.compare Flambda.compare_specialised_to) (snd t1) (snd t2)

    let equal t1 t2 =
      compare t1 t2 = 0

    let hash t =
      Hashtbl.hash (Continuation.hash (fst t),
        Hashtbl.hash (Variable.Map.bindings (snd t)))

    let output _chan _t = Misc.fatal_error "not implemented"
    let print _ppf _t = Misc.fatal_error "not implemented"
  end)
end

type specialising_result =
  | Didn't_specialise
  | Specialised of {
      old_cont : Continuation.t;
      new_cont : Continuation.t;
      new_handlers : Flambda.continuation_handlers;
    }

(* This function constructs a suitable environment for simplification of a
   continuation's body that is eligible for specialisation.  The freshening
   of the body is performed during the simplification.
   If the continuation is defined simultaneously with others, all of the
   bodies will be simplified; specialised argument information may be
   introduced for continuations apart from the starting point (called [cont])
   using the invariant parameters flow information.
   (We deal with continuation bodies individually, rather than simplifying an
   entire [Let_cont] / [Apply_cont] pair, because we don't have to hand values
   for any non-specialised arguments of the continuation [cont].  There may
   have been multiple application points.)
*)
let try_specialising ~cont ~(old_handlers : Flambda.continuation_handlers)
      ~(newly_specialised_args : Flambda.specialised_args) ~env ~simplify
      ~backend : specialising_result =
  let invariant_params_flow =
    Invariant_params.Continuations.invariant_param_sources old_handlers
      ~backend
  in
  let freshening = Freshening.activate (E.freshening env) in
  let new_conts, freshening =
    Continuation.Map.fold (fun cont _handler (new_conts, freshening) ->
        let new_cont, freshening =
          Freshening.add_static_exception freshening cont
        in
        let new_conts =
          Continuation.Map.add cont new_cont new_conts
        in
        new_conts, freshening)
      old_handlers
      (Continuation.Map.empty, freshening)
  in
  let env =
    E.set_freshening env freshening
  in
  let entry_point_cont = cont in
  let new_handlers, total_benefit =
    Continuation.Map.fold (fun cont old_handler benefit ->
        let params, freshening =
          Freshening.add_variables' freshening old_handler.params
        in
        let env = E.set_freshening env freshening in
        let new_cont_approx =
          Continuation_approx.create_unknown ~name:new_cont
            ~num_params:(List.length params)
        in
        let env = E.add_continuation env new_cont new_cont_approx in
        let wrong_spec_args =
          Variable.Set.inter (Variable.Map.keys old_handler.specialised_args)
            (Variable.Map.keys newly_specialised_args)
        in
        if not (Variable.Set.is_empty wrong_spec_args) then begin
          Misc.fatal_errorf "These parameters of continuation %a have already \
              been specialised: %a"
            Continuation.print cont
            Variable.Set.print wrong_spec_args
        end;
        let env =
          (* Add approximations for parameters including existing specialised
             args (and projection information even for non-specialised args). *)
          List.fold_left (fun env param ->
              let param' = Freshening.apply_variable freshening param in
              match Variable.Map.find param old_handler.specialised_args with
              | exception Not_found ->
                if Variable.Map.mem param newly_specialised_args then
                  env
                else
                  E.add env param' (A.value_unknown Other)
              | { var; projection; } ->
                let env =
                  match projection with
                  | None -> env
                  | Some projection ->
                    E.add_projection env ~projection ~bound_to:param'
                in
                match var with
                | None -> env
                | Some var ->
                  match E.find_opt env var with
                  | Some approx -> E.add env param' approx
                  | None ->
                    Misc.fatal_errorf "Existing parameter %a of continuation \
                        %a is specialised to variable %a which does not exist \
                        in the environment: %a"
                      Variable.print param
                      Continuation.print cont
                      Variable.print var
                      E.print env)
            env
            old_handler.params
        in
        let env =
          (* Add approximations for newly-specialised args.  These are either:
             (a) those arising from the "entry point" (i.e. [Apply_cont] of
                 [entry_point_cont]); or
             (b) those arising from invariant parameters flow from the entry
                 point's continuation handler. *)
          let newly_specialised_args =
            if Continuation.equal cont entry_point_cont then
              newly_specialised_args
            else
              Variable.Map.fold (fun param (spec_to : Flambda.specialised_to)
                      newly_specialised_args ->
                  match Variable.Map.find param invariant_params_flow with
                  | exception Not_found -> newly_specialised_args
                  | flows_to ->
                    Variable.Set.fold (fun (cont', param')
                            newly_specialised_args ->
                        if not (Continuation.equal cont cont') then
                          newly_specialised_args
                        else
                          Variable.Map.add param' spec_to
                            newly_specialised_args)
                      flows_to)
                newly_specialised_args
                Variable.Map.empty
          in
          Variable.Map.fold (fun param (spec_to : Flambda.specialised_to) env ->
              let param' = Freshening.apply_variable freshening param in
              let env =
                match spec_to.projection with
                | None -> env
                | Some projection ->
                  E.add_projection env ~projection ~bound_to:param'
              in
              match spec_to.var with
              | None ->
                Misc.fatal_errorf "Parameter %a of continuation %a is claimed \
                    to be a newly-specialised argument but it has no variable \
                    equality"
                  Variable.print param
                  Continuation.print cont
              | Some var ->
                match E.find_opt env var with
                | Some approx -> E.add env param' approx
                | None ->
                  Misc.fatal_errorf "Attempt to specialise parameter %a of \
                      continuation %a to variable %a which does not exist in \
                      the environment: %a"
                    Variable.print param
                    Continuation.print cont
                    Variable.print var
                    E.print env)
            newly_specialised_args
            env
        in
        let r = R.create () in
        let env = E.activate_freshening (E.set_never_inline env) in
        let new_handler, r = simplify env r old_handler.handler in
        let total_benefit = B.(+) (R.benefit r) total_benefit in
        let specialised_args =
          Variable.Map.disjoint_union old_handler.specialised_args
            newly_specialised_args
        in
        let new_handler : Flambda.continuation_handler =
          { params;
            stub = old_handler.stub;
            handler = new_handler;
            specialised_args;
          }
        in
        let new_handlers =
          Continuation.Map.add cont new_handler new_handlers
        in
        new_handlers, total_inlining_benefit)
    old_handlers
    (Continuation.Map.empty, B.zero)
  in
  let module W = Inlining_cost.Whether_sufficient_benefit in
  let wsb =
    let originals =
      List.map (fun (handler : Flambda.continuation_handler) ->
          handler.handler)
        (Continuation.Map.data old_handlers)
    in
    let new_handlers =
      List.map (fun (handler : Flambda.continuation_handler) ->
          handler.handler)
        (Continuation.Map.data new_handlers)
    in
    W.create_list ~originals
      ~toplevel:(E.at_toplevel env)
      ~branch_depth:(E.branch_depth env)
      new_handlers
      ~benefit:inlining_benefit
      ~lifting:false
      ~round:(E.round env)
  in
  if W.evaluate wsb then
    let old_cont = cont in
    let new_cont = Freshening.apply_static_exception freshening old_cont in
    Specialised {
      old_cont;
      new_cont;
      new_handlers;
    }
  else
    Didn't_specialise

let find_specialisations r ~simplify ~backend =
  let module N = Num_continuation_uses in
  let module U = Inline_and_simplify_aux.Continuation_uses in
  (* The first step constructs two maps.  The first of these is:
          (continuation * (specialised_params -> arg))
       -> set of (continuation * args)
     which groups together uses of the continuation where some subset of
     its invariant parameters have the same arguments across those uses.  The
     range of the map enables identification of the corresponding [Apply_cont]
     nodes which will need to be repointed if the continuation is specialised
     for those uses.
     The second map just maps continuations to their handlers (including any
     handlers defined simultaneously) and the environment of definition. *)
  let specialisations, conts_to_handlers =
    (* CR mshinwell: [recursive] appears to be redundant with
       [approx.recursive] *)
    Continuation.Map.fold (fun cont (uses, approx, env, _recursive)
          ((specialisations, conts_to_handlers) as acc) ->
        match Continuation_approx.handlers approx with
        | None ->
          (* Applications of continuations inside their own handlers will
             hit this case.  This is equivalent to the "self call" check
             in [Inlining_decision]. *)
          acc
        | Some (Nonrecursive _) -> acc
        | Some (Recursive handlers) ->
          let invariant_params =
            Invariant_params.Continuations.invariant_params_in_recursion
              handlers ~backend
          in
          let handler =
            match Continuation.Map.find cont handlers with
            | handler -> handler
            | exception Not_found ->
              Misc.fatal_errorf "Continuation %a not found in handler map \
                  inside the approximation"
                Continuation.print cont
          in
          List.fold_left (fun ((specialisations, conts_to_handlers) as acc)
                  (use : U.Use.t) ->
              assert (List.length handler.params = List.length use.args);
              let params_with_args =
                Variable.Map.of_list (List.combine handler.params use.args)
              in
              let params_with_specialised_args =
                Variable.Map.filter (fun param (_arg, arg_approx) ->
                    Variable.Map.mem param invariant_params
                      && not (Variable.Map.mem param
                        handler.specialised_args)
                      && A.useful arg_approx)
                  params_with_args
              in
              if Variable.Map.cardinal params_with_specialised_args < 1 then
                acc
              else
                let params_with_specialised_args =
                  Variable.Map.map (fun (arg, _) : Flambda.specialised_to ->
                      { var = Some arg;
                        projection = None;
                      })
                    params_with_specialised_args
                in
                let key : Continuation_with_specialised_args.t =
                  cont, params_with_specialised_args
                in
                let uses =
                  match
                    Continuation_with_specialised_args.Map.find key
                      specialisations
                  with
                  | exception Not_found -> Continuation.With_args.Set.empty
                  | uses -> uses
                in
                let use_args =
                  List.map (fun (arg, _approx) -> arg) use.args
                in
                let specialisations =
                  Continuation_with_specialised_args.Map.add key
                    (Continuation.With_args.Set.add (cont, use_args) uses)
                    specialisations
                in
                let conts_to_handlers =
                  Continuation.Map.add cont (handlers, env) conts_to_handlers
                in
                specialisations, conts_to_handlers)
            (specialisations, conts_to_handlers)
            (U.inlinable_application_points uses))
      (R.continuation_definitions_with_uses r)
      (Continuation_with_specialised_args.Map.empty,
        Continuation.Map.empty)
  in
  (* The second step takes the map from above and makes a decision for
     each proposed specialisation, returning two maps:
       continuation "k" -> new continuation(s) to be defined just before "k"
       (continuation * args) -> new continuation
     The first map is then used to add new [Let_cont] definitions and the
     second is used to rewrite [Apply_cont] to specialised continuations. *)
  Continuation_with_specialised_args.Map.fold (fun
          (cont, newly_specialised_args)
          cont_application_points ((new_conts, apply_cont_rewrites) as acc) ->
      let old_handlers, env =
        match Continuation.Map.find cont conts_to_handlers with
        | exception Not_found -> assert false  (* see above *)
        | old_handlers -> old_handlers
      in
      match
        try_specialising ~cont ~old_handlers ~newly_specialised_args
          ~env ~simplify ~backend
      with
      | Didn't_specialise -> acc
      | Specialised { old_cont; new_cont; new_handlers; } ->
        let existing_conts =
          match Continuation.Map.find old_cont new_conts with
          | exception Not_found -> []
          | existing_conts -> existing_conts
        in
        let new_conts =
          Continuation.Map.add old_cont (new_handlers :: existing_conts)
            new_conts
        in
        let apply_cont_rewrites =
          Continuation.With_args.Set.fold (fun ((cont', _args) as key)
                  apply_cont_rewrites ->
              assert (Continuation.equal cont cont');
              assert (not (Continuation.With_args.Map.mem key
                apply_cont_rewrites));
              Continuation.With_args.Map.add key new_cont apply_cont_rewrites)
            cont_application_points
            apply_cont_rewrites
        in
        new_conts, apply_cont_rewrites)
    specialisations
    (Continuation.Map.empty, Continuation.With_args.Map.empty)

let insert_specialisations (expr : Flambda.expr) ~new_conts
        ~apply_cont_rewrites =
  Flambda_iterators.map_toplevel_expr (fun (expr : Flambda.t) ->
      match expr with
      | Let_cont { name; _ } ->
        begin match Continuation.Map.find name new_conts with
        | exception Not_found -> expr
        | new_conts ->
          List.fold_left (fun body handlers : Flambda.expr ->
              Let_cont {
                body;
                handlers = Recursive handlers;
              })
            expr
            new_conts
        end
      | Apply_cont (cont, trap_action, args) ->
        let key = cont, args in
        begin match Continuation.With_args.Map.find key apply_cont_rewrites with
        | exception Not_found -> expr
        | new_cont ->
          assert (trap_action = None);
          Apply_cont (new_cont, None, args)
        end
      | Apply _ | Let _ | Let_mutable _ | Switch _ | Proved_unreachable -> expr)
    expr

let for_toplevel_expression expr r ~simplify ~backend =
  let new_conts, apply_cont_rewrites =
    find_specialisations r ~simplify ~backend
  in
  insert_specialisations expr ~new_conts ~apply_cont_rewrites
