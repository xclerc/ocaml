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
  | Specialised of Continuation.t * Flambda.continuation_handler

(* This function constructs a suitable environment for simplification of a
   continuation's body that is eligible for specialisation.  The freshening
   of the body is performed during the simplification. *)
let try_specialising ~cont ~(old_handler : Flambda.continuation_handler)
      ~(newly_specialised_args : Flambda.specialised_args) ~env ~simplify
      : specialising_result =
  let freshening = Freshening.activate (E.freshening env) in
  let params, freshening =
    Freshening.add_variables' freshening old_handler.params
  in
  let new_cont, freshening = Freshening.add_static_exception freshening cont in
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
    Misc.fatal_errorf "These parameters of continuation %a have already been \
        specialised: %a"
      Continuation.print cont
      Variable.Set.print wrong_spec_args
  end;
  let env =
    (* Add approximations for parameters including existing specialised args. *)
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
          match E.find_opt env var with
          | Some approx -> E.add env param' approx
          | None ->
            Misc.fatal_errorf "Existing parameter %a of continuation %a is \
                specialised to variable %a which does not exist in the \
                environment: %a"
              Variable.print param
              Continuation.print cont
              Variable.print var
              E.print env)
      env
      old_handler.params
  in
  let env =
    (* Add approximations for newly-specialised args. *)
    Variable.Map.fold (fun param (spec_to : Flambda.specialised_to) env ->
        let param' = Freshening.apply_variable freshening param in
        let env =
          match spec_to.projection with
          | None -> env
          | Some projection -> E.add_projection env ~projection ~bound_to:param'
        in
        match E.find_opt env spec_to.var with
        | Some approx -> E.add env param' approx
        | None ->
          Misc.fatal_errorf "Attempt to specialise parameter %a of \
              continuation %a to variable %a which does not exist in the \
              environment: %a"
            Variable.print param
            Continuation.print cont
            Variable.print spec_to.var
            E.print env)
      newly_specialised_args
      env
  in
  let r = R.create () in
  let new_handler, r = simplify env r old_handler.handler in
  let inlining_benefit = R.benefit r in
  let module W = Inlining_cost.Whether_sufficient_benefit in
  let wsb =
    W.create ~original:old_handler.handler
      ~toplevel:(E.at_toplevel env)
      ~branch_depth:(E.branch_depth env)
      new_handler
      ~benefit:inlining_benefit
      ~lifting:false
      ~round:(E.round env)
  in
  if W.evaluate wsb then
    let specialised_args =
      Variable.Map.disjoint_union old_handler.specialised_args
        newly_specialised_args
    in
    let new_handler : Flambda.continuation_handler =
      { params;
        recursive = old_handler.recursive;
        handler = new_handler;
        specialised_args;
      }
    in
    Specialised (new_cont, new_handler)
  else
    Didn't_specialise

let find_specialisations r ~simplify =
  let module N = Num_continuation_uses in
  let module U = Inline_and_simplify_aux.Continuation_uses in
  (* The first step constructs a map:
          (continuation * (specialised_params -> arg))
       -> set of (continuation * args)
     which groups together uses of the continuation where some subset of
     its invariant parameters have the same arguments across those uses.  The
     range of the map enables identification of the corresponding [Apply_cont]
     nodes which will need to be repointed if the continuation is specialised
     for those uses. *)
  let specialisations =
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
            let invariant_params =
              Invariant_params.invariant_params_of_continuation cont handler
            in
            List.fold_left (fun specialisations (use : U.Use.t) ->
                assert (List.length handler.params = List.length use.args);
                let params_with_args =
                  Variable.Map.of_list (List.combine handler.params use.args)
                in
                let params_with_specialised_args =
                  Variable.Map.filter (fun param (_arg, arg_approx) ->
                      Variable.Set.mem param invariant_params
                        && not (Variable.Map.mem param
                          handler.specialised_args)
                        && A.useful arg_approx)
                    params_with_args
                in
                if Variable.Map.cardinal params_with_specialised_args < 1 then
                  specialisations
                else
                  let params_with_specialised_args =
                    Variable.Map.map (fun (arg, _) : Flambda.specialised_to ->
                        { var = arg;
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
                  Continuation_with_specialised_args.Map.add key
                    (Continuation.With_args.Set.add (cont, use_args) uses)
                    specialisations)
              Continuation_with_specialised_args.Map.empty
              (U.inlinable_application_points uses))
      (R.continuation_definitions_with_uses r)
      Continuation_with_specialised_args.Map.empty
  in
  (* The second step takes the map from above and makes a decision for
     each proposed specialisation, returning two maps:
       continuation "k" -> new continuations to be defined just before "k"
       (continuation * args) -> new continuation
     The first map is then used to add new [Let_cont] definitions and the
     second is used to rewrite [Apply_cont] to specialised continuations. *)
  Continuation_with_specialised_args.Map.fold (fun
          (cont, newly_specialised_args)
          cont_application_points ((new_conts, apply_cont_rewrites) as acc) ->
      match
        try_specialising ~cont ~old_handler:handler ~newly_specialised_args
          ~env ~simplify
      with
      | Didn't_specialise -> acc
      | Specialised (new_cont, handler) ->
        let existing_conts =
          match Continuation.Map.find cont new_conts with
          | exception Not_found -> []
          | existing_conts -> existing_conts
        in
        let new_conts =
          Continuation.Map.add cont ((new_cont, handler) :: existing_conts)
            new_conts
        in
        let apply_cont_rewrites =
          Continuation_with_args.Set.fold (fun ((cont', args) as key)
                  apply_cont_rewrites ->
              assert (Continuation.equal cont cont');
              assert (not (Continuation.Map.mem key apply_cont_rewrites));
              Continuation.Map.add key new_cont apply_cont_rewrites)
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
          List.fold_left (fun body (new_cont, handler) ->
              Let_cont {
                name = new_cont;
                body;
                handler;
              })
            expr
            new_conts
        end
      | Apply_cont (cont, trap_action, args) ->
        begin match Continuation.Map.find cont apply_cont_rewrites with
        | exception Not_found -> expr
        | new_cont ->
          assert (trap_action = None);
          Apply_cont (new_cont, None, args)
        end
      | Apply _ | Let _ | Let_mutable _ | Switch _ | Proved_unreachable -> expr)
    expr

let for_toplevel_expression expr r ~simplify =
  let new_conts, apply_cont_rewrites = find_specialisations r ~simplify in
  insert_specialisations expr ~new_conts ~apply_cont_rewrites
