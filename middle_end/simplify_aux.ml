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

module E = Simplify_env
module T = Flambda_types

let prepare_to_simplify_set_of_closures ~env
      ~(set_of_closures : Flambda.set_of_closures)
      ~function_decls ~freshen
      ~(only_for_function_decl : Flambda.function_declaration option) =
  let free_vars =
    Variable.Map.map (fun (external_var : Flambda.free_var) ->
        let var =
          let var =
            Freshening.apply_variable (E.freshening env) external_var.var
          in
          match
            T.simplify_var_to_var_using_env (E.find_exn env var)
              ~is_present_in_env:(fun var -> E.mem env var)
          with
          | None -> var
          | Some var -> var
        in
        let approx = E.find_exn env var in
        (* The projections are freshened below in one step, once we know
           the closure freshening substitution. *)
        let projection = external_var.projection in
        ({ var; projection; } : Flambda.free_var), approx)
      set_of_closures.free_vars
  in
  let specialised_args =
    Variable.Map.filter_map set_of_closures.specialised_args
      ~f:(fun param (spec_to : Flambda.specialised_to) ->
        let keep =
          match only_for_function_decl with
          | None -> true
          | Some function_decl ->
            Variable.Set.mem param (Parameter.Set.vars function_decl.params)
        in
        if not keep then None
        else
          match spec_to.var with
          | Some external_var ->
            let var =
              Freshening.apply_variable (E.freshening env) external_var
            in
            let var =
              match
                T.simplify_var_to_var_using_env (E.find_exn env var)
                  ~is_present_in_env:(fun var -> E.mem env var)
              with
              | None -> var
              | Some var -> var
            in
            let projection = spec_to.projection in
            Some ({ var = Some var; projection; } : Flambda.specialised_to)
          | None ->
            Misc.fatal_errorf "No equality to variable for specialised arg %a"
              Variable.print param)
  in
  let environment_before_cleaning = env in
  (* [E.local] helps us to catch bugs whereby variables escape their scope. *)
  let env = E.local env in
  let free_vars, function_decls, sb, freshening =
    Freshening.apply_function_decls_and_free_vars (E.freshening env) free_vars
      function_decls ~only_freshen_parameters:(not freshen)
  in
  let env = E.set_freshening env sb in
  let free_vars =
    Freshening.freshen_free_vars_projection_relation' free_vars
      ~freshening:(E.freshening env)
      ~closure_freshening:(Some freshening)
  in
  let specialised_args =
    let specialised_args =
      Variable.Map.map_keys (Freshening.apply_variable (E.freshening env))
        specialised_args
    in
    Freshening.freshen_specialised_args_projection_relation specialised_args
      ~freshening:(E.freshening env)
      ~closure_freshening:(Some freshening)
  in
  let parameter_approximations =
    (* Approximations of parameters that are known to always hold the same
       argument throughout the body of the function. *)
    (* CR mshinwell: This next line might be a duplicate of a line above? *)
    Variable.Map.map_keys (Freshening.apply_variable (E.freshening env))
      (Variable.Map.mapi (fun param (spec_to : Flambda.specialised_to) ->
          match spec_to.var with
          | Some var -> E.find_exn environment_before_cleaning var
          | None ->
            Misc.fatal_errorf "No equality to variable for specialised arg %a"
              Variable.print param)
        specialised_args)
  in
  let direct_call_surrogates =
    Variable.Map.fold (fun existing surrogate surrogates ->
        let existing =
          Freshening.Project_var.apply_closure_id freshening
            (Closure_id.wrap existing)
        in
        let surrogate =
          Freshening.Project_var.apply_closure_id freshening
            (Closure_id.wrap surrogate)
        in
        assert (not (Closure_id.Map.mem existing surrogates));
        Closure_id.Map.add existing surrogate surrogates)
      set_of_closures.direct_call_surrogates
      Closure_id.Map.empty
  in
  let env =
    E.enter_set_of_closures_declaration env
      function_decls.set_of_closures_origin
  in
  (* we use the previous closure for evaluating the functions *)
  let internal_value_set_of_closures =
    let bound_vars =
      Variable.Map.fold (fun id (_, desc) map ->
          Var_within_closure.Map.add (Var_within_closure.wrap id) desc map)
        free_vars Var_within_closure.Map.empty
    in
    T.create_value_set_of_closures ~function_decls ~bound_vars
      ~invariant_params:(lazy Variable.Map.empty) ~specialised_args
      ~freshening ~direct_call_surrogates
  in
  (* Populate the environment with the approximation of each closure.
     This part of the environment is shared between all of the closures in
     the set of closures. *)
  let set_of_closures_env =
    Variable.Map.fold (fun closure _ env ->
        let approx =
          T.closure ~closure_var:closure
            (Closure_id.Map.singleton (Closure_id.wrap closure)
               internal_value_set_of_closures)
        in
        E.add env closure approx
      )
      function_decls.funs env
  in
  free_vars, specialised_args, function_decls, parameter_approximations,
    internal_value_set_of_closures, set_of_closures_env

(* This adds only the minimal set of approximations to the closures.
   It is not strictly necessary to have this restriction, but it helps
   to catch potential substitution bugs. *)
let populate_closure_approximations
      ~(function_decl : Flambda.function_declaration)
      ~(free_vars : (_ * T.t) Variable.Map.t)
      ~(parameter_approximations : T.t Variable.Map.t)
      ~set_of_closures_env =
  (* Add approximations of free variables *)
  let env =
    Variable.Map.fold (fun id (_, desc) env ->
        E.add_outer_scope env id desc)
      free_vars set_of_closures_env
  in
  (* Add known approximations of function parameters *)
  let env =
    List.fold_left (fun env id ->
        let approx =
          try Variable.Map.find id parameter_approximations
          with Not_found -> (T.unknown Other)
        in
        E.add env id approx)
      env (Parameter.List.vars function_decl.params)
  in
  env

let prepare_to_simplify_closure ~(function_decl : Flambda.function_declaration)
      ~free_vars ~specialised_args ~parameter_approximations
      ~set_of_closures_env =
  let closure_env =
    populate_closure_approximations ~function_decl ~free_vars
      ~parameter_approximations ~set_of_closures_env
  in
  (* Add definitions of known projections to the environment. *)
  let add_projections ~closure_env ~which_variables ~get_projection =
    Variable.Map.fold (fun inner_var param env ->
        match get_projection param with
        | None -> env
        | Some projection ->
          let from = Projection.projecting_from projection in
          if Variable.Set.mem from function_decl.free_variables then
            E.add_projection env ~projection ~bound_to:inner_var
          else
            env)
      which_variables
      closure_env
  in
  let closure_env =
    add_projections ~closure_env ~which_variables:specialised_args
      ~get_projection:(fun (spec_arg : Flambda.specialised_to) ->
        spec_arg.projection)
  in
  add_projections ~closure_env ~which_variables:free_vars
    ~get_projection:(fun ((fv : Flambda.free_var), _) -> fv.projection)
