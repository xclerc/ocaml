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
      ~(set_of_closures : Flambda.Set_of_closures.t)
      ~function_decls ~freshen
      ~(only_for_function_decl : Flambda.Function_declaration.t option) =
  let free_vars =
    Variable.Map.map (fun (external_var : Flambda.Free_var.t) ->
        let var =
          let var =
            Freshening.apply_variable (E.freshening env) external_var.var
          in
          (* XXX This should use [reify], since there's an advantage if that
             works: removing a free variable. *)
          match
            T.follow_variable_equality (E.find_exn env var)
              ~is_present_in_env:(fun var -> E.mem env var)
          with
          | None -> var
          | Some var -> var
        in
        let ty = E.find_exn env var in
        var, approx)
      set_of_closures.free_vars
  in
  let environment_before_cleaning = env in
  (* [E.local] helps us to catch bugs whereby variables escape their scope. *)
  let env = E.local env in
  let free_vars, function_decls, sb, freshening =
    Freshening.apply_function_decls_and_free_vars (E.freshening env) free_vars
      function_decls ~only_freshen_parameters:(not freshen)
  in
  let env = E.set_freshening env sb in
  let specialised_args =
    Variable.Map.map_keys (Freshening.apply_variable (E.freshening env))
      specialised_args
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
  free_vars, specialised_args, function_decls,
    internal_value_set_of_closures, set_of_closures_env

let prepare_to_simplify_closure ~(function_decl : Flambda.Function_declaration.t)
      ~free_vars ~specialised_args ~set_of_closures_env =
  let closure_env =
    Variable.Map.fold (fun inner_var (_outer_var, ty) env ->
        E.add_outer_scope env inner_var ty)
      free_vars set_of_closures_env
  in
  (* CR mshinwell: Freshening?  And cleaning? *)
  List.fold_left (fun env param ->
      let var = Parameter.var param in
      let ty = Parameter.ty param in
      let env = E.add env var ty in
      match T.projection ty with
      | None -> env
      | Some projection ->
        E.add_projection env ~projection ~bound_to:var)
    env function_decl.params

module C = Inlining_cost

external swap16 : int -> int = "%bswap16"
external swap32 : int32 -> int32 = "%bswap_int32"
external swap64 : int64 -> int64 = "%bswap_int64"
external swapnative : nativeint -> nativeint = "%bswap_native"

let const_int_expr expr n =
  if Effect_analysis.no_effects_named expr then
    let (new_expr, approx) = T.make_const_int_named n in
    new_expr, approx, C.Benefit.remove_code_named expr C.Benefit.zero
  else expr, T.value_int n, C.Benefit.zero
let const_char_expr expr c =
  if Effect_analysis.no_effects_named expr then
    let (new_expr, approx) = T.make_const_char_named c in
    new_expr, approx, C.Benefit.remove_code_named expr C.Benefit.zero
  else expr, T.value_char c, C.Benefit.zero
let const_ptr_expr expr n =
  if Effect_analysis.no_effects_named expr then
    let (new_expr, approx) = T.make_const_ptr_named n in
    new_expr, approx, C.Benefit.remove_code_named expr C.Benefit.zero
  else expr, T.value_constptr n, C.Benefit.zero
let const_bool_expr expr b =
  const_ptr_expr expr (if b then 1 else 0)
let const_float_expr expr f =
  if Effect_analysis.no_effects_named expr then
    let (new_expr, approx) = T.make_const_float_named f in
    new_expr, approx, C.Benefit.remove_code_named expr C.Benefit.zero
  else expr, T.value_boxed_float f, C.Benefit.zero
let const_boxed_int_expr expr t i =
  if Effect_analysis.no_effects_named expr then
    let (new_expr, approx) = T.make_const_boxed_int_named t i in
    new_expr, approx, C.Benefit.remove_code_named expr C.Benefit.zero
  else expr, T.value_boxed_int t i, C.Benefit.zero

let const_comparison_expr expr (cmp : Lambda.comparison) x y =
  (* Using the [Pervasives] comparison functions here in the compiler
     coincides with the definitions of such functions in the code
     compiled by the user, and is thus correct. *)
  const_bool_expr expr
    (match cmp with
     | Ceq -> x = y
     | Cneq -> x <> y
     | Clt -> x < y
     | Cgt -> x > y
     | Cle -> x <= y
     | Cge -> x >= y)

let freshen_and_squash_aliases env var =
  let var = Freshening.apply_variable (E.freshening env) var in
  let ty = E.find_exn env var in
  (* CR mshinwell: Shouldn't the variable always be in the env now? *)
  match T.follow_variable_equality ty ~is_present_in_env:(E.mem env) with
  | None -> var, ty
  | Some var -> var, ty

let freshen_and_squash_aliases_list env vars =
  List.map (fun var -> freshen_and_squash_aliases env var) vars

let simpler_equivalent_term env r original_named ty
      : (Variable.t * Flambda.Named.t) list * Flambda.Reachable.t * R.t =
  if not (Effect_analysis.no_effects_named original_named) then
    [], Flambda.Reachable.reachable original_named, r
  else
    let importer = E.importer env in
    match T.reify_using_env ~importer ty ~is_present_in_env:(E.mem env) with
    | None -> [], Flambda.Reachable.reachable original_named, r
    | Some named ->
      let r = R.map_benefit r (B.remove_code_named original_named) in
      [], Flambda.Reachable.reachable named, r
