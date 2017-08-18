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

(** Command line argument -inline *)
val initial_inlining_threshold : round:int -> Inlining_cost.Threshold.t

(** Command line argument -inline-toplevel *)
val initial_inlining_toplevel_threshold
  : round:int -> Inlining_cost.Threshold.t

val prepare_to_simplify_set_of_closures
   : env:Env.t
  -> set_of_closures:Flambda.set_of_closures
  -> function_decls:Flambda.function_declarations
  -> freshen:bool
  -> only_for_function_decl:Flambda.function_declaration option
  -> (Flambda.free_var * Simple_value_approx.t) Variable.Map.t  (* fvs *)
    * Flambda.specialised_to Variable.Map.t         (* specialised arguments *)
    * Flambda.function_declarations
    * Simple_value_approx.t Variable.Map.t       (* parameter approximations *)
    * Simple_value_approx.value_set_of_closures
    * Env.t

val prepare_to_simplify_closure
   : function_decl:Flambda.function_declaration
  -> free_vars:(Flambda.free_var * Simple_value_approx.t) Variable.Map.t
  -> specialised_args:Flambda.specialised_to Variable.Map.t
  -> parameter_approximations:Simple_value_approx.t Variable.Map.t
  -> set_of_closures_env:Env.t
  -> Env.t
