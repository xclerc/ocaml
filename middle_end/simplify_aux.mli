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
  -> set_of_closures:Flambda.Set_of_closures.t
  -> function_decls:Flambda.Function_declarations.t
  -> freshen:bool
  -> only_for_function_decl:Flambda.Function_declaration.t option
  -> (Flambda.Free_var.t * Flambda_type.t) Variable.Map.t  (* fvs *)
    * Flambda_type0.T.specialised_args
    * Flambda.Function_declarations.t
    * Flambda_type0.T.set_of_closures
    * Env.t

val prepare_to_simplify_closure
   : function_decl:Flambda.Function_declaration.t
  -> free_vars:(Flambda.Free_var.t * Flambda_type.t) Variable.Map.t
  -> specialised_args:Flambda_type0.T.specialised_args
  -> set_of_closures_env:Env.t
  -> Env.t
