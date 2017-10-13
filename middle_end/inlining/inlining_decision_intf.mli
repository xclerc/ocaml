(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

(* CR-someday mshinwell: name of this source file could now be improved *)

type 'a by_copying_function_body =
     env:Simplify_env.t
  -> r:Simplify_result.t
  -> clos:Flambda.Function_declarations.t
  -> lfunc:Flambda.Expr.t
  -> fun_id:Closure_id.t
  -> func:Flambda.Function_declaration.t
  -> args:Flambda.Expr.t list
  -> Flambda.Expr.t * Simplify_result.t

type 'a by_copying_function_declaration =
     env:Simplify_env.t
  -> r:Simplify_result.t
  -> funct:Flambda.Expr.t
  -> clos:Flambda.Function_declarations.t
  -> fun_id:Closure_id.t
  -> func:Flambda.Function_declaration.t
  -> args_with_approxs:(Flambda.Expr.t list) * (Flambda_type.t list)
  -> invariant_params:Variable.Set.t
  -> specialised_args:Variable.Set.t
  -> dbg:Debuginfo.t
  -> (Flambda.Expr.t * Simplify_result.t) option

type simplify =
     Simplify_env.t
  -> Simplify_result.t
  -> Flambda.Expr.t
  -> Flambda.Expr.t * Simplify_result.t
