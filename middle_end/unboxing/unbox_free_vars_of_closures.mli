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

(** When approximations of free variables of closures indicate that they
    are closures or blocks, rewrite projections from such blocks to new
    variables (which become free in the closures), with the defining
    expressions of the projections lifted out of the corresponding sets
    of closures. *)

val run
   : env:Simplify_env.t
  -> set_of_closures:Flambda.Set_of_closures.t
  -> ((Variable.t * Flambda.Named.t) list
    * Flambda.Set_of_closures.t * Inlining_cost.Benefit.t) option
