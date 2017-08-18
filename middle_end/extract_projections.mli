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

(** Identify projections from variables used in function or continuation
    bodies (free variables or specialised args, for example, according to
    [which_variables] below).  Projections from variables that are also
    used boxed are not returned. *)

(** The returned projections are [projecting_from] (cf. projection.mli)
    the "existing inner vars".
*)
val from_function's_free_vars
   : env:Simplify_aux.Env.t
  -> free_vars:Flambda.free_vars
  -> function_decl:Flambda.function_declaration
  -> Projection.Set.t

val from_function's_specialised_args
   : env:Simplify_aux.Env.t
  -> specialised_args:Flambda.specialised_args
  -> function_decl:Flambda.function_declaration
  -> Projection.Set.t

(** For continuations, all parameters are checked for potential projections. *)
val from_continuation
   : uses:Simplify_aux.Continuation_uses.t
  -> handler:Flambda.continuation_handler
  -> Projection.Set.t
