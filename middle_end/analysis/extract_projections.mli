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

(*

(** Identify projections from variables used in function or continuation
    bodies (free variables or specialised args, for example, according to
    [which_variables] below).  Projections from variables that are also
    used boxed are not returned. *)

(** The returned projections are [projecting_from] (cf. projection.mli)
    the "existing inner vars".
*)
val from_function's_free_vars
   : env:Simplify_env.t
  -> free_vars:Flambda.Free_vars.t
  -> function_decl:Flambda.Function_declaration.t
  -> Projection.Set.t

(** For continuations, all parameters are checked for potential projections. *)
val from_continuation
   : uses:Simplify_result.Continuation_uses.t
  -> handler:Flambda.Continuation_handler.t
  -> Projection.Set.t

*)
