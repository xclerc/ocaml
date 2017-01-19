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

(** Introduce specialised arguments to continuations. *)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

val for_toplevel_expression
   : Flambda.expr
  -> Inline_and_simplify_aux.Result.t
  -> simplify:(Inline_and_simplify_aux.Env.t
    -> Inline_and_simplify_aux.Result.t
    -> Flambda.expr
    -> Flambda.expr * Inline_and_simplify_aux.Result.t)
  -> backend:(module Backend_intf.S)
  -> Flambda.expr
