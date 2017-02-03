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

(** Decision and transformation code for inlining of continuations.
    This runs on toplevel expressions (i.e. function bodies,
    [Initialize_symbol] bodies and [Effect] bodies) after simplification
    and collection of continuation use information has happened.  Separation
    from the main simplification loop reduces the complexity of the inlining
    from quadratic to linear. *)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

val for_toplevel_expression
   : Flambda.expr
  -> Inline_and_simplify_aux.Result.t
  -> simplify:(Inline_and_simplify_aux.Env.t
    -> Inline_and_simplify_aux.Result.t
    -> Flambda.expr
    -> Flambda.expr * Inline_and_simplify_aux.Result.t)
  -> Flambda.expr * Inline_and_simplify_aux.Result.t
