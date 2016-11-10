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

(** Move continuations upwards to try to reduce duplication when
    inlining.  (In previous versions of Flambda this pass used to operate
    on normal [Let] expressions; that is no longer required since we no
    longer have nested scopes for those.  However nested scopes do still
    exist in the context of continuations.  Avoiding that would require
    something like converting to SSA form.)

    More specifically, this pass detects situations of the form:

    let_cont k1 x1 =
      let_cont k2 x2 =
        <cont>
      in
      <body2>
    in
    <body1>

    (with [x1] not free in <cont>) and transform them to:

    let_cont k2 x2 =
      <cont>
    in
    let_cont k1 x1 =
      <body2>
    in
    <body1>

    (This example is simplified since it supposes continuations only have
    one argument.)
*)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

val run : Flambda.program -> Flambda.program
