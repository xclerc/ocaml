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

(** Where an expression with only generative effects is evaluated prior to a
    non-recursive continuation definition, but is only used inside the handler
    of such continuation, move the expression into the handler. This
    transformation should help to move computations occurring before conditional
    branches to the branches where they are actually used.

      let x = ... in
      let_cont k = <handler> in
      <body>
    -->
      let_cont k =
        let x = ... in
        <handler>
      in
      <body>

    when x is not free in <body>.

    Sinking of lets like this exposes more opportunities for Comballoc.
*)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

val run : Flambda.program -> Flambda.program
