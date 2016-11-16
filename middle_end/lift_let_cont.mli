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


Constructs introducing nesting are: let/let_mutable (just treat this as let)
  and let_cont.  So basically all we have to handle is let vs. let_cont in
  both body and handler positions.
Terminators are: apply, apply_cont, switch.

We always want to move let_cont as high as possible.
Lets that have computational cost should never be lifted.

Maybe it should be: any let that binds a constant should be lifted right
to the top.  Then you just have to consider cases where the let_cont
(really, a block of let_conts) is/are second:

1.
  let x = (* computation *) in
  let_cont k1 = (* not using x *) in
  ...
  let_cont kn = (* not using x *) in
-->
  let_cont k1 = (* not using x *) in
  ...
  let_cont kn = (* not using x *) in
  let x = (* computation *) in

2.
  let_cont k1 = ... in
  let_cont k2 = (* not using k1 *) in
  ...
  let_cont kn = (* not using k1 *) in
-->
  let_cont k2 = (* not using k1 *) in
  ...
  let_cont kn = (* not using k1 *) in
  let_cont k1 = ... in

The final thing is to deal with handlers.  When entering a handler the
first thing is to apply rules 1 and 2 above.  This means in particular that
any continuation eligible for lifting out save perhaps that it may depend on
one of the handler's arguments will be at the top.  Thus only one more rule
is needed, applied recursively to the rewritten handler:
3.
  let_cont k1 xs =
                                                   ]
    let_cont k2 = (* not involving xs *) in body2  ] this is the rewritten
                                                   ] handler
  in
  body1
--->
  let_cont k2 = (* not involving xs *) in body2
  let_cont k1 xs = body2 in
  body1

Ignoring terminators:

- Lets that bind constants depend on "top" only
- Lets that bind anything else depend on the previous "let" or if not "top"

let x = (* computation *) in
let k1 = (* not using x *) in
let y = ... x ... in
let z = (* computation *) in
let k2 = ... x ... in
let k3 = ... k2 ... in
let k4 = (* uses x but not y *) in
let k5 = ... in

(x = ..., {}, {})
(k1 = ..., {}, {})
(y = ..., {x}, {})
(z = ..., {y}, {})  (* note that for [z] we add [y] as a dependency *)
(k2 = ..., {x}, {})
(k3 = ..., {}, {k2})
(k4 = ..., {x}, {})

                  top
                   |
        ----------------------
        |                    |
        |                    |
        x                    k1
  ------|--------------
  |          |        |
  y          k2       k4
  |          |
  z          k3

*)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

val run : Flambda.program -> Flambda.program
