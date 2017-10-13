(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*            Pierre Chambart and Vincent Laviron, OCamlPro               *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2017 OCamlPro SAS                                          *)
(*   Copyright 2017 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** Analysis propagating the possibility for a value to reach a
    variable.
 
    We say that a variable x "flows to" another variable y if there exists an
    execution where a value bound to x can later be bound to y.
 
    We define the partial order "<=" as the transitive closure of the
    "flows to" relation.  ("flows to" is not necessarily transitively closed,
    but is usually quite close to being so.)
 
    For instance in:
 
    let f b x y =
      let v = if b then x else y in
      if b then
        let w = v in
        w
      else
        let z = v in
        z
 
    x and y flows to v;
    v flows to w and z;
    x flows to w;
    y flows to z;
    but x does not flow to z, yet z <= x.
 
    This analysis computes an over-approximation of the '<=' relation.
 
    The main approximation point is about functions: ...
*)

(* CR mshinwell for pchambart / vlaviron: Please finish the above comment. *)

type result = unit

val run : Flambda_static.Program.t -> result
