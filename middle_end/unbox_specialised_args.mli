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

(** When approximations of specialised arguments indicate that they are
    closures or blocks, add more specialised arguments corresponding to
    the projections from such blocks (with definitions of such projections
    lifted out), such that the original specialised arguments may later be
    eliminated.

    This in particular enables elimination of closure allocations in
    examples such as:

      let rec map f = function
        | [] -> []
        | a::l -> let r = f a in r :: map f l

      let g x =
        map (fun y -> x + y) [1; 2; 3; 4]

    Here, the specialised version of [map] initially has a specialised
    argument [f]; and upon inlining there will be a projection of [x] from
    the closure of [f].  This pass adds a new specialised argument to carry
    that projection, at which point the closure of [f] is redundant.
*)

val rewrite_set_of_closures
   : env:Simplify_aux.Env.t
  (* CR-soon mshinwell: eliminate superfluous parameter *)
  -> duplicate_function:(
       env:Simplify_aux.Env.t
    -> set_of_closures:Flambda.Set_of_closures.t
    -> fun_var:Variable.t
    -> new_fun_var:Variable.t
    -> Flambda.Function_declaration.t
      * Flambda.specialised_to Variable.Map.t)
  -> set_of_closures:Flambda.Set_of_closures.t
  -> ((Variable.t * Flambda.Named.t) list
    * Flambda.Set_of_closures.t * Inlining_cost.Benefit.t) option
