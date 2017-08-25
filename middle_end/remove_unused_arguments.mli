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

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

(** Introduce a stub function to avoid depending on unused arguments.

    For instance, it turns
      [let rec fact n unused =
         if n = 0 then 1
         else n * fact (n-1) unused]
    into
      [let rec fact' n =
         if n = 0 then 1
         else n * fact' (n-1)
       and fact n unused = fact' n]
*)
val separate_unused_arguments_in_closures
   : Flambda_static.Program.t
  -> backend:(module Backend_intf.S)
  -> Flambda_static.Program.t

val separate_unused_arguments_in_set_of_closures
   : Flambda.Set_of_closures.t
  -> backend:(module Backend_intf.S)
  -> Flambda.Set_of_closures.t option
