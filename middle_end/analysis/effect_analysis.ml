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

let no_effects_prim prim =
  match Flambda_primitive.effects_and_coeffects prim with
  | (No_effects | Only_generative_effects _), (No_coeffects | Has_coeffects) ->
    true
  | _ -> false


and no_effects_named (named : Flambda.Named.t) =
  match named with
  | Simple _ | Read_mutable _ | Set_of_closures _ -> true
  | Assign _ -> false
  | Prim (prim, _dbg) -> no_effects_prim prim

let only_generative_effects_prim prim =
  match Semantics_of_primitives.for_primitive prim with
  | Only_generative_effects, No_coeffects -> true
  | _ -> false

let only_generative_effects_named (named : Flambda.Named.t) =
  match named with
  | Simple _ | Read_mutable _ | Set_of_closures _ -> true
  | Assign _ -> false
  | Prim (prim, _dbg) -> only_generative_effects_prim prim
