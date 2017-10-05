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

let no_effects_prim (prim : Lambda.primitive) =
  match Semantics_of_primitives.for_primitive prim with
  | (No_effects | Only_generative_effects), (No_coeffects | Has_coeffects) ->
    true
  | _ -> false

let rec no_effects (flam : Flambda.Expr.t) =
  match flam with
  | Let { defining_expr; body; _ } ->
    no_effects_named defining_expr && no_effects body
  | Let_mutable { body } -> no_effects body
  (* CR mshinwell: needs thought *)
  | Switch _ -> false
  | Let_cont { body; _ } -> no_effects body
  | Apply _ | Apply_cont _ -> false
  | Unreachable -> true

and no_effects_named (named : Flambda.Named.t) =
  match named with
  | Var _ | Symbol _ | Const _ | Allocated_const _ | Read_mutable _
  | Read_symbol_field _
  | Set_of_closures _ | Project_closure _ | Project_var _
  | Move_within_set_of_closures _ -> true
  | Assign _ -> false
  | Prim (prim, _, _) -> no_effects_prim prim

let only_generative_effects_prim (prim : Lambda.primitive) =
  match Semantics_of_primitives.for_primitive prim with
  | Only_generative_effects, No_coeffects -> true
  | _ -> false

let only_generative_effects_named (named : Flambda.Named.t) =
  match named with
  | Set_of_closures _ -> true
  | Prim (prim, _, _) -> only_generative_effects_prim prim
  | Var _ | Symbol _ | Const _ | Allocated_const _ | Read_mutable _
  | Read_symbol_field _ | Project_closure _ | Project_var _
  | Move_within_set_of_closures _ | Assign _ -> false
