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

module T = Flambda_types
module C = Inlining_cost

external swap16 : int -> int = "%bswap16"
external swap32 : int32 -> int32 = "%bswap_int32"
external swap64 : int64 -> int64 = "%bswap_int64"
external swapnative : nativeint -> nativeint = "%bswap_native"

let const_int_expr expr n =
  if Effect_analysis.no_effects_named expr then
    let (new_expr, approx) = T.make_const_int_named n in
    new_expr, approx, C.Benefit.remove_code_named expr C.Benefit.zero
  else expr, T.value_int n, C.Benefit.zero
let const_char_expr expr c =
  if Effect_analysis.no_effects_named expr then
    let (new_expr, approx) = T.make_const_char_named c in
    new_expr, approx, C.Benefit.remove_code_named expr C.Benefit.zero
  else expr, T.value_char c, C.Benefit.zero
let const_ptr_expr expr n =
  if Effect_analysis.no_effects_named expr then
    let (new_expr, approx) = T.make_const_ptr_named n in
    new_expr, approx, C.Benefit.remove_code_named expr C.Benefit.zero
  else expr, T.value_constptr n, C.Benefit.zero
let const_bool_expr expr b =
  const_ptr_expr expr (if b then 1 else 0)
let const_float_expr expr f =
  if Effect_analysis.no_effects_named expr then
    let (new_expr, approx) = T.make_const_float_named f in
    new_expr, approx, C.Benefit.remove_code_named expr C.Benefit.zero
  else expr, T.value_boxed_float f, C.Benefit.zero
let const_boxed_int_expr expr t i =
  if Effect_analysis.no_effects_named expr then
    let (new_expr, approx) = T.make_const_boxed_int_named t i in
    new_expr, approx, C.Benefit.remove_code_named expr C.Benefit.zero
  else expr, T.value_boxed_int t i, C.Benefit.zero

let const_comparison_expr expr (cmp : Lambda.comparison) x y =
  (* Using the [Pervasives] comparison functions here in the compiler
     coincides with the definitions of such functions in the code
     compiled by the user, and is thus correct. *)
  const_bool_expr expr
    (match cmp with
     | Ceq -> x = y
     | Cneq -> x <> y
     | Clt -> x < y
     | Cgt -> x > y
     | Cle -> x <= y
     | Cge -> x >= y)

let freshen_and_squash_aliases env var =
  let var = Freshening.apply_variable (E.freshening env) var in
  let ty = E.find_exn env var in
  (* CR mshinwell: Shouldn't the variable always be in the env now? *)
  match T.follow_variable_equality ty ~is_present_in_env:(E.mem env) with
  | None -> var, ty
  | Some var -> var, ty

let freshen_and_squash_aliases_list env vars =
  List.map (fun var -> freshen_and_squash_aliases env var) vars

let simpler_equivalent_term env r original_named ty
      : (Variable.t * Flambda.Named.t) list * Flambda.Reachable.t * R.t =
  if not (Effect_analysis.no_effects_named original_named) then
    [], Flambda.Reachable.reachable original_named, r
  else
    let importer = E.importer env in
    match T.reify_using_env ~importer ty ~is_present_in_env:(E.mem env) with
    | None -> [], Flambda.Reachable.reachable original_named, r
    | Some named ->
      let r = R.map_benefit r (B.remove_code_named original_named) in
      [], Flambda.Reachable.reachable named, r
