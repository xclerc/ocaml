(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module E = Simplify_env_and_result.Env
module R = Simplify_env_and_result.Result
module T = Flambda_type

type named_simplifier =
  (Variable.t * Flambda.Named.t) list * Flambda.Reachable.t
    * Flambda_type.t * R.t

let type_for_const (const : Simple.Const.t) =
  match const with
  (* CR mshinwell: unify terminology: "untagged" vs "naked" *)
  | Untagged_immediate i -> T.this_naked_immediate i
  | Tagged_immediate i -> T.this_tagged_immediate i
  | Naked_float f -> T.this_naked_float f
  | Naked_int32 n -> T.this_naked_int32 n
  | Naked_int64 n -> T.this_naked_int64 n
  | Naked_nativeint n -> T.this_naked_nativeint n

let type_for_simple env (simple : Simple.t)
      : (Flambda.Named.t * Flambda_type.t) Flambda.Or_invalid.t =
  match simple with
  | Const c -> Ok (Simple (Const c), type_for_const c)
  | Name name ->
    let ty = E.type_for_name env name in
    let reified =
      T.reify ~importer
        ~type_for_name:(fun name -> E.type_for_name env name)
        ty
    in
    match reified with
    | Term (named, ty) -> Ok (named, ty)
    | Cannot_reify -> Ok (Simple simple, ty)
    | Invalid -> Invalid
