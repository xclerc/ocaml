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

module B = Inlining_cost.Benefit
module E = Simplify_env_and_result.Env
module K = Flambda_kind
module R = Simplify_env_and_result.Result
module T = Flambda_type

module Float_by_bit_pattern = Numbers.Float_by_bit_pattern
module Int = Numbers.Int
module Named = Flambda.Named
module Reachable = Flambda.Reachable

let simplify_block_set_computed env r prim dbg ~value_kind ~init_or_assign
      arg1 arg2 arg3 =
  ...

let simplify_bytes_set env r prim dbg ~string_accessor_width arg1 arg2 arg3 =
  ...

let simplify_bigstring_set env r prim dbg ~bigstring_accessor_width
      arg1 arg2 arg3 =
  ...

let simplify_ternary_primitive env r prim arg1 arg2 arg3 dbg =
  match prim with
  | Block_set_computed (value_kind, init_or_assign) ->
    simplify_block_set_computed env r prim dbg ~value_kind ~init_or_assign
      arg1 arg2 arg3
  | Bytes_set string_accessor_width ->
    simplify_bytes_set env r prim dbg ~string_accessor_width arg1 arg2 arg3
  | Bigstring_set bigstring_accessor_width ->
    simplify_bigstring_set env r prim dbg ~bigstring_accessor_width
      arg1 arg2 arg3
