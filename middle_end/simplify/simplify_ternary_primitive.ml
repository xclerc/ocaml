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

let simplify_block_set_known_index env r prim ~field ~block_access_kind
      ~init_or_assign ~block ~new_value dbg =
  if field < 0 then begin
    Misc.fatal_errorf "[Block_set] with bad field index %d: %a"
      field
      Flambda_primitive.print prim
  end;
  let field_kind' = Flambda_primitive.kind_of_block_set_kind field_kind in
  let block, block_ty = S.simplify_simple env block in
  let new_value, new_value_ty = S.simplify_simple env new_value in
  let original_term () : Named.t = Prim (Binary (prim, block, index), dbg) in
  let result_kind = K.unit () in
  let invalid () = Reachable.invalid (), T.bottom result_kind in
  let ok () =
    match new_value_proof with
    | Proved _ ->
      Reachable.reachable (original_term ()), T.unknown result_kind Other
    | Invalid -> invalid ()
  in
  match block_access_kind with
  | Definitely_immediate | Must_scan ->
    let proof = (E.type_accessor env T.prove_blocks) block_ty in
    begin match proof with
    | Proved (Exactly blocks) ->
      if not (T.Blocks.valid_field_access blocks ~field) then invalid ()
      else ok ()
    | Proved Not_all_values_known -> ok ()
    | Invalid -> invalid ()
    end
  | Naked_float ->
    let block_proof = (E.type_accessor env T.prove_float_array) block_ty in
    let new_value_proof =
      (E.type_accessor env T.prove_naked_float) new_value_ty
    in
    begin match block_proof with
    | Proved (Exactly sizes) ->
      if not (Int.Set.exists (fun size -> size > field) sizes) then invalid ()
      else ok ()
    | Proved Not_all_values_known -> ok ()
    | Invalid -> invalid ()
    end
  | Generic_array _spec -> Misc.fatal_error "Not yet implemented"
    (* CR mshinwell: Finish off
    Simplify_generic_array.simplify_block_set env r prim ~field spec args
    *)

let simplify_block_set env r prim dbg ~value_kind ~init_or_assign
      arg1 arg2 arg3 =
  ...

let simplify_bytes_or_bigstring_set env r prim dbg bytes_like_value
      string_accessor_width ~str ~index ~new_value =
  ...

let simplify_ternary_primitive env r prim arg1 arg2 arg3 dbg =
  match prim with
  | Block_set (value_kind, init_or_assign) ->
    simplify_block_set env r prim dbg ~value_kind ~init_or_assign
      arg1 arg2 arg3
  | Bytes_set string_accessor_width ->
    simplify_bytes_set env r prim dbg ~string_accessor_width arg1 arg2 arg3
  | Bigstring_set bigstring_accessor_width ->
    simplify_bigstring_set env r prim dbg ~bigstring_accessor_width
      arg1 arg2 arg3
