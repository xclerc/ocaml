(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
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

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

type t =
  | Value
  | Unboxed_float
  | Unboxed_int32
  | Unboxed_int64
  | Unboxed_nativeint
  | Bottom

let compatible t1 t2 =
  match t1, t2 with
  | Bottom, _ | _, Bottom
  | Value, Value
  | Unboxed_float, Unboxed_float
  | Unboxed_int32, Unboxed_int32
  | Unboxed_int64, Unboxed_int64
  | Unboxed_nativeint, Unboxed_nativeint -> true
  | (Value | Unboxed_float | Unboxed_int32 | Unboxed_int64
      | Unboxed_nativeint), _ -> false

include Identifiable.Make (struct
  type nonrec t = t

  let to_int t =
    match t with
    | Value -> 0
    | Unboxed_float -> 1
    | Unboxed_int32 -> 2
    | Unboxed_int64 -> 3
    | Unboxed_nativeint -> 4
    | Bottom -> 5

  let compare t1 t2 = Pervasives.compare (to_int t1) (to_int t2)
  let equal t1 t2 = (compare t1 t2 = 0)

  let hash = Hashtbl.hash

  let print ppf t =
    match t with
    | Value -> Format.pp_print_string ppf "value"
    | Unboxed_float -> Format.pp_print_string ppf "unboxed_float"
    | Unboxed_int32 -> Format.pp_print_string ppf "unboxed_int32"
    | Unboxed_int64 -> Format.pp_print_string ppf "unboxed_int64"
    | Unboxed_nativeint -> Format.pp_print_string ppf "unboxed_nativeint"
    | Bottom -> Format.pp_print_string ppf "bottom"

  let output _ _ = Misc.fatal_error "Flambda_kind.output not implemented"
end)
