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
  | Value_must_scan
  | Value_can_scan
  | Naked_immediate
  | Naked_float
  | Naked_int32
  | Naked_int64
  | Naked_nativeint

let value ~must_scan = if must_scan then Value_must_scan else Value_can_scan
let naked_immediate () = Naked_immediate

let naked_float () =
  if Targetint.size < 64 then None
  else Some Naked_float

let naked_int32 () = Naked_int32

let naked_int64 () =
  if Targetint.size < 64 then None
  else Some Naked_int64

let naked_nativeint () = Naked_nativeint

let lambda_value_kind t =
  let module L = Lambda in
  match t with
  | Value_must_scan -> Some L.Pgenval
  | Value_can_scan -> Some L.Pintval
  | Naked_immediate -> Some L.Pnaked_intval
  | Naked_float -> Some L.Pfloatval
  | Naked_int32 -> Some (L.Pboxedintval Pint32)
  | Naked_int64 -> Some (L.Pboxedintval Pint64)
  | Naked_nativeint -> Some (L.Pboxedintval Pnativeint)

include Identifiable.Make (struct
  type nonrec t = t

  let compare t1 t2 = Pervasives.compare t1 t2
  let equal t1 t2 = (compare t1 t2 = 0)

  let hash = Hashtbl.hash

  let print ppf t =
    match t with
    | Value_must_scan -> Format.pp_print_string ppf "value_must_scan"
    | Value_can_scan -> Format.pp_print_string ppf "value_can_scan"
    | Naked_immediate -> Format.pp_print_string ppf "naked_immediate"
    | Naked_float -> Format.pp_print_string ppf "naked_float"
    | Naked_int32 -> Format.pp_print_string ppf "naked_int32"
    | Naked_int64 -> Format.pp_print_string ppf "naked_int64"
    | Naked_nativeint -> Format.pp_print_string ppf "naked_nativeint"
end)

let compatible t1 t2 =
  match t1, t2 with
  | Value_must_can, Value_can_scan
  | Value_can_scan, Value_must_scan -> true
  | _, _ -> equal t1 t2
