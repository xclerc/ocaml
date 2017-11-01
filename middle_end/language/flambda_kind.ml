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

type scanning =
  | Must_scan
  | Can_scan

let join_scanning s1 s2 =
  match s1, s2 with
  | Must_scan, Must_scan
  | Must_scan, Can_scan
  | Can_scan, Must_scan -> Must_scan
  | Can_scan, Can_scan -> Can_scan

let meet_scanning s1 s2 =
  match s1, s2 with
  | Must_scan, Must_scan -> Must_scan
  | Must_scan, Can_scan
  | Can_scan, Must_scan
  | Can_scan, Can_scan -> Can_scan

type t =
  | Value of scanning
  | Naked_immediate
  | Naked_float
  | Naked_int32
  | Naked_int64
  | Naked_nativeint

type kind = t

let value scanning = Value scanning

(* CR mshinwell: can remove lambdas now *)
let naked_immediate () = Naked_immediate

let naked_float () = Naked_float

let naked_int32 () = Naked_int32

let naked_int64 () = Naked_int64

let naked_nativeint () = Naked_nativeint

include Identifiable.Make (struct
  type nonrec t = t

  let compare t1 t2 = Pervasives.compare t1 t2
  let equal t1 t2 = (compare t1 t2 = 0)

  let hash = Hashtbl.hash

  let print ppf t =
    match t with
    | Value Must_scan -> Format.pp_print_string ppf "value_must_scan"
    | Value Can_scan -> Format.pp_print_string ppf "value_can_scan"
    | Naked_immediate -> Format.pp_print_string ppf "naked_immediate"
    | Naked_float -> Format.pp_print_string ppf "naked_float"
    | Naked_int32 -> Format.pp_print_string ppf "naked_int32"
    | Naked_int64 -> Format.pp_print_string ppf "naked_int64"
    | Naked_nativeint -> Format.pp_print_string ppf "naked_nativeint"
end)

let compatible t ~if_used_at =
  match t, if_used_at with
  (* The two important cases: *)
  | Value Can_scan, Value Must_scan -> true
  | Value Must_scan, Value Can_scan -> false
  | _, _ -> equal t if_used_at

let is_value t =
  match t with
  | Value _ -> true
  | Naked_immediate
  | Naked_float
  | Naked_int32
  | Naked_int64
  | Naked_nativeint -> false

let is_naked_float t =
  match t with
  | Naked_float -> true
  | Value _
  | Naked_immediate
  | Naked_int32
  | Naked_int64
  | Naked_nativeint -> false

module Standard_int = struct
  type t =
    | Tagged_immediate
    | Naked_int32
    | Naked_int64
    | Naked_nativeint

  let to_kind t : kind =
    match t with
    | Tagged_immediate -> Value Can_scan
    | Naked_int32 -> Naked_int32
    | Naked_int64 -> Naked_int64
    | Naked_nativeint -> Naked_nativeint

  let print ppf t =
    match t with
    | Tagged_immediate -> Format.pp_print_string ppf "Tagged_immediate"
    | Naked_int32 -> Format.pp_print_string ppf "Naked_int32"
    | Naked_int64 -> Format.pp_print_string ppf "Naked_int64"
    | Naked_nativeint -> Format.pp_print_string ppf "Naked_nativeint"

  let print_lowercase ppf t =
    match t with
    | Tagged_immediate -> Format.pp_print_string ppf "tagged_immediate"
    | Naked_int32 -> Format.pp_print_string ppf "naked_int32"
    | Naked_int64 -> Format.pp_print_string ppf "naked_int64"
    | Naked_nativeint -> Format.pp_print_string ppf "naked_nativeint"
end

module Boxable_number = struct
  type t =
    | Naked_float
    | Naked_int32
    | Naked_int64
    | Naked_nativeint

  let to_kind t : kind =
    match t with
    | Naked_float -> Naked_float
    | Naked_int32 -> Naked_int32
    | Naked_int64 -> Naked_int64
    | Naked_nativeint -> Naked_nativeint

  let print ppf t =
    match t with
    | Naked_float -> Format.pp_print_string ppf "Naked_float"
    | Naked_int32 -> Format.pp_print_string ppf "Naked_int32"
    | Naked_int64 -> Format.pp_print_string ppf "Naked_int64"
    | Naked_nativeint -> Format.pp_print_string ppf "Naked_nativeint"

  let print_lowercase ppf t =
    match t with
    | Naked_float -> Format.pp_print_string ppf "naked_float"
    | Naked_int32 -> Format.pp_print_string ppf "naked_int32"
    | Naked_int64 -> Format.pp_print_string ppf "naked_int64"
    | Naked_nativeint -> Format.pp_print_string ppf "naked_nativeint"
end
