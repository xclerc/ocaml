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
  | Tagged_int
  | Naked_int
  | Naked_float
  | Naked_int32
  | Naked_int64
  | Naked_nativeint
  | Bottom

let value () = Value
let tagged_int () = Tagged_int
let naked_int () = Naked_inta

let naked_float () =
  if Targetint.size < 64 then None
  else Some Naked_float

let naked_int32 () = Naked_int32

let naked_int64 () =
  if Targetint.size < 64 then None
  else Some Naked_int64

let naked_nativeint () = Naked_nativeint
let bottom () = Bottom

let compatible t1 t2 =
  match t1, t2 with
  | Bottom, _ | _, Bottom
  | Value, Value
  | Tagged_int, Tagged_int
  | Naked_float, Naked_float
  | Naked_int32, Naked_int32
  | Naked_int64, Naked_int64
  | Naked_nativeint, Naked_nativeint -> true
  | (Value | Tagged_int | Naked_float | Naked_int32 | Naked_int64
      | Naked_nativeint), _ -> false

let lambda_value_kind t =
  let module L = Lambda in
  match t with
  | Value -> Some L.Pgenval
  | Tagged_int -> Some L.Pintval
  | Naked_float -> Some L.Pfloatval
  | Naked_int32 -> Some (L.Pboxedintval Pint32)
  | Naked_int64 -> Some (L.Pboxedintval Pint64)
  | Naked_nativeint -> Some (L.Pboxedintval Pnativeint)
  | Bottom -> None

include Identifiable.Make (struct
  type nonrec t = t

  let compare t1 t2 = Pervasives.compare t1 t2
  let equal t1 t2 = (compare t1 t2 = 0)

  let hash = Hashtbl.hash

  let print ppf t =
    match t with
    | Value -> Format.pp_print_string ppf "value"
    | Tagged_int -> Format.pp_print_string ppf "tagged_int"
    | Naked_float -> Format.pp_print_string ppf "naked_float"
    | Naked_int32 -> Format.pp_print_string ppf "naked_int32"
    | Naked_int64 -> Format.pp_print_string ppf "naked_int64"
    | Naked_nativeint -> Format.pp_print_string ppf "naked_nativeint"
    | Bottom -> Format.pp_print_string ppf "bottom"

  let output _ _ = Misc.fatal_error "Flambda_kind.output not implemented"
end)
