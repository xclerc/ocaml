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

type t = int
type tag = t

include Identifiable.Make (Numbers.Int)

let create_exn tag =
  if tag < 0 || tag > 255 then
    Misc.fatal_error (Printf.sprintf "Tag.create_exn %d" tag)
  else
    tag

let to_int t = t

let zero = 0
let string_tag = Obj.string_tag
let double_tag = Obj.double_tag
let double_array_tag = Obj.double_array_tag
let custom_tag = Obj.custom_tag
let closure_tag = Obj.closure_tag

module Scannable = struct
  type nonrec t = t

  include Identifiable.Make (Numbers.Int)

  let create tag =
    if tag < 0 || tag >= Obj.no_scan_tag then None
    else Some tag

  let create_exn tag =
    match create tag with
    | Some tag -> tag
    | None ->
      Misc.fatal_error (Printf.sprintf "Tag.Scannable.create_exn %d" tag)

  let to_int t = t
  let to_tag t = t

  let of_tag tag =
    if tag < 0 || tag >= Obj.no_scan_tag then None
    else Some tag

  let zero = 0
  let object_tag = Obj.object_tag
end

module Non_scannable = struct
  type nonrec t = t

  include Identifiable.Make (Numbers.Int)

  let create tag =
    if tag < Obj.no_scan_tag then None
    else Some tag

  let create_exn tag =
    match create tag with
    | Some tag -> tag
    | None ->
      Misc.fatal_error (Printf.sprintf "Tag.Non_scannable.create_exn %d" tag)

  let to_int t = t
  let to_tag t = t

  let of_tag tag =
    if tag < 0 || tag >= Obj.no_scan_tag then None
    else Some tag
end
