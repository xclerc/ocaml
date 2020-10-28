(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2019 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type t = unit

let id = ()
let is_id () = true
let inverse () = ()
let compose () ~newer:() = ()
let print ppf () = Format.fprintf ppf "id"
let equal () () = true
let hash () = 0

let unroll_to () = None
let depth () = 1
