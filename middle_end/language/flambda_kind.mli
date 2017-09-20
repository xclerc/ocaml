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

(** Kinds of Flambda types.  These correspond in the backend to distinctions
    between different classes of registers in which variables are held
    and/or differences in GC (non-) registration of roots.
*)

type scanning = private
  | Must_scan
  | Can_scan

type t =
  | Value of scanning
  | Naked_immediate
  | Naked_float
  | Naked_int32
  | Naked_int64
  | Naked_nativeint

val value : must_scan:bool -> t
val naked_immediate : unit -> t
val naked_float : unit -> t
val naked_int32 : unit -> t
val naked_int64 : unit -> t
val naked_nativeint : unit -> t

(** Two value kinds are "compatible" iff they are both the same kind, or one
    of them is [Bottom]. *)
val compatible : t -> t -> bool

val lambda_value_kind : t -> Lambda.value_kind option

include Identifiable.S with type t := t
