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

    Kinds form a partial order.  Each non-[Bottom] kind is incomparable with
    every other non-[Bottom] kind.  [Bottom] is strictly less than everything
    else.

    "Basic" kinds are those which do not involve any notion of tagging and
    are non-[Bottom].
*)

module Basic : sig
  type t = private
    | Value
    | Naked_int
    | Naked_float
    | Naked_int32
    | Naked_int64
    | Naked_nativeint

  val value : unit -> t
  val naked_int : unit -> t
  val naked_float : unit -> t option
  val naked_int32 : unit -> t
  val naked_int64 : unit -> t option
  val naked_nativeint : unit -> t
end

type t = private
  | Value
  | Tagged_int
  | Naked_int
  | Naked_float
  | Naked_int32
  | Naked_int64
  | Naked_nativeint
  | Bottom

val of_basic : Basic.t -> t

val value : unit -> t
val tagged_int : unit -> t
val naked_int : unit -> t
val naked_float : unit -> t option
val naked_int32 : unit -> t
val naked_int64 : unit -> t option
val naked_nativeint : unit -> t
val bottom : unit -> t

(** Two value kinds are "compatible" iff they are both the same kind, or one
    of them is [Bottom]. *)
val compatible : t -> t -> bool

val lambda_value_kind : t -> Lambda.value_kind option

type gc_semantics =
  | Must_register
  | Can_register
  | Cannot_register

val gc_semantics : t -> gc_semantics

include Identifiable.S with type t := t
