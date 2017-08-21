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

(** Tags on runtime boxed values. *)

include Identifiable.S

val create_exn : int -> t

val to_int : t -> int

val zero : t
val object_tag : t

module Scannable : sig
  (** Tags that are strictly less than [No_scan_tag], corresponding to
      blocks that can be scanned by the GC. *)
  type t

  (** Raises not only if the supplied integer is less than 0 but also if
      it is greater than or equal to [No_scan_tag]. *)
  val create_exn : int -> t

  val to_int : t -> int

  include Identifiable.S with type t := t
end
