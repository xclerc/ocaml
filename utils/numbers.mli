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

(** Modules about numbers, some of which satisfy {!Identifiable.S}. *)

module Int : sig
  include Identifiable.S with type t = int

  (** [zero_to_n n] is the set of numbers \{0, ..., n\} (inclusive). *)
  val zero_to_n : int -> Set.t
end

module Int8 : sig
  type t

  val zero : t
  val one : t

  val of_int_exn : int -> t
  val to_int : t -> int
end

module Int16 : sig
  type t

  val of_int_exn : int -> t
  val of_int64_exn : Int64.t -> t

  val to_int : t -> int
end

module type Float_ops = sig
  type t

  val one : t
  val minus_one : t

  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val div : t -> t -> t

  val neg : t -> t
  val abs : t -> t

  val is_either_zero : t -> t
  val is_any_nan : t -> bool
end

module Float_by_bit_pattern : sig
  (** Floating point numbers whose comparison and equality relations are
      the usual [Int64] relations on the bit patterns of the floats.  This
      in particular means that different representations of NaN will be
      distinguished, as will the two signed zeros.

      Never use [Pervasives.compare] on values of type [t].  Use either
      [compare] or [compare_ieee] depending on which semantics you want.
      Likewise for equality.
  *)

  include Identifiable.S

  include Float_ops with type t := t

  val of_float : float -> t

  (** Comparison of floating-point values as defined by IEEE 754. *)
  val compare_ieee : t -> t -> int

  (** Equality on floating-point values as defined by IEEE 754. *)
  val equal_ieee : t -> t -> bool
end

module Int32 : sig
  include Identifiable.S with type t = Int32.t

  val byte_swap : t -> t
end

module Int64 : sig
  include Identifiable.S with type t = Int64.t

  val byte_swap : t -> t
end

module Nativeint : sig
  include Identifiable.S with type t = Nativeint.t

  val byte_swap : t -> t
end
