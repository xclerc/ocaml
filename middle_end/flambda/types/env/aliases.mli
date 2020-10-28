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

(** Union-find-like structure for keeping track of equivalence classes,
    used for alias resolution in the typing environment, with support for
    associating orderings to aliases of canonical elements. *)

[@@@ocaml.warning "+a-4-30-40-41-42"]

(* CR xclerc for xclerc: this module provides a functor rather than "direct"
   access to alias handling to simplify testing. This could be reconsidered
   once we trust the code to be correct, in particular because the indirection
   makes the code extremely slow. *)

type 'a coercion_to_canonical = {
  coercion_to_canonical : 'a;
} [@@ocaml.unboxed]

module type Coercion = sig
  type t
  val equal : t -> t -> bool
  val inverse : t -> t
  val id : t
  val is_id : t -> bool
  val compose : t -> newer:t -> t
  val print : Format.formatter -> t -> unit
end

module type Element = sig
  type t
  val name : Name.t -> t
  val without_coercion : t -> t
  val pattern_match
    : t
    -> name:(Reg_width_things.Name.t -> 'a)
    -> const:(Reg_width_things.Const.t -> 'a)
    -> 'a
  include Identifiable.S with type t := t
end

module type Export = sig
  type e
  type t
  val add : t -> e -> t
  val empty : t
  val to_ids_for_export : t -> Ids_for_export.t
  module Import_map : sig
    type t
    val of_import_map : Ids_for_export.Import_map.t -> t
    val simple : t -> e -> e
  end
end

module Make (C : Coercion) (E : Element) (_ : Export with type e = E.t) : sig

type nonrec coercion_to_canonical = C.t coercion_to_canonical

type t

include Contains_ids.S with type t := t

val print : Format.formatter -> t -> unit

val invariant : t -> unit

val empty : t

type add_result = private {
  t : t;
  canonical_element : E.t;
  alias_of : E.t;
  coerce_alias_of_to_canonical_element : C.t;
}

val add
   : t
  -> element1:E.t
  -> binding_time_and_mode1:Binding_time.With_name_mode.t
  -> coerce_from_element2_to_element1:C.t
  -> element2:E.t
  -> binding_time_and_mode2:Binding_time.With_name_mode.t
  -> add_result

val mem : t -> E.t -> bool

(** [get_canonical_element] returns [None] only when the
    [min_order_within_equiv_class] cannot be satisfied. *)
val get_canonical_element_exn
   : t
  -> E.t
  -> Name_mode.t
  -> min_name_mode:Name_mode.t
  -> E.t * coercion_to_canonical

(** [get_aliases] always returns the supplied element in the result set. *)
val get_aliases : t -> E.t -> coercion_to_canonical E.Map.t

val get_canonical_ignoring_name_mode : t -> Name.t -> E.t

val merge : t -> t -> t

end
