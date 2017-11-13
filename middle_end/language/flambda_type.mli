(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** The type system of Flambda including various functions to analyse types.
    (The basic definitions are in [Flambda type0], which does not
    depend on [Flambda].) *)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

(** Basic definitions, constructors and accessors. *)
include module type of struct include Flambda0.Flambda_type end

(** The type of a symbol that cannot be resolved (e.g. missing .cmx file).
    It is assumed that the symbol's value may need scanning by the GC. *)
val unresolved_symbol : Symbol.t -> t

(** For each of the kinds in an arity, create an "unknown" type, with
    reason [Other]. *)
val unknown_types_from_arity : Flambda_arity.t -> t list

(** Create an "unknown" type with the same kind as the given type. *)
val unknown_like : (t -> t) type_accessor

(** Rename free variables in a type. *)
val rename_variables
   : (t
  -> f:(Variable.t -> Variable.t)
  -> t) with_importer

(** Building of types and terms representing tagged / boxed values from
    specified constants. *)
val this_tagged_bool_named : bool -> Flambda0.Named.t * t
val this_tagged_immediate_named : Immediate.t -> Flambda0.Named.t * t

(** Building of types and terms representing untagged / unboxed values from
    specified constants. *)
val this_untagged_immediate_named : Immediate.t -> Flambda0.Named.t * t
val this_naked_float_named : float -> Flambda0.Named.t * t
val this_naked_int32_named : Int32.t -> Flambda0.Named.t * t
val this_naked_int64_named : Int64.t -> Flambda0.Named.t * t
val this_naked_nativeint_named : Targetint.t -> Flambda0.Named.t * t

type 'a or_wrong = private
  | Ok of 'a
  | Wrong

module Or_not_all_values_known : sig
  type 'a t = private
    | Exactly of 'a
    | Not_all_values_known
end

module Blocks : sig
  type t
end

module Joined_closures : sig
  type t

  val sets_of_closures : t -> ty_value Closure_id.Map.t

  val to_type : t -> flambda_type
end

module Joined_sets_of_closures : sig
  type t

  val function_decls : t -> function_declaration Closure_id.Map.t
  val closure_elements : t -> ty_value Var_within_closure.Map.t

  (** Return the type of a given closure, specified by closure ID, selected
      from the given set of closures. *)
  val type_for_closure_id : t -> Closure_id.t -> flambda_type

  val to_type : t -> flambda_type
end

module Evaluated : sig
  (** A straightforward canonical form which can be used easily for the
      determination of properties of a type.

      There are some subtleties concerning "unknown" and "bottom" types here.
      For reliable determination of these two properties the [is_unknown]
      and [is_bottom] functions should be used in preference to matching on
      values of type [t].
  *)
  type t_values = private
    | Unknown
    | Bottom
    | Blocks_and_tagged_immediates of
        (Blocks.t * Immediate.Set.t) Or_not_all_values_known.t
    (** For [Blocks_and_tagged_immediates] it is guaranteed that the
        "blocks" portion is non-empty.  (Otherwise [Tagged_immediates_only]
        will be produced.) *)
    | Tagged_immediates_only of Immediate.Set.t Or_not_all_values_known.t
    | Boxed_floats of Numbers.Float.Set.t Or_not_all_values_known.t
    | Boxed_int32s of Numbers.Int32.Set.t Or_not_all_values_known.t
    | Boxed_int64s of Numbers.Int64.Set.t Or_not_all_values_known.t
    | Boxed_nativeints of Targetint.Set.t Or_not_all_values_known.t
    | Closures of Joined_closures.t Or_not_all_values_known.t
    | Sets_of_closures of Joined_sets_of_closures.t Or_not_all_values_known.t
    | Strings of String_info.Set.t Or_not_all_values_known.t
    | Float_arrays of { lengths : Numbers.Int.Set.t Or_not_all_values_known.t; }

  type t = private
    | Values of t_values
    | Naked_immediates of Immediate.Set.t Or_not_all_values_known.t
    | Naked_floats of Numbers.Float.Set.t Or_not_all_values_known.t
    | Naked_int32s of Numbers.Int32.Set.t Or_not_all_values_known.t
    | Naked_int64s of Numbers.Int64.Set.t Or_not_all_values_known.t
    | Naked_nativeints of Targetint.Set.t Or_not_all_values_known.t

  (** Evaluate the given type to a canonical form, possibly with an associated
      name. *)
  val create : (flambda_type -> t * (Name.t option)) type_accessor

  val print : Format.formatter -> t -> unit

  (** The kind of the given evaluated type. *)
  val kind : t -> Flambda_kind.t
end

(** Whether the given type says that a term of that type can never be
    constructed (in other words, it is [Invalid]). *)
val is_bottom : (t -> bool) type_accessor

(** Determine whether the given type provides any information about an
    Flambda term of that type. *)
val is_known : (t -> bool) type_accessor

(** Determine whether the given type provides useful information about an
    Flambda term of that type. *)
val is_useful : (t -> bool) type_accessor

(** Whether all types in the given list do *not* satisfy [useful]. *)
val all_not_useful : (t list -> bool) type_accessor

(** XXX Something like this? *)
type equation_rhs =
  | Simple of Simple.t
  | Type of t

val equations_implied_by_type
   : (t -> (equation_rhs Variable.Map.t)) type_accessor

(*
(** Whether the given type describes a float array. *)
val is_float_array : t -> bool

(** Whether code that mutates a value with the given type is to be
    treated as invalid.  Cannot be called with an [Extern] or [Symbol]
    type; these need to be resolved first. *)
val invalid_to_mutate : t -> bool

(** Find the type for a bound variable in a set-of-closures
    type.  A fatal error is produced if the variable is not bound in
    the given type. *)
val type_for_bound_var : set_of_closures -> Var_within_closure.t -> t

(** Returns [true] when it can be proved that the provided types identify a
    unique value (with respect to physical equality) at runtime.  The input
    list must have length two. *)
val physically_same_values : t list -> bool

(** Returns [true] when it can be proved that the provided types identify
    different values (with respect to physical equality) at runtime.  The
    input list must have length two. *)
val physically_different_values : t list -> bool

*)

type reification_result =
  | Term of Simple.t * t
  | Cannot_reify
  | Invalid

(** Try to produce a canonical Flambda term that has the given Flambda type.
    The resulting term will never cause an allocation.  The term will also
    not contain any free variables unless [allow_free_variables] has been set
    to [true].

    This function may be used to turn the types of [Simple] terms into their
    canonical representative terms (as it follows aliases in the environment).

    If [expected_kind] does not match the kind of the term / type being
    returned then a fatal error will be produced.
*)
val reify
   : (allow_free_variables:bool
  -> expected_kind:Flambda_kind.t
  -> flambda_type
  -> reification_result) type_accessor

type get_field_result = private
  | Ok of t
  | Invalid

(** Given the type [t] of a value (expected to correspond to a block of kind
    [Value]) and a field index then return an appropriate type for that field
    of the block (or [Invalid]).  The expected kind of the field, as per
    [Flambda_primitive.Block_load], must be provided.

    Note that this will return [Invalid] if a use is detected of a variant-like
    type (union of blocks and immediates).
*)
val get_field
   : (t
  -> field_index:int
  -> field_kind:Flambda_primitive.field_kind
  -> get_field_result) type_accessor

type boxed_float_proof = private
  | Proved of Numbers.Float.Set.t Or_not_all_values_known.t
  | Invalid

(** Prove that the given type represents:
    - one or more known boxed floats ([Proved (Ok ...)]);
    - one or more unknown boxed floats ([Proved Not_all_values_known]);
    - value(s) that are not boxed floats (meaning that code computing a value
      of such type, in a context where a boxed float is required, is invalid).
    The set returned in an [Proved (Ok ...)] result is guaranteed non-empty.
*)
val prove_boxed_float : (t -> boxed_float_proof) type_accessor

type boxed_int32_proof = private
  | Proved of Numbers.Int32.Set.t Or_not_all_values_known.t
  | Invalid

(** As for [prove_boxed_float] but for [Int32]. *)
val prove_boxed_int32 : (t -> boxed_int32_proof) type_accessor

type boxed_int64_proof = private
  | Proved of Numbers.Int64.Set.t Or_not_all_values_known.t
  | Invalid

(** As for [prove_boxed_float] but for [Int64]. *)
val prove_boxed_int64 : (t -> boxed_int64_proof) type_accessor

type boxed_nativeint_proof = private
  | Proved of Targetint.Set.t Or_not_all_values_known.t
  | Invalid

(** As for [prove_boxed_float] but for [Nativeint]. *)
val prove_boxed_nativeint : (t -> boxed_nativeint_proof) type_accessor

type closures_proof =
  | Proved of Joined_closures.t Or_not_all_values_known.t
  | Invalid

(** As for [proved_boxed_float] but for closures. *)
val prove_closures : (t -> closures_proof) type_accessor

type sets_of_closures_proof = private
  | Proved of Joined_sets_of_closures.t Or_not_all_values_known.t
  | Invalid

(** As for [proved_boxed_float] but for sets of closures. *)
val prove_sets_of_closures : (t -> sets_of_closures_proof) type_accessor

(** As for [proved_boxed_float] but for naked floats.  Note that there is
    no [Invalid] case returned---no such cases are possible that are not
    kind errors (which cause a fatal error). *)
val prove_naked_float
   : (t
  -> Numbers.Float.Set.t Or_not_all_values_known.t) type_accessor

type tagged_immediate_proof = private
  | Proved of Immediate.Set.t Or_not_all_values_known.t
  | Invalid

(** As for [prove_boxed_float] but for a tagged immediate. *)
val prove_tagged_immediate : (t -> tagged_immediate_proof) type_accessor

type string_proof = private
  | Proved of String_info.Set.t Or_not_all_values_known.t
  | Invalid

(** As for [prove_boxed_float] but for a tagged immediate. *)
val prove_string : (t -> string_proof) type_accessor

type lengths_of_arrays_or_blocks_proof = private
  | Proved of Numbers.Int.Set.t Or_not_all_values_known.t
  | Invalid

(** Determine the known length(s) of the array(s) or structured block(s)
    (i.e. blocks with tag less than [No_scan_tag]) described by the given
    type.
    Note that this will return [Invalid] if a use is detected of a variant-like
    type (union of blocks and immediates).
*)
val lengths_of_arrays_or_blocks
   : (t
  -> lengths_of_arrays_or_blocks_proof) type_accessor

(*
(** As for [reify] but only produces terms when the type describes a
    unique tagged immediate. *)
val reify_as_tagged_immediate : t -> Immediate.t option

(** As for [reify_as_int], but for arrays of unboxed floats (corresponding
    to values with tag [Double_array_tag]. *)
val reify_as_unboxed_float_array : t -> float list option

(** As for [reify_as_int], but for strings. *)
val reify_as_string : t -> string option

type proved_scannable_block =
  | Wrong
  | Ok of Tag.Scannable.t * t array

(** Try to prove that a value with the given type may be used as a block
    that can be scanned by the GC.  (Note that there are cases of scannable
    blocks, e.g. closures, that this function will return [Wrong] for.) *)
val prove_scannable_block : t -> proved_scannable_block

type reified_as_scannable_block_or_immediate =
  | Wrong
  | Immediate
  | Scannable_block

(** Try to prove that the given type is of the expected form to describe
    either a GC-scannable block or an immediate. *)
(* CR mshinwell: This doesn't actually produce a term, so doesn't reify *)
val reify_as_scannable_block_or_immediate
   : t
  -> reified_as_scannable_block_or_immediate

*)

(*

type strict_reified_as_closure =
  | Wrong
  | Ok of set_of_closures Closure_id.Map.t * Variable.t option * Symbol.t option

(** Try to prove that a value with the given type may be used as a
    closure.  Values coming from external compilation units with unresolved
    types are not permitted. *)
val strict_reify_as_closure : t -> strict_reified_as_closure

type strict_reified_as_closure_singleton =
  | Wrong
  | Ok of Closure_id.t * Variable.t option * Symbol.t option * set_of_closures

(** As for [strict_reify_as_closure] but disallows situations where
    multiple different closures flow to the same program point. *)
val strict_reify_as_closure_singleton
   : t
  -> strict_reified_as_closure_singleton

type reified_as_closure_allowing_unresolved =
  | Wrong
  | Unresolved of unresolved_value
  | Unknown
  | Ok of set_of_closures Closure_id.Map.t * Variable.t option * Symbol.t option

(** As for [reify_as_closure], but values coming from external
    compilation units with unresolved types are permitted. *)
val reify_as_closure_allowing_unresolved
   : t
  -> reified_as_closure_allowing_unresolved
*)
type switch_branch_classification =
  | Cannot_be_taken
  | Can_be_taken
  | Must_be_taken

(** Given the type of a [Switch] scrutinee, determine whether the case of
    the corresponding switch with the given integer label either cannot be
    taken, can be taken or will always be taken. *)
val classify_switch_branch
   : (flambda_type
  -> scrutinee:Name.t
  -> Targetint.t
  -> switch_branch_classification) type_accessor

(** Returns [true] iff the given type provides the same or strictly more
    information about the corresponding value than the supplied type [than]. *)
val as_or_more_precise : (t -> than:t -> bool) type_accessor

(** Type equality.  (This isn't just syntactic.) *)
val equal : (t -> t -> bool) type_accessor

(** An [Importer] that does nothing. *)
val null_importer : (module Importer)
