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
    (The basic definitions are in [Flambda_types0], which does not
    depend on [Flambda].) *)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

(** The type of an Flambda term. *)
type t = Flambda_types0.T.t

(** Means of making and examining types. *)
include Flambda_types0.Constructors_and_accessors

(** The type of a symbol that cannot be resolved (e.g. missing .cmx file). *)
val unresolved_symbol : Symbol.t -> t

(** Take the given integer and produce an appropriate type for it
    together with an Flambda term (that can be [Let]-bound) representing it. *)
val make_const_int_named : int -> Flambda.named * t

(** As for [make_const_int_named], but for characters. *)
val make_const_char_named : char -> Flambda.named * t

(** As for [make_const_int_named], but for "const_pointer"s. *)
val make_const_ptr_named : int -> Flambda.named * t

(** As for [make_const_int_named], but for booleans. *)
val make_const_bool_named : bool -> Flambda.named * t

(** As for [make_const_int_named], but for boxed floats. *)
val make_const_boxed_float_named : float -> Flambda.named * t

(** As for [make_const_int_named], but for boxed int32s. *)
val make_const_boxed_int32_named : Int32.t -> Flambda.named * t

(** As for [make_const_int_named], but for boxed int64s. *)
val make_const_boxed_int64_named : Int64.t -> Flambda.named * t

(** As for [make_const_int_named], but for boxed nativeints. *)
val make_const_boxed_nativeint_named : Nativeint.t -> Flambda.named * t

(** As for [make_const_int_named], but for unboxed floats. *)
val make_const_unboxed_float_named : float -> Flambda.named * t

(** As for [make_const_int_named], but for unboxed int32s. *)
val make_const_unboxed_int32_named : Int32.t -> Flambda.named * t

(** As for [make_const_int_named], but for unboxed int64s. *)
val make_const_unboxed_int64_named : Int64.t -> Flambda.named * t

(** As for [make_const_int_named], but for unboxed nativeints. *)
val make_const_unboxed_nativeint_named : Nativeint.t -> Flambda.named * t

(** Whether the given type says that a term of that type is unreachable. *)
val is_bottom : t -> bool

(** Determine whether the given type provides any information about an
    Flambda term of that type.  (This holds just when the type is not
    one of the [Unknown]s.) *)
val known : t -> bool

(** Determine whether the given type provides useful information about an
    Flambda term of that type.  To be "useful" the type must satisfy
    [known] and not correspond to an unreachable term ([Bottom]). *)
val useful : t -> bool

(** Whether all types in the given list do *not* satisfy [useful]. *)
val all_not_useful : t list -> bool

(** Whether code that mutates a value with the given type is to be
    treated as invalid.  Cannot be called with an [Extern] or [Symbol]
    type; these need to be resolved first. *)
val invalid_to_mutate : t -> bool

(** Find the type for a bound variable in a set-of-closures
    type.  A fatal error is produced if the variable is not bound in
    the given type. *)
val type_for_bound_var : value_set_of_closures -> Var_within_closure.t -> t

(** Given a set-of-closures type and a closure ID, apply any
    freshening specified by the type to the closure ID, and return
    the resulting ID.  Causes a fatal error if the resulting closure ID does
    not correspond to any function declaration in the type. *)
val freshen_and_check_closure_id
   : value_set_of_closures
  -> Closure_id.Set.t
  -> Closure_id.Set.t

(** Returns [true] when it can be proved that the provided types identify a
    unique value (with respect to physical equality) at runtime.  The input
    list must have length two. *)
val physically_same_values : t list -> bool

(** Returns [true] when it can be proved that the provided types identify
    different values (with respect to physical equality) at runtime.  The
    input list must have length two. *)
val physically_different_values : t list -> bool

type get_field_result =
  | Ok of t
  | Unreachable

(** Given the type [t] of a value, expected to correspond to a block
    (in the [Pmakeblock] sense of the word), and a field index then return
    an appropriate type for that field of the block (or
    [Unreachable] if the code with the type [t] is unreachable).
    N.B. Not _all_ cases of unreachable code are returned as [Unreachable]. *)
val get_field : t -> field_index:int -> get_field_result

(** If the given Flambda type corresponds to an array, return the length
    of that array; in all other cases return [None]. *)
val length_of_array : t -> int option

(** If the given type identifies another variable and [is_present_in_env]
    deems it to be in scope, return that variable (wrapped in a [Some]),
     otherwise return [None]. *)
val follow_variable_equality
   : t
  -> is_present_in_env:(Variable.t -> bool)
  -> Variable.t option

module Reification_summary : sig
  type t
    | Nothing_done
    | Replaced_term
end

type reification_result = Flambda.named * Reification_summary.t * t

(** Try to produce a canonical Flambda term that has the given Flambda type. *)
val reify : t -> (Flambda.named * t) option

(** When there are no side effects performed by the given term, return a
    replacement for that term produced from the given Flambda type
    (cf. [reify]), the replacement being expected to be a less complex term. *)
val maybe_replace_term_with_reified_term
   : t
  -> Flambda.named
  -> reification_result

(** As for [maybe_replace_term_with_reified_term], but also enables us to
    simplify based on equalities between variables.  The caller must provide
    a function that tells us whether, if we simplify to a given variable,
    the value of that variable will be accessible in the current
    environment. *)
val maybe_replace_term_with_reified_term_using_env
   : t
  -> is_present_in_env:(Variable.t -> bool)
  -> Flambda.named
  -> reification_result

(** As for [reify] but only produces terms when the type describes a
    unique integer. *)
val reify_as_int : t -> int option

(** As for [reify_as_int], but for boxed floats. *)
val reify_as_boxed_float : t -> float option

(** As for [reify_as_int], but for constant float arrays. *)
val reify_as_constant_float_array : value_float_array -> float list option

(** As for [reify_as_int], but for strings. *)
val reify_as_string : t -> string option

type reified_as_scannable_block =
  | Wrong
  | Ok of Tag.Scannable.t * t array

(** Try to prove that a value with the given type may be used as a block
    that can be scanned by the GC. *)
val reify_as_scannable_block : t -> reified_as_scannable_block

type reified_as_variant =
  | Wrong
  | Ok of Unionable.t

(** Try to prove that the given type is of the expected form for the
    Flambda type of a value of variant type. *)
val reify_as_variant : t -> reified_as_variant

type reified_as_scannable_block_or_immediate =
  | Wrong
  | Immediate
  | Scannable_block

(** Try to prove that the given type is of the expected form to describe
    either a GC-scannable block or an immediate. *)
(* CR mshinwell: currently "immediate" is just int, char or constptr (need to
   document this).  Should it include the unboxed integers? *)
val reify_as_scannable_block_or_immediate
   : t
  -> reified_as_scannable_block_or_immediate

type reified_as_set_of_closures =
  | Wrong
  | Unresolved of unresolved_value
  | Unknown
  | Ok of Variable.t option * value_set_of_closures
  (** In the [Ok] case, there may not be a variable associated with the set of
      closures; it might be out of scope. *)

(** Try to prove that a value with the given type may be used as a
    set of closures.  Values coming from external compilation units with
    unresolved types are permitted. *)
val reify_as_set_of_closures : t -> reified_as_set_of_closures

type strict_reified_as_set_of_closures =
  | Wrong
  | Ok of Variable.t option * value_set_of_closures

(** As for [reify_as_set_of_closures], but disallows unresolved or
    unknown types. *)
val strict_reify_as_set_of_closures
   : t
  -> strict_reified_as_set_of_closures

type strict_reified_as_closure =
  | Wrong
  | Ok of value_set_of_closures Closure_id.Map.t
      * Variable.t option * Symbol.t option

(** Try to prove that a value with the given type may be used as a
    closure.  Values coming from external compilation units with unresolved
    types are not permitted. *)
val strict_reify_as_closure : t -> strict_reified_as_closure

type strict_reified_as_closure_singleton =
  | Wrong
  | Ok of Closure_id.t * Variable.t option
      * Symbol.t option * value_set_of_closures

(** As for [strict_reify_as_closure] but disallows situations where
    multiple different closures flow to the same program point. *)
val strict_reify_as_closure_singleton
   : t
  -> strict_reified_as_closure_singleton

type reified_as_closure_allowing_unresolved =
  | Wrong
  | Unresolved of unresolved_value
  | Unknown
  | Ok of value_set_of_closures Closure_id.Map.t
      * Variable.t option * Symbol.t option

(** As for [reify_as_closure], but values coming from external
    compilation units with unresolved types are permitted. *)
val reify_as_closure_allowing_unresolved
   : t
  -> reified_as_closure_allowing_unresolved

type switch_branch_classification =
  | Cannot_be_taken
  | Can_be_taken
  | Must_be_taken

(** Given the type of a [Switch] scrutinee, determine whether the case of
    the corresponding switch with the given integer label either cannot be
    taken, can be taken or will always be taken. *)
val classify_switch_branch
   : t
  -> int
  -> switch_branch_classification
