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

(** The variable to which the given type states equality, if such exists. *)
val var : t -> Variable.t option

(** The symbol, or field of a symbol, to which the given type states
    equality, if such exists. *)
val symbol : t -> (Symbol.t * (int option)) option

(** The type of a symbol that cannot be resolved (e.g. missing .cmx file).
    It is assumed that the symbol's value may need scanning by the GC. *)
val unresolved_symbol : Symbol.t -> t

(*
(** Attempt to use a type to refine a value kind. *)
val refine_value_kind : t -> Lambda.value_kind -> Lambda.value_kind
*)

(** Rename free variables in a type. *)
val rename_variables
   : (t
  -> f:(Variable.t -> Variable.t)
  -> t) with_importer

(** Building of types and terms representing tagged / boxed values from
    specified constants. *)
val this_tagged_bool_named : bool -> Flambda0.Named.t * t
val this_tagged_immediate_named : Immediate.t -> Flambda0.Named.t * t
val this_boxed_float_named : float -> Flambda0.Named.t * t
val this_boxed_int32_named : Int32.t -> Flambda0.Named.t * t
val this_boxed_int64_named : Int64.t -> Flambda0.Named.t * t
val this_boxed_nativeint_named : Targetint.t -> Flambda0.Named.t * t

(** Building of types and terms representing untagged / unboxed values from
    specified constants. *)
val this_untagged_immediate_named : Immediate.t -> Flambda0.Named.t * t
val this_naked_float_named : float -> Flambda0.Named.t * t
val this_naked_int32_named : Int32.t -> Flambda0.Named.t * t
val this_naked_int64_named : Int64.t -> Flambda0.Named.t * t
val this_naked_nativeint_named : Targetint.t -> Flambda0.Named.t * t

(** Whether the given type says that a term of that type is unreachable. *)
val is_bottom : (t -> bool) with_importer

(** Determine whether the given type provides any information about an
    Flambda term of that type.  (This holds just when the type is not
    one of the [Unknown]s.) *)
val known : (t -> bool) with_importer

(** Determine whether the given type provides useful information about an
    Flambda term of that type.  To be "useful" the type must satisfy
    [known] and not correspond to an unreachable term ([Bottom]). *)
val useful : (t -> bool) with_importer

(** Whether all types in the given list do *not* satisfy [useful]. *)
val all_not_useful : (t list -> bool) with_importer

type 'a or_wrong = private
  | Ok of 'a
  | Wrong

module Or_not_all_values_known : sig
  type 'a t = private
    | Exactly of 'a
    | Not_all_values_known
end

module Blocks : sig
  type t = private ty_value array Tag.Scannable.Map.t
end

module Summary : sig
  type t = private
    | Wrong
    | Blocks_and_tagged_immediates of
        Blocks.t * (Immediate.Set.t Or_not_all_values_known.t)
    | Boxed_floats of Numbers.Float.Set.t Or_not_all_values_known.t
    | Boxed_int32s of Numbers.Int32.Set.t Or_not_all_values_known.t
    | Boxed_int64s of Numbers.Int64.Set.t Or_not_all_values_known.t
    | Boxed_nativeints of Targetint.Set.t Or_not_all_values_known.t
    | Closures of set_of_closures Closure_id.Map.t Or_not_all_values_known.t
    | Set_of_closures of set_of_closures Or_not_all_values_known.t
end

(** Create a summary of a type, flattening unions as required. *)
val summarize : (t -> Summary.t) with_importer

(*
(** Whether the given type describes a float array. *)
val is_float_array : t -> bool

(** Whether the given type describes one or more boxed floats. *)
val is_boxed_float : t -> bool

(** Whether code that mutates a value with the given type is to be
    treated as invalid.  Cannot be called with an [Extern] or [Symbol]
    type; these need to be resolved first. *)
val invalid_to_mutate : t -> bool

(** Find the type for a bound variable in a set-of-closures
    type.  A fatal error is produced if the variable is not bound in
    the given type. *)
val type_for_bound_var : set_of_closures -> Var_within_closure.t -> t

(** Given a set-of-closures type and a closure ID, apply any
    freshening specified by the type to the closure ID, and return
    the resulting ID.  Causes a fatal error if the resulting closure ID does
    not correspond to any function declaration in the type. *)
val freshen_and_check_closure_id
   : set_of_closures
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

(** Try to produce a canonical Flambda term, with no free variables, that has
    the given Flambda type. *)
val reify : t -> Flambda0.Named.t option

(** As for [reify], but in the event where a type cannot be reified, may
    return a [Var], [Symbol] or [Read_symbol_field] term (save that for
    [Var] this will only happen if [is_present_in_env] says that the
    particular variable is in scope). *)
val reify_using_env
   : t
  -> is_present_in_env:(Variable.t -> bool)
  -> Flambda0.Named.t option

(** As for [reify] but only produces terms when the type describes a
    unique tagged immediate. *)
val reify_as_tagged_immediate : t -> Immediate.t option

(** As for [reify_as_tagged_immediate], but for boxed floats. *)
val reify_as_boxed_float : t -> float option

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

type reified_as_set_of_closures =
  | Wrong
  | Unresolved of unresolved_value
  | Unknown
  | Ok of Variable.t option * set_of_closures
  (** In the [Ok] case, there may not be a variable associated with the set of
      closures; it might be out of scope. *)

(** Try to prove that a value with the given type may be used as a
    set of closures.  Values coming from external compilation units with
    unresolved types are permitted. *)
val reify_as_set_of_closures : t -> reified_as_set_of_closures

type strict_reified_as_set_of_closures =
  | Wrong
  | Ok of Variable.t option * set_of_closures

(** As for [reify_as_set_of_closures], but disallows unresolved or
    unknown types. *)
val strict_reify_as_set_of_closures
   : t
  -> strict_reified_as_set_of_closures

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

(** Returns [true] iff the given type provides strictly more information
    about the corresponding value than the supplied type [than]. *)
val strictly_more_precise : t -> than:t -> bool

(** Returns [true] iff the given type provides the same or strictly more
    information about the corresponding value than the supplied type [than]. *)
val as_or_more_precise : t -> than:t -> bool

*)
