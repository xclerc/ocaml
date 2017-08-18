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

(** Basic definitions and constructors for the type system of Flambda.
    The types give approximations to the results of evaluating Flambda
    terms at runtime.  Each type has a kind, as per [Flambda_kind].
    This type system is in fact parameterised over the type of Flambda
    expressions.
    Normal Flambda passes should use the interface provided in
    [Flambda_types] rather than this one. *)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module Boxed_number_kind : sig
  type t = private
    | Float
    | Int32
    | Int64
    | Nativeint
end

type unresolved_value =
  | Set_of_closures_id of Set_of_closures_id.t
  | Symbol of Symbol.t

type unknown_because_of =
  | Unresolved_value of unresolved_value
  | Other

type load_lazily =
  | Export_id of Export_id.t
  | Symbol of Symbol.t

module rec T : sig
  (** The type of an Flambda term. *)
  type ('decls, 'freshening) t = private {
    descr : descr;
    var : Variable.t option;
    symbol : (Symbol.t * int option) option;
  } 

  (** Types are equipped with a subtyping relation given by a partial order.

      [Bottom] is, well, bottom.
      Each [Unknown (k, _)] gives a top element.

      [Bottom] means "no value can flow to this point".
      [Unknown (k, _)] means "any value of kind [k] might flow to this point".
  *)
  (* CR mshinwell: After the closure reworking patch has been merged and
     the work on classic mode closure approximations has been merged (the
     latter introducing a type of function declarations in this module), then
     the only circularity between this type and Flambda will be for
     Flambda.expr on function bodies. *)
  and ('decls, 'freshening) descr = private 
    | Unknown of Flambda_kind.t * unknown_because_of
    | Union of Unionable.t
    | Unboxed_float of Float.Set.t
    | Unboxed_int32 of Int32.Set.t
    | Unboxed_int64 of Int64.Set.t
    | Unboxed_nativeint of Nativeint.Set.t
    | Boxed_number of boxed_number_kind * t
    | Set_of_closures of ('decls, 'freshening) set_of_closures
    | Closure of ('decls, 'freshening) closure
    | String of string
    | Float_array of float_array
    | Bottom
    | Load_lazily of load_lazily

  and ('decls, 'freshening) closure = {
    potential_closures : ('decls, 'freshening) t Closure_id.Map.t;
    (** Map of closures ids to set of closures *)
  } [@@unboxed]

  (* CR-soon mshinwell: add support for the approximations of the results, so we
     can do all of the tricky higher-order cases. *)
  and ('decls, 'freshening) set_of_closures = private {
    function_decls : 'decls;
    bound_vars : t Var_within_closure.Map.t;
    invariant_params : Variable.Set.t Variable.Map.t lazy_t;
    size : int option Variable.Map.t lazy_t;
    (** For functions that are very likely to be inlined, the size of the
        function's body. *)
    specialised_args : specialised_args;
    freshening : 'freshening;
    (** Any freshening that has been applied to [function_decls]. *)
    direct_call_surrogates : Closure_id.t Closure_id.Map.t;
  }

  and float_array_contents =
    | Contents of t array
    | Unknown_or_mutable

  and float_array = {
    contents : float_array_contents;
    size : int;
  }
  (* CR-someday mshinwell: This should probably be altered so that the
     specialisation isn't just to a variable, or some particular projection,
     but is instead to an actual type (which would be enhanced to describe
     the projection too). *)
  and specialised_to = {
    var : Variable.t option;
    (** The "outer variable".  For non-specialised arguments of continuations
        (which may still be involved in projection relations) this may be
        [None]. *)
    projection : Projection.t option;
    (** The [projecting_from] value (see projection.mli) of any [projection]
        must be another free variable or specialised argument (depending on
        whether this record type is involved in [free_vars] or
        [specialised_args] respectively) in the same set of closures.
        As such, this field describes a relation of projections between
        either the [free_vars] or the [specialised_args]. *)
  }

  and specialised_args = specialised_to Variable.Map.t

  (* CR-soon mshinwell for pchambart: Add comment describing semantics.  (Maybe
     we should move the comment from the .ml file into here.) *)
  (** Form the type of a join point in the control flow graph where the values
      on the incoming edges have the given types. *)
  val join : really_import_approx:(t -> t) -> t -> t -> t

  val print : Format.formatter -> t -> unit
  val print_descr : Format.formatter -> descr -> unit
  val print_set_of_closures
    : Format.formatter
    -> set_of_closures
    -> unit
end and Unionable : sig
  module Immediate : sig
    type t = private
      (* CR mshinwell: We could consider splitting these again *)
      | Int of int
      | Char of char
      | Constptr of int

    include Identifiable.S with type t := t
  end

  type blocks = T.t array Tag.Scannable.Map.t

  type t = private
    | Blocks of blocks
    | Blocks_and_immediates of blocks * Immediate.Set.t
    | Immediates of Immediate.Set.t

  val print : Format.formatter -> t -> unit

  (** Partial ordering:
        Ill_typed_code <= Ok _ <= Anything
  *)
  type 'a or_bottom =
    | Anything
    | Ok of 'a
    | Ill_typed_code

  val join : t -> t -> really_import_approx:(T.t -> T.t) -> t or_bottom

  type singleton = private
    | Block of Tag.Scannable.t * T.t array
    | Int of int
    | Char of char
    | Constptr of int

  (** Find the properties that are guaranteed to hold of a value with union
      type at every point it is used. *)
  val flatten : t -> singleton or_bottom
end

module type Constructors_and_accessors = sig
  (** Each type has a unique kind. *)
  val kind : t -> really_import_approx:(t -> t) -> Flambda_kind.t

  (** Construction of types involving equalities to runtime values. *)
  val unknown : Value_kind.t -> unknown_because_of -> t
  val int : int -> t
  val constptr : int -> t
  val char : char -> t
  val unboxed_float : float -> t
  val unboxed_int32 : Int32.t -> t
  val unboxed_int64 : Int64.t -> t
  val unboxed_nativeint : Nativeint.t -> t
  val boxed_float : float -> t
  val boxed_int32 : Int32.t -> t
  val boxed_int64 : Int64.t -> t
  val boxed_nativeint : Nativeint.t -> t
  val mutable_float_array : size:int -> t
  val immutable_float_array : t array -> t
  val string : int -> string option -> t
  val block : Tag.Scannable.t -> t array -> t
  val extern : Export_id.t -> t
  val symbol : Symbol.t -> t
  val unresolved : unresolved_value -> t
  val bottom : t

  (** Construction of types without equalities to runtime values. *)
  val any_float : t
  val any_unboxed_float : t
  val any_unboxed_int32 : t
  val any_unboxed_int64 : t
  val any_unboxed_nativeint : t

  (** Construct a closure type given the type of the
      corresponding set of closures and the closure ID of the closure to
      be projected from such set.  [closure_var] and/or [set_of_closures_var]
      may be specified to augment the type with variables that may
      be used to access the closure value itself, so long as they are in
      scope at the proposed point of use. *)
  val closure
     : ?closure_var:Variable.t
    -> ?set_of_closures_var:Variable.t
    -> ?set_of_closures_symbol:Symbol.t
    -> ('decls, 'freshening) set_of_closures Closure_id.Map.t
    -> ('decls, 'freshening) t

  (** Create a [set_of_closures] structure which can be used for building
      a type describing a set of closures. *)
  val create_set_of_closures
     : function_decls:'decls
    -> bound_vars:t Var_within_closure.Map.t
    -> invariant_params:Variable.Set.t Variable.Map.t lazy_t
    -> specialised_args:Flambda.specialised_to Variable.Map.t
    -> freshening:'freshening
    -> direct_call_surrogates:Closure_id.t Closure_id.Map.t
    -> ('decls, 'freshening) set_of_closures

  (** Construct a set of closures type.  [set_of_closures_var] is as for
      the parameter of the same name in [closure], above. *)
  val set_of_closures
     : ?set_of_closures_var:Variable.t
    -> ('decls, 'freshening) set_of_closures
    -> ('decls, 'freshening) t

  (** Extraction of the description field(s) of type(s). *)
  val descr : t -> descr
  val descrs : t list -> descr list

  (** Change the closure freshening inside a set of closures type. *)
  val update_freshening_of_set_of_closures
     : set_of_closures
    -> freshening:Freshening.Project_var.t
    -> set_of_closures

  (** Augment an type with a given variable (see comment above).
      If the type was already augmented with a variable, the one
      passed to this function replaces it within the type. *)
  val augment_with_variable : t -> Variable.t -> t

  (** Like [augment_with_variable], but for symbol information. *)
  val augment_with_symbol : t -> Symbol.t -> t

  (** Like [augment_with_symbol], but for symbol field information. *)
  val augment_with_symbol_field : t -> Symbol.t -> int -> t

  (** Replace the description within an type. *)
  val replace_description : t -> descr -> t

  (** Attempt to use a value kind to refine a type. *)
  val refine_using_value_kind : t -> Lambda.value_kind -> t

  (** Attempt to use a type to refine a value kind. *)
  val refine_value_kind : t -> Lambda.value_kind -> Lambda.value_kind
end

include S
