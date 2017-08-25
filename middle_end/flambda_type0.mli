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

(** Basic definitions and constructors for the type system of Flambda. The types
    give approximations to the results of evaluating Flambda terms at runtime.
    Each type has a kind, as per [Flambda_kind].

    This type system is in fact parameterised over the type of Flambda
    expressions.

    Normal Flambda passes should use the interface provided in [Flambda_types]
    rather than this one. *)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module Boxed_number_kind : sig
  type t = private
    | Float
    | Int32
    | Int64
    | Nativeint

  include Identifiable.S with type t := t
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

type closure_freshening =
  { vars_within_closure : Var_within_closure.t Var_within_closure.Map.t;
    closure_id : Closure_id.t Closure_id.Map.t;
  }

val print_closure_freshening : Format.formatter -> closure_freshening -> unit

module type Constructors_and_accessors = sig
  type 'd t
  type 'd descr
  type 'd set_of_closures

  (** Each type has a unique kind. *)
  val kind
     : 'd t
    -> really_import_approx:('d t -> 'd t)
    -> Flambda_kind.t

  (** Like [kind], but causes a fatal error if the type has not been fully
      resolved. *)
  val kind_exn : _ t -> Flambda_kind.t

  (** Construct one of the various top types ("any value of the given kind
      can flow to this point"). *)
  val unknown : Flambda_kind.t -> unknown_because_of -> _ t

  (** The unique bottom type ("no value can flow to this point"). *)
  val bottom : unit -> _ t

  (** Construction of types involving equalities to runtime values. *)
  val int : int -> _ t
  val constptr : int -> _ t
  val char : char -> _ t
  val unboxed_float : float -> _ t
  val unboxed_int32 : Int32.t -> _ t
  val unboxed_int64 : Int64.t -> _ t
  val unboxed_nativeint : Nativeint.t -> _ t
  val boxed_float : float -> _ t
  val boxed_int32 : Int32.t -> _ t
  val boxed_int64 : Int64.t -> _ t
  val boxed_nativeint : Nativeint.t -> _ t
  val mutable_float_array : size:int -> _ t
  val immutable_float_array : 'd t array -> 'd t
  val mutable_string : size:int -> _ t
  val immutable_string : string -> _ t
  val block : Tag.t -> 'd t array -> 'd t

  (** Construction of types that link to other types which have not yet
      been loaded into memory (from a .cmx file). *)
  val export_id_loaded_lazily : Export_id.t -> _ t
  val symbol_loaded_lazily : Symbol.t -> _ t

  (** Construction of types without equalities to runtime values. *)
  val any_boxed_float : unit -> _ t
  val any_unboxed_float : unit -> _ t
  val any_unboxed_int32 : unit -> _ t
  val any_unboxed_int64 : unit -> _ t
  val any_unboxed_nativeint : unit -> _ t

  (** Construct a closure type given the type of the corresponding set of
      closures and the closure ID of the closure to be projected from such set.
      [closure_var] and/or [set_of_closures_var] may be specified to augment the
      type with variables that may be used to access the closure value itself,
      so long as they are in scope at the proposed point of use. *)
  val closure
     : ?closure_var:Variable.t
    -> ?set_of_closures_var:Variable.t
    -> ?set_of_closures_symbol:Symbol.t
    -> 'd set_of_closures Closure_id.Map.t
    -> 'd t

  (** Create a [set_of_closures] structure which can be used for building a type
      describing a set of closures. *)
  val create_set_of_closures
     : function_decls:'d
    -> size:int option Variable.Map.t lazy_t
    -> bound_vars:'d t Var_within_closure.Map.t
    -> invariant_params:Variable.Set.t Variable.Map.t lazy_t
    -> freshening:closure_freshening
    -> direct_call_surrogates:Closure_id.t Closure_id.Map.t
    -> 'd set_of_closures

  (** Construct a set of closures type. [set_of_closures_var] is as for the
      parameter of the same name in [closure], above. *)
  val set_of_closures
     : ?set_of_closures_var:Variable.t
    -> 'd set_of_closures
    -> 'd t

  (** Change the closure freshening inside a set of closures type. *)
  val update_freshening_of_set_of_closures
     : 'd set_of_closures
    -> freshening:closure_freshening
    -> 'd set_of_closures

  (** Augment an type with a given variable (see comment above). If the type was
      already augmented with a variable, the one passed to this function
      replaces it within the type. *)
  val augment_with_variable : 'd t -> Variable.t -> 'd t

  (** Replace the variable at the toplevel of a given type. *)
  val update_variable : 'd t -> Variable.t option -> 'd t

  (** Like [augment_with_variable], but for symbol information. *)
  val augment_with_symbol : 'd t -> Symbol.t -> 'd t

  (** Like [augment_with_symbol], but for symbol field information. *)
  val augment_with_symbol_field : 'd t -> Symbol.t -> int -> 'd t

  (** Replace the description within an type. *)
  val replace_description : 'd t -> 'd descr -> 'd t

  (** Attempt to use a value kind to refine a type. *)
  val refine_using_value_kind : 'd t -> Lambda.value_kind -> 'd t

  (** Free variables in a type. *)
  val free_variables : 'd t -> Variable.Set.t

  type cleaning_spec =
    | Available
    | Available_different_name of Variable.t
    | Unavailable

  (** Adjust a type so that all of the variables it references are in scope
      in some context.  The context is expressed by a function that says
      whether the variable is available under its existing name, available under
      another name, or unavailable. *)
  val clean
    : 'd t
    -> (Variable.t -> cleaning_spec)
    -> 'd t
end

module rec T : sig
  (** The type of an Flambda term. *)
  type 'd t = private {
    descr : 'd descr;
    (** The main description of the type. *)
    var : Variable.t option;
    (** An optional equality to a variable. *)
    projection : Projection.t option;
    (** An optional statement that the type describes a particular
        projection from some value (see projection.mli). *)
    symbol : (Symbol.t * int option) option;
    (** An optional equality to a symbol, or if the integer field number is
        specified, to a field of a symbol. *)
  } 

  (** Types are equipped with a subtyping relation given by a partial order.

      [Bottom] is, well, bottom.
      Each [Unknown (k, _)] gives a top element.

      [Bottom] means "no value can flow to this point".
      [Unknown (k, _)] means "any value of kind [k] might flow to this point".
  *)
  (* CR mshinwell: After the work on classic mode closure approximations has
     been merged (the latter introducing a type of function declarations in
     this module), then the only circularity between this type and Flambda
     will be for Flambda.Expr.t on function bodies. *)
  and 'd descr = private 
    | Unknown of Flambda_kind.t * unknown_because_of
    | Union of 'd Unionable.t
    | Unboxed_float of Numbers.Float.Set.t
    | Unboxed_int32 of Numbers.Int32.Set.t
    | Unboxed_int64 of Numbers.Int64.Set.t
    | Unboxed_nativeint of Numbers.Nativeint.Set.t
    | Boxed_number of Boxed_number_kind.t * 'd t
    | Set_of_closures of 'd set_of_closures
    | Closure of 'd closure
    | Immutable_string of string
    | Mutable_string of { size : int; }
    | Float_array of 'd float_array
    | Bottom
    | Load_lazily of load_lazily

  and 'd closure = {
    potential_closures : 'd t Closure_id.Map.t;
    (** Map of closures ids to set of closures *)
  } [@@unboxed]

  (* CR-soon mshinwell: add support for the approximations of the results, so we
     can do all of the tricky higher-order cases. *)
  and 'd set_of_closures = private {
    function_decls : 'd;
    bound_vars : 'd t Var_within_closure.Map.t;
    invariant_params : Variable.Set.t Variable.Map.t lazy_t;
    size : int option Variable.Map.t lazy_t;
    (** For functions that are very likely to be inlined, the size of the
        function's body. *)
    freshening : closure_freshening;
    (** Any freshening that has been applied to [function_decls]. *)
    direct_call_surrogates : Closure_id.t Closure_id.Map.t;
  }

  and 'd float_array_contents =
    | Contents of 'd t array
    | Unknown_or_mutable

  and 'd float_array = {
    contents : 'd float_array_contents;
    size : int;
  }

  (** Form the type of a join point in the control flow graph where the values
      on the incoming edges have the given types. *)
  val join
     : really_import_approx:('d t -> 'd t)
    -> 'd t
    -> 'd t
    -> 'd t

  val print
     : (Format.formatter -> 'd -> unit)
    -> Format.formatter
    -> 'd t
    -> unit

  val print_descr
     : (Format.formatter -> 'd -> unit)
    -> Format.formatter
    -> 'd descr
    -> unit

  val print_set_of_closures
     : (Format.formatter -> 'd -> unit)
    -> Format.formatter
    -> 'd set_of_closures
    -> unit

  include Constructors_and_accessors
    with type 'd t := 'd t
    with type 'd descr := 'd descr
    with type 'd set_of_closures := 'd set_of_closures
end and Unionable : sig
  module Immediate : sig
    type t = private
      (* CR mshinwell: We could consider splitting these again *)
      | Int of int
      | Char of char
      | Constptr of int

    include Identifiable.S with type t := t

    val represents : t -> int
  end

  type 'd blocks = 'd T.t array Tag.Scannable.Map.t

  type 'd t = private
    | Blocks of 'd blocks
    | Blocks_and_immediates of 'd blocks * Immediate.Set.t
    | Immediates of Immediate.Set.t

  val invariant : _ t -> unit

  val print
     : (Format.formatter -> 'd -> unit)
    -> Format.formatter
    -> 'd t
    -> unit

  val map_blocks : 'd t -> f:('d blocks -> 'd blocks) -> 'd t

  (** Partial ordering:
        Ill_typed_code <= Ok _ <= Anything
  *)
  type 'a or_bottom =
    | Anything
    | Ok of 'a
    | Ill_typed_code

  val join
     : really_import_approx:('d T.t -> 'd T.t)
    -> 'd t
    -> 'd t
    -> 'd t or_bottom

  type 'd singleton = private
    | Block of Tag.Scannable.t * ('d T.t array)
    | Int of int
    | Char of char
    | Constptr of int

  (* CR mshinwell: review names of the following & add comments *)

  val useful : _ t -> bool

  val maybe_is_immediate_value : _ t -> int -> bool

  val ok_for_variant : _ t -> bool

  val is_singleton : _ t -> bool

  val size_of_block : _ t -> int option

  val invalid_to_mutate : _ t -> bool

  val as_int : _ t -> int option

  (** Find the properties that are guaranteed to hold of a value with union type
      at every point it is used. *)
  val flatten : 'd t -> 'd singleton or_bottom
end
