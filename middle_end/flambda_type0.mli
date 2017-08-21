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
  type ('d, 'f) t = private {
    descr : ('d, 'f) descr;
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
  (* CR mshinwell: After the closure reworking patch has been merged and
     the work on classic mode closure approximations has been merged (the
     latter introducing a type of function declarations in this module), then
     the only circularity between this type and Flambda will be for
     Flambda.expr on function bodies. *)
  and ('d, 'f) descr = private 
    | Unknown of Flambda_kind.t * unknown_because_of
    | Union of ('d, 'f) Unionable.t
    | Unboxed_float of Numbers.Float.Set.t
    | Unboxed_int32 of Numbers.Int32.Set.t
    | Unboxed_int64 of Numbers.Int64.Set.t
    | Unboxed_nativeint of Numbers.Nativeint.Set.t
    | Boxed_number of Boxed_number_kind.t * ('d, 'f) t
    | Set_of_closures of ('d, 'f) set_of_closures
    | Closure of ('d, 'f) closure
    | String of string
    | Float_array of ('d, 'f) float_array
    | Bottom
    | Load_lazily of load_lazily

  and ('d, 'f) closure = {
    potential_closures : ('d, 'f) t Closure_id.Map.t;
    (** Map of closures ids to set of closures *)
  } [@@unboxed]

  (* CR-soon mshinwell: add support for the approximations of the results, so we
     can do all of the tricky higher-order cases. *)
  and ('d, 'f) set_of_closures = private {
    function_decls : 'd;
    bound_vars : ('d, 'f) t Var_within_closure.Map.t;
    invariant_params : Variable.Set.t Variable.Map.t lazy_t;
    size : int option Variable.Map.t lazy_t;
    (** For functions that are very likely to be inlined, the size of the
        function's body. *)
    freshening : 'f;
    (** Any freshening that has been applied to [function_decls]. *)
    direct_call_surrogates : Closure_id.t Closure_id.Map.t;
  }

  and ('d, 'f) float_array_contents =
    | Contents of ('d, 'f) t array
    | Unknown_or_mutable

  and ('d, 'f) float_array = {
    contents : ('d, 'f) float_array_contents;
    size : int;
  }

  (** Form the type of a join point in the control flow graph where the values
      on the incoming edges have the given types. *)
  val join
     : really_import_approx:(('d, 'f) t -> ('d, 'f) t)
    -> ('d, 'f) t
    -> ('d, 'f) t
    -> ('d, 'f) t

  val print
     : (Format.formatter -> 'decls -> unit)
    -> (Format.formatter -> 'freshening -> unit)
    -> Format.formatter
    -> ('d, 'f) t
    -> unit

  val print_descr
     : (Format.formatter -> 'decls -> unit)
    -> (Format.formatter -> 'freshening -> unit)
    -> Format.formatter
    -> ('d, 'f) t
    -> unit

  val print_set_of_closures
     : (Format.formatter -> 'decls -> unit)
    -> (Format.formatter -> 'freshening -> unit)
    -> Format.formatter
    -> ('d, 'f) set_of_closures
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

  type ('d, 'f) blocks = ('d, 'f) T.t array Tag.Scannable.Map.t

  type ('d, 'f) t = private
    | Blocks of ('d, 'f) blocks
    | Blocks_and_immediates of ('d, 'f) blocks * Immediate.Set.t
    | Immediates of Immediate.Set.t

  val print
     : (Format.formatter -> 'decls -> unit)
    -> (Format.formatter -> 'freshening -> unit)
    -> Format.formatter
    -> ('d, 'f) t
    -> unit

  (** Partial ordering:
        Ill_typed_code <= Ok _ <= Anything
  *)
  type 'a or_bottom =
    | Anything
    | Ok of 'a
    | Ill_typed_code

  val join
     : really_import_approx:(('d, 'f) T.t -> ('d, 'f) T.t)
    -> ('d, 'f) t
    -> ('d, 'f) t
    -> ('d, 'f) t or_bottom

  type ('d, 'f) singleton = private
    | Block of Tag.Scannable.t * (('d, 'f) T.t array)
    | Int of int
    | Char of char
    | Constptr of int

  (** Find the properties that are guaranteed to hold of a value with union type
      at every point it is used. *)
  val flatten : ('d, 'f) t -> ('d, 'f) singleton or_bottom
end

module type Constructors_and_accessors = sig
  type ('d, 'f) t
  type ('d, 'f) descr
  type ('d, 'f) set_of_closures

  (** Each type has a unique kind. *)
  val kind
     : ('d, 'f) t
    -> really_import_approx:(('d, 'f) t -> ('d, 'f) t)
    -> Flambda_kind.t

  (** Like [kind], but causes a fatal error if the type has not been fully
      resolved. *)
  val kind_exn : (_, _) t -> Flambda_kind.t

  (** Construction of types involving equalities to runtime values. *)
  val unknown : Flambda_kind.t -> unknown_because_of -> (_, _) t
  val int : int -> (_, _) t
  val constptr : int -> (_, _) t
  val char : char -> (_, _) t
  val unboxed_float : float -> (_, _) t
  val unboxed_int32 : Int32.t -> (_, _) t
  val unboxed_int64 : Int64.t -> (_, _) t
  val unboxed_nativeint : Nativeint.t -> (_, _) t
  val boxed_float : float -> (_, _) t
  val boxed_int32 : Int32.t -> (_, _) t
  val boxed_int64 : Int64.t -> (_, _) t
  val boxed_nativeint : Nativeint.t -> (_, _) t
  val mutable_float_array : size:int -> (_, _) t
  val immutable_float_array : ('d, 'f) t array -> ('d, 'f) t
  val mutable_string : length:int -> (_, _) t
  val immutable_string : string -> (_, _) t
  val block : Tag.t -> ('d, 'f) t array -> ('d, 'f) t
  val extern : Export_id.t -> (_, _) t
  val symbol : Symbol.t -> (_, _) t
  val unresolved : unresolved_value -> (_, _) t
  val bottom : (_, _) t

  (** Construction of types without equalities to runtime values. *)
  val any_float : (_, _) t
  val any_unboxed_float : (_, _) t
  val any_unboxed_int32 : (_, _) t
  val any_unboxed_int64 : (_, _) t
  val any_unboxed_nativeint : (_, _) t

  (** Construct a closure type given the type of the corresponding set of
      closures and the closure ID of the closure to be projected from such set.
      [closure_var] and/or [set_of_closures_var] may be specified to augment the
      type with variables that may be used to access the closure value itself,
      so long as they are in scope at the proposed point of use. *)
  val closure
     : ?closure_var:Variable.t
    -> ?set_of_closures_var:Variable.t
    -> ?set_of_closures_symbol:Symbol.t
    -> ('d, 'f) set_of_closures Closure_id.Map.t
    -> ('d, 'f) t

  (** Create a [set_of_closures] structure which can be used for building a type
      describing a set of closures. *)
  val create_set_of_closures
     : function_decls:'d
    -> bound_vars:('d, 'f) t Var_within_closure.Map.t
    -> invariant_params:Variable.Set.t Variable.Map.t lazy_t
    -> freshening:'f
    -> direct_call_surrogates:Closure_id.t Closure_id.Map.t
    -> ('d, 'f) set_of_closures

  (** Construct a set of closures type. [set_of_closures_var] is as for the
      parameter of the same name in [closure], above. *)
  val set_of_closures
     : ?set_of_closures_var:Variable.t
    -> ('d, 'f) set_of_closures
    -> ('d, 'f) t

  (** Change the closure freshening inside a set of closures type. *)
  val update_freshening_of_set_of_closures
     : ('d, 'f) set_of_closures
    -> freshening:'f
    -> ('d, 'f) set_of_closures

  (** Augment an type with a given variable (see comment above). If the type was
      already augmented with a variable, the one passed to this function
      replaces it within the type. *)
  val augment_with_variable : ('d, 'f) t -> Variable.t -> ('d, 'f) t

  (** Like [augment_with_variable], but for symbol information. *)
  val augment_with_symbol : ('d, 'f) t -> Symbol.t -> ('d, 'f) t

  (** Like [augment_with_symbol], but for symbol field information. *)
  val augment_with_symbol_field : ('d, 'f) t -> Symbol.t -> int -> ('d, 'f) t

  (** Replace the description within an type. *)
  val replace_description : ('d, 'f) t -> ('d, 'f) descr -> ('d, 'f) t
end

include module type of T

include Constructors_and_accessors
  with type ('d, 'f) t := ('d, 'f) t
  with type ('d, 'f) descr := ('d, 'f) descr
  with type ('d, 'f) set_of_closures := ('d, 'f) set_of_closures
