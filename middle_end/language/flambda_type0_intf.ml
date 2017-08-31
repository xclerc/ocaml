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

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module type S = sig
  type function_declarations

  module Naked_number : sig
    type t =
      | Int of Targetint.Set.t
      | Char of Misc.Stdlib.Char.Set.t
      | Constptr of Targetint.Set.t
      | Float of Numbers.Float.Set.t
      | Int32 of Numbers.Int32.Set.t
      | Int64 of Numbers.Int64.Set.t
      | Nativeint of Numbers.Nativeint.Set.t

    include Identifiable.S with type t := t
  end

  module Boxed_or_encoded_number_kind : sig
    (** "Encodings" do not allocate. *)
    type encoded =
      | Tagged_int

    (** "Boxings" allocate. *)
    type boxed =
      | Float
      | Int32
      | Int64
      | Nativeint

    type t =
      | Boxed of boxed
      | Encoded of encoded

    include Identifiable.S with type t := t

    (** Return the number of words allocated in total (both inside and
        outside the OCaml heap) for the given boxing or encoding. *)
    val num_words_allocated_excluding_header : t -> int
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

  type string_contents = private
    | Contents of string
    | Unknown_or_mutable

  type string_ty = private {
    contents : string_contents;
    size : int;
  }

  val print_closure_freshening : Format.formatter -> closure_freshening -> unit

  (** Values of type [t] are known as "Flambda types".
      They may be loaded lazily from .cmx files and formed into union types.

      Values of type [singleton] form a partial order.

      [Bottom] is the unique least element.
      The [Unknown (k, _)] values form the greatest elements.

      The intuitive meanings of these distinguished elements are:
      - [Bottom]: "no value can flow to this point".
      - [Unknown (k, _)]: "any value of kind [k] might flow to this point".
  *)
  type t = private {
    descr : descr;
    (** The main description of the type. *)
    var : Variable.t option;
    (** An optional equality to a variable. *)
    symbol : (Symbol.t * int option) option;
    (** An optional equality to a symbol, or if the integer field number is
        specified, to a field of a symbol. *)
  } 

  and descr =
    | Ok of singleton_or_union
    | Load_lazily of load_lazily

  and singleton_or_union =
    | Singleton of singleton
    | Union of t * t

  and singleton =
    | Unknown of Flambda_kind.Basic.t * unknown_because_of
    | Naked_number of Naked_number.t
    | Boxed_or_encoded_number of Boxed_or_encoded_number_kind.t * t
    | Block of t array Tag.Scannable.Map.t
    | Set_of_closures of set_of_closures
    | Closure of closure
    | String of string_ty
    | Float_array of float_array
    | Bottom

  and closure = private {
    potential_closures : t Closure_id.Map.t;
    (** Map of closures ids to set of closures *)
  } [@@unboxed]

  (* CR-soon mshinwell: add support for the approximations of the results,
     so we can do all of the tricky higher-order cases. *)
  and set_of_closures = private {
    function_decls : function_declarations;
    bound_vars : t Var_within_closure.Map.t;
    invariant_params : Variable.Set.t Variable.Map.t lazy_t;
    size : int option Variable.Map.t lazy_t;
    (** For functions that are very likely to be inlined, the size of the
        function's body. *)
    freshening : closure_freshening;
    (** Any freshening that has been applied to [function_decls]. *)
    direct_call_surrogates : Closure_id.t Closure_id.Map.t;
  }

  and float_array_contents = private
    | Contents of t array
    | Unknown_or_mutable

  and float_array = private {
    contents : float_array_contents;
    size : int;
  }

  (** Least upper bound of two types. *)
  val join
     : really_import_approx:(t -> t)
    -> t
    -> t
    -> t

  (** Greatest lower bound of two types. *)
  val meet
     : really_import_approx:(t -> t)
    -> t
    -> t
    -> t

  val print
     : Format.formatter
    -> t
    -> unit

  val print_descr
     : Format.formatter
    -> descr
    -> unit

  val print_set_of_closures
     : Format.formatter
    -> set_of_closures
    -> unit

  (** Each type has a unique kind. *)
  val kind
     : t
    -> really_import_approx:(t -> t)
    -> Flambda_kind.t

  (** Like [kind], but causes a fatal error if the type has not been fully
      resolved. *)
  val kind_exn : t -> Flambda_kind.t

  (** Construct one of the various top types ("any value of the given kind
      can flow to this point"). *)
  val unknown : Flambda_kind.Basic.t -> unknown_because_of -> t

  (** The unique bottom type ("no value can flow to this point"). *)
  val bottom : unit -> t

  (** Construction of types involving equalities to runtime values. *)
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
  val mutable_string : size:int -> t
  val immutable_string : string -> t
  val block : Tag.t -> t array -> t

  (** Construction of types that link to other types which have not yet
      been loaded into memory (from a .cmx file). *)
  val export_id_loaded_lazily : Export_id.t -> t
  val symbol_loaded_lazily : Symbol.t -> t

  (** Construction of types without equalities to runtime values. *)
  val any_boxed_float : unit -> t
  val any_unboxed_float : unit -> t
  val any_unboxed_int32 : unit -> t
  val any_unboxed_int64 : unit -> t
  val any_unboxed_nativeint : unit -> t

  (** Construct a closure type given the type of the corresponding set of
      closures and the closure ID of the closure to be projected from such
      set. [closure_var] and/or [set_of_closures_var] may be specified to
      augment the type with variables that may be used to access the closure
      value itself, so long as they are in scope at the proposed point of
      use. *)
  (* CR mshinwell: bad name? *)
  val closure
     : ?closure_var:Variable.t
    -> ?set_of_closures_var:Variable.t
    -> ?set_of_closures_symbol:Symbol.t
    -> set_of_closures Closure_id.Map.t
    -> t

  (** Create a [set_of_closures] structure which can be used for building a
      type describing a set of closures. *)
  val create_set_of_closures
     : function_decls:function_declarations
    -> size:int option Variable.Map.t lazy_t
    -> bound_vars:t Var_within_closure.Map.t
    -> invariant_params:Variable.Set.t Variable.Map.t lazy_t
    -> freshening:closure_freshening
    -> direct_call_surrogates:Closure_id.t Closure_id.Map.t
    -> set_of_closures

  (** Construct a set of closures type. [set_of_closures_var] is as for the
      parameter of the same name in [closure], above. *)
  val set_of_closures
     : ?set_of_closures_var:Variable.t
    -> set_of_closures
    -> t

  (** Change the closure freshening inside a set of closures type. *)
  val update_freshening_of_set_of_closures
     : set_of_closures
    -> freshening:closure_freshening
    -> set_of_closures

  (** Augment an type with a given variable (see comment above). If the type
      was already augmented with a variable, the one passed to this function
      replaces it within the type. *)
  val augment_with_variable : t -> Variable.t -> t

  (** Replace the variable at the toplevel of a given type. *)
  val update_variable : t -> Variable.t option -> t

  (** Like [augment_with_variable], but for symbol information. *)
  val augment_with_symbol : t -> Symbol.t -> t

  (** Like [augment_with_symbol], but for symbol field information. *)
  val augment_with_symbol_field : t -> Symbol.t -> int -> t

  (** Replace the description within an type. *)
  val replace_description : t -> descr -> t

  (** Attempt to use a value kind to refine a type. *)
  val refine_using_value_kind : t -> Lambda.value_kind -> t

  (** Free variables in a type. *)
  val free_variables : t -> Variable.Set.t

  type cleaning_spec =
    | Available
    | Available_different_name of Variable.t
    | Unavailable

  (** Adjust a type so that all of the free variables it references are in
      scope in some context. The context is expressed by a function that says
      whether the variable is available under its existing name, available
      under another name, or unavailable. *)
  val clean
     : t
    -> (Variable.t -> cleaning_spec)
    -> t
end

(*
    module Immediate : sig
      (** These immediate values are always tagged. *)
      type t = private
        (* CR mshinwell: We could consider splitting these again *)
        | Int of int
        | Char of char
        | Constptr of int

      include Identifiable.S with type t := t

      val represents : t -> int
    end

    type blocks = T.t array Tag.Scannable.Map.t

    type t = private
      | Blocks of blocks
      | Blocks_and_immediates of blocks * Immediate.Set.t

    val invariant : t -> unit

    val print
       : Format.formatter
      -> t
      -> unit

    val map_blocks : t -> f:(blocks -> blocks) -> t

    (** Partial ordering:
          Bottom <= Ok _ <= Unknown
    *)
    type 'a or_bottom =
      | Unknown
      | Ok of 'a
      | Bottom

    val join
      : really_import_approx:(T.t -> T.t)
      -> t
      -> t
      -> t or_bottom

    type singleton = private
      | Block of Tag.Scannable.t * (T.t array)
      | Int of int
      | Char of char
      | Constptr of int

    (* CR mshinwell: review names of the following & add comments *)

    val useful : t -> bool

    val maybe_is_immediate_value : t -> int -> bool

    val ok_for_variant : t -> bool

    val is_singleton : t -> bool

    val size_of_block : t -> int option

    val invalid_to_mutate : t -> bool

    val as_int : t -> int option

    (** Find the properties that are guaranteed to hold of a value with union
        type at every point it is used. *)
    val flatten : t -> singleton or_bottom
  end

  include module type of struct include T end
end
*)
