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

  module Boxed_or_encoded_number_kind : sig
    (** "Encodings" do not allocate. *)
    type encoded = private
      | Tagged_immediate

    (** "Boxings" allocate. *)
    type boxed = private
      | Float
      | Int32
      | Int64
      | Nativeint

    type t = private
      | Boxed of boxed
      | Encoded of encoded

    include Identifiable.S with type t := t

    (** Return the number of words allocated in total (both inside and
        outside the OCaml heap) for the given boxing or encoding. *)
    val num_words_allocated_excluding_header : t -> int
  end

  type closure_freshening =
    { vars_within_closure : Var_within_closure.t Var_within_closure.Map.t;
      closure_id : Closure_id.t Closure_id.Map.t;
    }

  val print_closure_freshening : Format.formatter -> closure_freshening -> unit

  type unresolved_value =
    | Set_of_closures_id of Set_of_closures_id.t
    | Symbol of Symbol.t

  type unknown_because_of =
    | Unresolved_value of unresolved_value
    | Other

  type load_lazily =
    | Export_id of Export_id.t
    | Symbol of Symbol.t

  type string_contents = private
    | Contents of string
    | Unknown_or_mutable

  type string_ty = private {
    contents : string_contents;
    size : int;
  }

  type 'a with_var_and_symbol = private {
    descr : 'a;
    var : Variable.t option;
    symbol : (Symbol.t * int option) option;
  }

  (** Values of type [t] are known as "Flambda types".  Each Flambda type
      has a unique kind.

      Flambda types may be loaded lazily from .cmx files.  In some cases they
      may be formed into union types. *)
  type t = private
    | Value of ty_value
    | Naked_immediate of ty_naked_immediate
    | Naked_float of ty_naked_float
    | Naked_int32 of ty_naked_int32
    | Naked_int64 of ty_naked_int64
    | Naked_nativeint of ty_naked_nativeint

  and ty_value = of_kind_value ty
  and ty_naked_immediate = of_kind_naked_immediate ty
  and ty_naked_float = of_kind_naked_float ty
  and ty_naked_int32 = of_kind_naked_int32 ty
  and ty_naked_int64 = of_kind_naked_int64 ty
  and ty_naked_nativeint = of_kind_naked_nativeint ty

  and 'a ty = 'a maybe_unresolved with_var_and_symbol

  and resolved_t = private
    | Value of resolved_ty_value
    | Naked_immediate of resolved_ty_naked_immediate
    | Naked_float of resolved_ty_naked_float
    | Naked_int32 of resolved_ty_naked_int32
    | Naked_int64 of resolved_ty_naked_int64
    | Naked_nativeint of resolved_ty_naked_nativeint

  and ty_resolved_value = of_kind_value resolved_ty
  and ty_resolved_naked_immediate = of_kind_naked_immediate resolved_ty
  and ty_resolved_naked_float = of_kind_naked_float resolved_ty
  and ty_resolved_naked_int32 = of_kind_naked_int32 resolved_ty
  and ty_resolved_naked_int64 = of_kind_naked_int64 resolved_ty
  and ty_resolved_naked_nativeint = of_kind_naked_nativeint resolved_ty

  and 'a resolved_ty = 'a or_unknown_or_bottom with_var_and_symbol

  and 'a maybe_unresolved = private
    | Ok of 'a or_unknown_or_bottom
    | Load_lazily of load_lazily

  (** For each kind (cf. [Flambda_kind]) there is a partial order on types.
      [Bottom] is the unique least element and [Unknown] is the unique top
      element. *)
  and 'a or_unknown_or_bottom = private
    | Unknown of unresolved_value
    (** "Any value can flow to this point". *)
    | Ok of 'a
    | Bottom
    (** "No value can flow to this point". *)

  and of_kind_value = private
    | Singleton of of_kind_value_singleton
    | Union of of_kind_value with_var_and_symbol
        * of_kind_value with_var_and_symbol
    (** Note that [Union]s are statically prohibited from containing
        [Unknown]s or [Bottom]s at the top level.  This simplifies code
        that traverses union types. *)

  and of_kind_value_singleton = private
    | Boxed_or_encoded_number of Boxed_or_encoded_number_kind.t * ty_value
    | Block of Tag.Scannable.t * (ty_value array)
    | Set_of_closures of set_of_closures
    | Closure of {
        set_of_closures : ty_value;
        closure_id : Closure_id.t
      }
    | String of string_ty
    | Float_array of float_array_ty

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

  and float_array_ty = private {
    contents : float_array_contents;
    size : int;
  }

  and of_kind_naked_immediate =
    | Naked_int of Targetint.t
    | Naked_char of Char.t
    | Naked_constptr of Targetint.t

  and of_kind_naked_float =
    | Naked_float of float

  and of_kind_naked_int32 =
    | Naked_int32 of Int32.t

  and of_kind_naked_int64 =
    | Naked_int64 of Int64.t

  and of_kind_naked_nativeint =
    | Naked_nativeint of Targetint.t

  val print : Format.formatter -> t -> unit

  (** Each type has a unique kind. *)
  val kind : t -> Flambda_kind.t

  (** Construct a top type for the given kind ("any value of the given kind
      can flow to this point").  (The [unknown_because_of] reason is ignored
      when considering the partial ordering on types.) *)
  val unknown : Flambda_kind.t -> unknown_because_of -> t

  (** The bottom type for the given kind ("no value can flow to this point"). *)
  val bottom : Flambda_kind.t -> t

  (** Construction of types involving equalities to runtime values. *)
  val tagged_int : Targetint.t -> t
  val tagged_constptr : Targetint.t -> t
  val tagged_char : char -> t
  val untagged_int : Targetint.t -> t
  val untagged_constptr : Targetint.t -> t
  val untagged_char : char -> t
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
  val block : Tag.Scannable.t -> t array -> t

  (** Construction of types that link to other types which have not yet
      been loaded into memory (from a .cmx file). *)
  val export_id_loaded_lazily : Flambda_kind.t -> Export_id.t -> t
  val symbol_loaded_lazily : Flambda_kind.t -> Symbol.t -> t

  (** Construction of types without equalities to runtime values. *)
  val any_tagged_immediate : unit -> t
  val any_boxed_float : unit -> t
  val any_boxed_int32 : unit -> t
  val any_boxed_int64 : unit -> t
  val any_boxed_nativeint : unit -> t
  val any_untagged_immediate : unit -> t
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

  (** Augment the toplevel of the given type with the given variable.  If the
      type was already augmented with a variable, the one passed to this
      function replaces it. *)
  val augment_with_variable : t -> Variable.t -> t

  (** Like [augment_with_variable], but for symbol information.  The
      field index is set to [None]. *)
  val augment_with_symbol : t -> Symbol.t -> t

  (** Like [augment_with_symbol], but with a user-supplied field index. *)
  val augment_with_symbol_field : t -> Symbol.t -> field:int -> t

  (** Replace the variable at the toplevel of a given type. *)
  val replace_variable : t -> Variable.t option -> t

  (** Operations which need a function to resolve [Load_lazily] constructors
      at the toplevel of types.  These operations are re-exported in
      [Flambda_type] once the definition of [import_type] can be provided. *)
  module type Operations_needing_import_type = sig
    type 'a with_import_type

(*
    (** Attempt to use a value kind to refine a type. *)
    val refine_using_value_kind : t -> Lambda.value_kind -> t
*)

    (** Free variables in a type. *)
    val free_variables : (t -> Variable.Set.t) with_import_type

    (** Least upper bound of two types. *)
    val join : (t -> t -> t) with_import_type

    type cleaning_spec =
      | Available
      | Available_different_name of Variable.t
      | Unavailable
(*
    (** Adjust a type so that all of the free variables it references are in
        scope in some context. The context is expressed by a function that says
        whether the variable is available under its existing name, available
        under another name, or unavailable. *)
    val clean : (t -> (Variable.t -> cleaning_spec) -> t) with_import_type
*)
  end

  module Ops : Operations_needing_import_type
    with type 'a with_import_type = import_type:(t -> t) -> 'a
end
