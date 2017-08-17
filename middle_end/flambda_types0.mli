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
    terms at runtime.
    This type system is in fact parameterised over the type of Flambda
    expressions. *)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module Boxed_number_kind : sig
  type t = private
    | Float
    | Int32
    | Int64
    | Nativeint
end

type value_string = {
  contents : string option;  (* [None] if unknown or mutable *)
  size : int;
}

type unresolved_value =
  | Set_of_closures_id of Set_of_closures_id.t
  | Symbol of Symbol.t

type unknown_because_of =
  | Unresolved_value of unresolved_value
  | Other

(* CR-someday mshinwell: move to separate module and make [Identifiable].
  (Or maybe nearly Identifiable; having a special map that enforces invariants
  might be good.) *)
(* CR-someday mshinwell: This should perhaps be altered so that the
   specialisation isn't just to a variable, or some particular projection,
   but is instead to an actual approximation (which would be enhanced to
   describe the projection too). *)
type specialised_to = {
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

type specialised_args = specialised_to Variable.Map.t

(** A value of type [t] corresponds to an "approximation" of the result of
    a computation in the program being compiled.  That is to say, it
    represents what knowledge we have about such a result at compile time.
    The simplification pass exploits this information to partially evaluate
    computations.

    At a high level, an approximation for a value [v] has three parts:
    - the "description" (for example, "the constant integer 42");
    - an optional variable;
    - an optional symbol or symbol field.
    If the variable (resp. symbol) is present then that variable (resp.
    symbol) may be used to obtain the value [v].

    The exact semantics of the variable and symbol fields follows.

    Approximations are deduced at particular points in an expression tree,
    but may subsequently be propagated to other locations.

    At the point at which an approximation is built for some value [v], we can
    construct a set of variables (call the set [S]) that are known to alias the
    same value [v].  Each member of [S] will have the same or a more precise
    [descr] field in its approximation relative to the approximation for [v].
    (An increase in precision may currently be introduced for pattern
    matches.)  If [S] is non-empty then it is guaranteed that there is a
    unique member of [S] that was declared in a scope further out ("earlier")
    than all other members of [S].  If such a member exists then it is
    recorded in the [var] field.  Otherwise [var] is [None].

    Analogous to the construction of the set [S], we can construct a set [T]
    consisting of all symbols that are known to alias the value whose
    approximation is being constructed.  If [T] is non-empty then the
    [symbol] field is set to some member of [T]; it does not matter which
    one.  (There is no notion of scope for symbols.)

    Note about mutable blocks:

    Mutable blocks are always represented by [Unknown] or
    [Bottom].  Any other approximation could leave the door open to
    a miscompilation.   Such bad scenarios are most likely a user using
    [Obj.magic] or [Obj.set_field] in an inappropriate situation.
    Such a situation might be:
    [let x = (1, 1) in
     Obj.set_field (Obj.repr x) 0 (Obj.repr 2);
     assert(fst x = 2)]
    The user would probably expect the assertion to be true, but the
    compiler could in fact propagate the value of [x] across the
    [Obj.set_field].

    Insisting that mutable blocks have [Unknown] or [Value_bottom]
    approximations certainly won't always prevent this kind of error, but
    should help catch many of them.

    It is possible that there may be some false positives, with correct
    but unreachable code causing this check to fail.  However the likelihood
    of this seems sufficiently low, especially compared to the advantages
    gained by performing the check, that we include it.

    An example of a pattern that might trigger a false positive is:
    [type a = { a : int }
     type b = { mutable b : int }
     type _ t =
       | A : a t
       | B : b t
     let f (type x) (v:x t) (r:x) =
       match v with
       | A -> r.a
       | B -> r.b <- 2; 3

    let v =
    let r =
      ref A in
      r := A; (* Some pattern that the compiler can't understand *)
      f !r { a = 1 }]
    When inlining [f], the B branch is unreachable, yet the compiler
    cannot prove it and must therefore keep it.
*)

module rec T : sig
  type ('decls, 'freshening) t = private {
    descr : descr;
    var : Variable.t option;
    symbol : (Symbol.t * int option) option;
  }

  (** Approximations form a partial order.

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
    | Unknown of Value_kind.t * unknown_because_of
    | Union of Unionable.t
    (* CR mshinwell: Should we call this "Unboxed_float" and the same for
       the others? *)
    | Float of Float.Set.t
    | Int32 of Int32.Set.t
    | Int64 of Int64.Set.t
    | Nativeint of Nativeint.Set.t
    | Boxed_number of boxed_number_kind * t
    | Set_of_closures of ('decls, 'freshening) value_set_of_closures
    | Closure of ('decls, 'freshening) value_closure
    | String of value_string
    | Float_array of value_float_array
    | Extern of Export_id.t
    | Symbol of Symbol.t
    | Unresolved of unresolved_value
    | Bottom

  and ('decls, 'freshening) value_closure = {
    potential_closures : ('decls, 'freshening) t Closure_id.Map.t;
    (** Map of closures ids to set of closures *)
  } [@@unboxed]

  (* CR-soon mshinwell: add support for the approximations of the results, so we
     can do all of the tricky higher-order cases. *)
  and ('decls, 'freshening) value_set_of_closures = private {
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

  and value_float_array_contents =
    | Contents of t array
    | Unknown_or_mutable

  and value_float_array = {
    contents : value_float_array_contents;
    size : int;
  }

  (* CR-soon mshinwell for pchambart: Add comment describing semantics.  (Maybe
     we should move the comment from the .ml file into here.) *)
  val join : really_import_approx:(t -> t) -> t -> t -> t

  val print : Format.formatter -> t -> unit
  val print_descr : Format.formatter -> descr -> unit
  val print_value_set_of_closures
    : Format.formatter
    -> value_set_of_closures
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

  (** Values of type [t] represent unions of approximations, that is to say,
      disjunctions of properties known to hold of a value at one or more of
      its use points. *)
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
      approximation at every point it is used. *)
  val flatten : t -> singleton or_bottom
end

include (module type of T)

module type Constructors_and_accessors = sig
  (** Extraction of the description of approximation(s). *)
  val descr : t -> descr
  val descrs : t list -> descr list

  val create_set_of_closures
    : function_decls:Flambda.function_declarations
    -> bound_vars:t Var_within_closure.Map.t
    -> invariant_params:Variable.Set.t Variable.Map.t lazy_t
    -> specialised_args:Flambda.specialised_to Variable.Map.t
    -> freshening:Freshening.Project_var.t
    -> direct_call_surrogates:Closure_id.t Closure_id.Map.t
    -> set_of_closures

  val update_freshening_of_set_of_closures
    : set_of_closures
    -> freshening:Freshening.Project_var.t
    -> set_of_closures

  (** Basic construction of approximations. *)
  val unknown : kind.t -> unknown_because_of -> t
  val int : int -> t
  val char : char -> t
  val boxed_float : float -> t
  val any_float : t
  val any_unboxed_float : t
  val any_unboxed_int32 : t
  val any_unboxed_int64 : t
  val any_unboxed_nativeint : t
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
  val boxed_int : 'i boxed_int -> 'i -> t
  val constptr : int -> t
  val block : Tag.Scannable.t -> t array -> t
  val extern : Export_id.t -> t
  val symbol : Symbol.t -> t
  val bottom : t
  val unresolved : unresolved_value -> t

  (** Construct a closure approximation given the approximation of the
      corresponding set of closures and the closure ID of the closure to
      be projected from such set.  [closure_var] and/or [set_of_closures_var]
      may be specified to augment the approximation with variables that may
      be used to access the closure value itself, so long as they are in
      scope at the proposed point of use. *)
  val value_closure
    : ?closure_var:Variable.t
    -> ?set_of_closures_var:Variable.t
    -> ?set_of_closures_symbol:Symbol.t
    -> value_set_of_closures Closure_id.Map.t
    -> t

  (** Construct a set of closures approximation.  [set_of_closures_var] is as for
      the parameter of the same name in [value_closure], above. *)
  val value_set_of_closures
    : ?set_of_closures_var:Variable.t
    -> value_set_of_closures
    -> t

  (** Take the given constant and produce an appropriate approximation for it
      together with an Flambda term representing it. *)
  val make_const_int_named : int -> Flambda.named * t
  val make_const_char_named : char -> Flambda.named * t
  val make_const_ptr_named : int -> Flambda.named * t
  val make_const_bool_named : bool -> Flambda.named * t
  val make_const_float_named : float -> Flambda.named * t
  val make_const_boxed_int_named : 'i boxed_int -> 'i -> Flambda.named * t

  (** Augment an approximation with a given variable (see comment above).
      If the approximation was already augmented with a variable, the one
      passed to this function replaces it within the approximation. *)
  val augment_with_variable : t -> Variable.t -> t

  (** Like [augment_with_variable], but for symbol information. *)
  val augment_with_symbol : t -> Symbol.t -> t

  (** Like [augment_with_symbol], but for symbol field information. *)
  val augment_with_symbol_field : t -> Symbol.t -> int -> t

  (** Replace the description within an approximation. *)
  val replace_description : t -> descr -> t

  (** Improve the description by taking the kind into account *)
  val augment_with_kind : t -> Lambda.value_kind -> t

  (** Improve the kind by taking the description into account *)
  val augment_kind_with_approx : t -> Lambda.value_kind -> Lambda.value_kind
end

include S
