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

(** Flambda language terms that represent statically-allocated objects
    (lifted closed functions, constants, etc). *)

module Constant_defining_value_block_field : sig
  type t =
    | Symbol of Symbol.t
    | Tagged_immediate of Immediate.t
end

module Constant_defining_value : sig
  (** Like a subset of [Flambda0.Named.t], except that instead of [Variable.t]s
      we have [Symbol.t]s, and everything is a constant (i.e. with a fixed value
      known at compile time).  Values of this type describe constants that will
      be directly assigned to symbols in the object file (see below). *)
  type t = private
    | Allocated_const of Allocated_const.t
      (** A single constant.  These are never "simple constants"
          (i.e. of type [Flambda.Const.t]) but are instead more complicated
          constructions. *)
    | Block of Tag.Scannable.t * Constant_defining_value_block_field.t list
      (** A pre-allocated block full of constants (either simple constants
          or references to other constants, see below). *)
    | Set_of_closures of Flambda0.Set_of_closures.t
      (** A closed (and thus constant) set of closures.  (That is to say,
          [free_vars] must be empty.) *)
    | Project_closure of Symbol.t * Closure_id.t
      (** Selection of one closure from a constant set of closures.
          Analogous to the equivalent operation on expressions. *)

  include Identifiable.S with type t := t

  val create_allocated_const : Allocated_const.t -> t

  val create_block
     : Tag.Scannable.t
    -> Constant_defining_value_block_field.t list
    -> t

  val create_set_of_closures : Flambda0.Set_of_closures.t -> t

  val create_project_closure : Symbol.t -> Closure_id.t -> t

  module Mappers : sig
    val map_set_of_closures
       : t
      -> f:(Flambda0.Set_of_closures.t -> Flambda0.Set_of_closures.t)
      -> t
  end
end

(** A "program" is the contents of one compilation unit.  It describes the
    various values that are assigned to symbols (and in some cases fields of
    such symbols) in the object file.  As such, it is closely related to
    the compilation of toplevel modules. *)
module Program_body : sig
  module Initialize_symbol : sig
    (** Type [t] is written to match up precisely with the constraints
        imposed by polymorphic operations such as comparison.  In particular
        whilst we could in theory lift say a pair of a float and an int64, this
        is disallowed, since there is no suitable tag that both prevents the
        GC from scanning the contents and yet allows comparison, hash, etc
        to see through.  (Symbols always have kind [Value] and thus
        [Initialize_symbol] blocks must always be traversable by the GC, even
        if a particular block is not registered in the compilation unit's
        GC roots table, by virtue of it not _needing_ to be scanned.) *)
    type t =
      | Values of {
          tag : Tag.Scannable.t;
          fields :
            (Flambda0.Expr.t * Flambda_kind.scanning * Continuation.t) list;
        }
      | Float of (Flambda0.Expr.t * Continuation.t) list
      | Int32 of Flambda0.Expr.t * Continuation.t
      | Int64 of Flambda0.Expr.t * Continuation.t
      | Nativeint of Flambda0.Expr.t * Continuation.t

    (** Whether an expression with the given return arity may be lifted to
        an [Initialize_symbol]. *)
    val eligible_return_arity : Return_arity.t -> bool

    (** The tag to be put on the statically-allocated block together with a
        flag indicating whether the block must be registered as a root. *)
    val tag_and_scanning : t -> Tag.t * Flambda_kind.scanning
  end

  type t =
    | Let_symbol of Symbol.t * Constant_defining_value.t * t
    (** Define the given symbol to have the given constant value. *)
    | Let_rec_symbol of (Symbol.t * Constant_defining_value.t) list * t
    (** As for [Let_symbol], but recursive.  This is needed to treat examples
        like this, where a constant set of closures is lifted to toplevel:

          let rec f x = f x

        After lifting this produces (in pseudo-Flambda):

          Let_rec_symbol set_of_closures_symbol =
            (Set_of_closures { f x ->
              let applied_function = Symbol f_closure in
              Apply (applied_function, x) })
          and f_closure = Project_closure (set_of_closures_symbol, f)

        Use of [Let_rec_symbol], by virtue of the special handling in
        [Simplify.define_let_rec_symbol_approx], enables the
        approximation of the set of closures to be present in order to
        correctly simplify the [Project_closure] construction.  (See
        [Simplify.simplify_project_closure] for that part.) *)
    | Initialize_symbol of Symbol.t * Initialize_symbol.t * t
    (** Define the given symbol as a constant block following the given
        description; but with a possibly non-constant initializer.  The
        initializer will be executed at most once (from the entry point of
        the compilation unit). *)
    | Effect of Flambda0.Expr.t * Continuation.t * t
    (** Cause the given expression, which may have a side effect, to be
        executed.  The result, which must be of kind [Value], is discarded
        and the zero-arity continuation called.  [Effect] constructions
        are never re-ordered. *)
    | End of Symbol.t
    (** [End] accepts the root symbol: the only symbol that can never be
        eliminated. *)
end

module Program : sig
  type t = {
    imported_symbols : Symbol.Set.t;
    program_body : Program_body.t;
  }

  val free_symbols : t -> Symbol.Set.t

  val print : Format.formatter -> t -> unit
end
