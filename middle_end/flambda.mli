(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

(** Intermediate language used for tree-based analysis and optimization.

    Flambda expressions augment Ilambda expressions by adding constructs for:
    - the construction and manipulation of closures; and
    - accessing constants that have been lifted to static data.

    The Flambda "program" type, described below, wraps Flambda expressions to
    describe the overall structure of a compilation unit.
*)

type return_arity = Flambda_kind.t list

(** Whether the callee in a function application is known at compile time. *)
type call_kind =
  | Indirect
  | Direct of {
      closure_id : Closure_id.t;
      return_arity : return_arity;
      (** [return_arity] describes what the callee returns.  It matches up with
          the arity of [continuation] in the enclosing [apply] record. *)
    }

(** Simple constants.  ("Structured constants" are rewritten to invocations
    of [Pmakeblock] so that they easily take part in optimizations.) *)
module Const : sig
  type t =
    | Int of int
    | Char of char
    (** [Char] is kept separate from [Int] to improve printing *)
    | Const_pointer of int
    (** [Const_pointer] is an immediate value of a type whose values may be
      boxed (typically a variant type with both constant and non-constant
      constructors). *)
    | Unboxed_float of float
    | Unboxed_int32 of Int32.t
    | Unboxed_int64 of Int64.t
    | Unboxed_nativeint of Nativeint.t

  include Identifiable.S with type t := t
end

type const = Const.t

type apply_kind =
  | Function
  | Method of { kind : Lambda.meth_kind; obj : Variable.t; }

(** The application of a function (or method on a given object) to a list of
    arguments. *)
type apply = {
  kind : apply_kind;
  (* CR-soon mshinwell: rename func -> callee, and
     lhs_of_application -> callee *)
  func : Variable.t;
  continuation : Continuation.t;
  (** Where to send the result of the application. *)
  args : Variable.t list;
  call_kind : call_kind;
  dbg : Debuginfo.t;
  inline : Lambda.inline_attribute;
  (** Instructions from the source code as to whether the callee should
      be inlined. *)
  specialise : Lambda.specialise_attribute;
  (** Instructions from the source code as to whether the callee should
      be specialised. *)
}

(** The update of a mutable variable.  Mutable variables are distinct from
    immutable variables in Flambda. *)
type assign = {
  being_assigned : Mutable_variable.t;
  new_value : Variable.t;
}

(** For details on these types, see projection.mli. *)
type project_closure = Projection.project_closure
type move_within_set_of_closures = Projection.move_within_set_of_closures
type project_var = Projection.project_var

(** See [free_vars] and [specialised_args], below. *)
type free_var = {
  var : Variable.t;
  projection : Projection.t option;
}

type free_vars = free_var Variable.Map.t

(** Actions affecting exception traps on the stack.  These are always
    associated with an [Apply_cont] node; the trap action is executed before
    the application of the continuation.

    The [Trap_id] values tie up corresponding pairs of pushes and pops
    irrespective of the handler (which might be shared).  [Pop] may not appear
    to need the [exn_handler] value during Flambda passes---but in fact it
    does, since it compiles to a reference to such continuation, and must
    not be moved out of its scope.

    Beware: continuations cannot be used both as an exception handler and as
    a normal continuation (since continuations used as exception handlers
    use a calling convention that may differ from normal).
*)
type trap_action =
  | Push of { id : Trap_id.t; exn_handler : Continuation.t; }
  (* CR mshinwell: Think about whether we really need the trap IDs now *)
  | Pop of { id : Trap_id.t; exn_handler : Continuation.t; }

(** With the exception of applications of primitives ([Prim]), Flambda terms
    are in CPS.

    Primitives being in direct style combined with care during CPS conversion
    should keep administrative redexes to a minimum.

    The CPS representation ensures that:
    - every intermediate value (and in particular every potential constant
      that we may want to lift) has a name;
    - there are no nested "let"s or complicated expressions as the defining
      expression of a "let";
    - every point to which we might wish to jump has a name;
    - no re-normalisation of terms is required when substituting an
      application for an inlined body (unlike in ANF form).  This is important
      for compilation speed.

    See comments on the [let_cont] type below for information about the form
    of continuations used.

    Exception flow is currently handled (for simplicity) using explicit push
    and pop trap operations (see above) rather than double-barrelled CPS.

    Note: All bound variables in Flambda terms must be distinct.
    [Flambda_invariants] verifies this. *)
type t =
  | Let of let_expr
  | Let_mutable of let_mutable
  | Let_cont of let_cont
  | Apply of apply
  | Apply_cont of Continuation.t * trap_action option * Variable.t list
  | Switch of Variable.t * switch
  | Proved_unreachable

(** Values of type [named] will always be [let]-bound to a [Variable.t]. *)
and named =
  | Var of Variable.t
  | Const of const
  | Prim of Lambda.primitive * Variable.t list * Debuginfo.t
  | Assign of assign
  | Read_mutable of Mutable_variable.t
  | Symbol of Symbol.t
  | Read_symbol_field of Symbol.t * int
  (** During the lifting of [let] bindings to [program] constructions after
      closure conversion, we generate symbols and their corresponding
      definitions (which may or may not be constant), together with field
      accesses to such symbols.  We would like it to be the case that such
      field accesses are simplified to the relevant component of the
      symbol concerned.  (The rationale is to generate efficient code and
      share constants as expected: see e.g. tests/asmcomp/staticalloc.ml.)
      The components of the symbol would be identified by other symbols.
      This sort of access pattern is feasible because the top-level structure
      of symbols is statically allocated and fixed at compile time.
      It may seem that [Prim (Pfield, ...)] expressions could be used to
      perform the field accesses.  However for simplicity, to avoid having to
      keep track of properties of individual fields of blocks,
      [Inconstant_idents] never deems a [Prim (Pfield, ...)] expression to be
      constant.  This would in general prevent field accesses to symbols from
      being simplified in the way we would like, since [Lift_constants] would
      not assign new symbols (i.e. the things we would like to simplify to)
      to the various projections from the symbols in question.
      To circumvent this problem we use [Read_symbol_field] when generating
      projections from the top level of symbols.  Owing to the properties of
      symbols described above, such expressions may be eligible for declaration
      as constant by [Inconstant_idents] (and thus themselves lifted to another
      symbol), without any further complication.
      [Read_symbol_field] may only be used when the definition of the symbol
      is in scope in the [program].  For external unresolved symbols, [Pfield]
      may still be used; it will be changed to [Read_symbol_field] by
      [Simplify] when (and if) the symbol is imported. *)
  | Allocated_const of Allocated_const.t
  | Set_of_closures of set_of_closures
  | Project_closure of project_closure
  | Move_within_set_of_closures of move_within_set_of_closures
  | Project_var of project_var

(* CR-someday mshinwell: Since we lack expression identifiers on every term,
   we should probably introduce [Mutable_var] into [named] if we introduce
   more complicated analyses on these in the future.  Alternatively, maybe
   consider removing mutable variables altogether. *)

and let_expr = private {
  var : Variable.t;
  kind : Flambda_kind.t;
  defining_expr : named;
  body : t;
  (* CR-someday mshinwell: we could consider having these be keys into some
     kind of global cache, to reduce memory usage. *)
  free_vars_of_defining_expr : Variable.Set.t;
  (** A cache of the free variables in the defining expression of the [let]. *)
  free_vars_of_body : Variable.Set.t;
  (** A cache of the free variables of the body of the [let].  This is an
      important optimization. *)
}

and let_mutable = {
  var : Mutable_variable.t;
  initial_value : Variable.t;
  contents_kind : Lambda.value_kind;
  body : t;
}

(** Values of type [let_cont] represent the definitions of continuations:
      let_cont [name] [args] = [handler] in [body]
    or in other words:
      [body]
      where [name] [args] = [handler]

    - Continuations are second-class.
    - Continuations do not capture variables.
    - Continuations may be (mutually-)recursive.

    It is an error to mark a continuation that might be recursive as
    non-recursive.  The converse is safe.
*)
and let_cont = {
  body : t;
  handlers : let_cont_handlers;
}
(* CR mshinwell: We need to add the following invariant checks:
   1. Usual checks on [let_cont.specialised_args].
   2. Also on that specialised_args map, that only [Field] projections are
      used.  (The other projections are all things to do with closures.)  We
      might consider changing the type somehow to make this statically
      checked.
   3. Specialised args are only allowed to have [var = None] in the
      [specialised_to] record iff they are non-specialised parameters of a
      continuation.
   4. Exception handlers should be "Handlers" with a single non-recursive
      continuation.
*)

(** Note: any continuation used as an exception handler must be non-recursive
    by the point it reaches [Flambda_to_clambda].  (This means that it is
    permissible to introduce mutual recursion through stubs associated with
    such continuations, so long as [Simplify] is run afterwards
    to inline them out and turn the resulting single [Recursive] handler into
    a [Nonrecursive] one. *)
and let_cont_handlers =
  | Nonrecursive of { name : Continuation.t; handler : continuation_handler; }
  | Recursive of continuation_handlers

and continuation_handlers =
  continuation_handler Continuation.Map.t

and continuation_handler = {
  params : Parameter.t list;
  equations : Projection.t Variable.Map.t;
  stub : bool;
  is_exn_handler : bool;
  (** Continuations used as exception handlers must always be [Nonrecursive]
      and must have exactly one argument.  To enable identification of them
      in passes not invoked from [Simplify] (where they could be
      identified by looking at the [Apply_cont]s that reference them) they
      are marked explicitly.
      (Relevant piece of background info: the backend cannot compile
      simultaneously-defined continuations when one or more of them is an
      exception handler.)
  *)
  handler : t;
}

(** The representation of a set of function declarations (possibly mutually
    recursive).  Such a set encapsulates the declarations themselves,
    information about their defining environment, and information used
    specifically for optimization.
    Before a function can be applied it must be "projected" from a set of
    closures to yield a "closure".  This is done using [Project_closure]
    (see above).  Given a closure, not only can it be applied, but information
    about its defining environment can be retrieved (using [Project_var],
    see above).
    At runtime, a [set_of_closures] corresponds to an OCaml value with tag
    [Closure_tag] (possibly with inline [Infix_tag](s)).  As an optimization,
    an operation ([Move_within_set_of_closures]) is provided (see above)
    which enables one closure within a set to be located given another
    closure in the same set.  This avoids keeping a pointer to the whole set
    of closures alive when compiling, for example, mutually-recursive
    functions.
*)
and set_of_closures = private {
  function_decls : function_declarations;
  (* CR-soon mshinwell: consider renaming [free_vars].  Also, it's still really
     confusing which side of this map to use when.  "Vars bound by the
     closure" is the domain.
     Another example of when this is confusing:
      let bound_vars_approx =
        Variable.Map.map (Env.find_approx env) set.free_vars
      in
     in [Build_export_info]. *)
  (* CR-soon mshinwell: I'd like to arrange these maps so that it's impossible
     to put invalid projection information into them (in particular, so that
     we enforce that the relation stays within the domain of the map). *)
  free_vars : free_vars;
  (** Mapping from all variables free in the body of the [function_decls] to
      variables in scope at the definition point of the [set_of_closures].
      The domain of this map is sometimes known as the "variables bound by
      the closure". *)
  direct_call_surrogates : Variable.t Variable.Map.t;
  (** If [direct_call_surrogates] maps [fun_var1] to [fun_var2] then direct
      calls to [fun_var1] should be redirected to [fun_var2].  This is used
      to reduce the overhead of transformations that introduce wrapper
      functions (which will be inlined at direct call sites, but will
      penalise indirect call sites).
      [direct_call_surrogates] may not be transitively closed. *)
  (* CR-soon mshinwell: move [equations] into [function_declarations] *)
  equations : Projection.t Variable.Map.t;
}

and function_declarations = private {
  set_of_closures_id : Set_of_closures_id.t;
  (** An identifier (unique across all Flambda trees currently in memory)
      of the set of closures associated with this set of function
      declarations. *)
  set_of_closures_origin : Set_of_closures_origin.t;
  (** An identifier of the original set of closures on which this set of
      function declarations is based.  Used to prevent different
      specialisations of the same functions from being inlined/specialised
      within each other. *)
  funs : function_declaration Variable.Map.t;
  (** The function(s) defined by the set of function declarations.  The
      keys of this map are often referred to in the code as "fun_var"s. *)
}

and function_declaration = private {
  closure_origin : Closure_origin.t;
  (** The closure from which this function declaration originally came.
      Used as a backstop against unbounded recursion during inlining. *)
  continuation_param : Continuation.t;
  (** The continuation parameter of the function, i.e. to where we must jump
      once the result of the function has been computed.  If the continuation
      takes more than one argument then the backend will compile the function
      so that it returns multiple values. *)
  return_arity : return_arity;
  (** The kinds of the parameters of the [continuation_param] continuation.
      (This encodes whether the function returns multiple and/or unboxed
      values, for example.) *)
  params : Parameter.t list;
  (** The normal (variable) parameters of the function together with their
      types.  Some of the parameters may have non-trivial types that
      indicate previous specialisation of the function.  Types of parameters
      must never regress in preciseness. *)
  (* CR mshinwell: check non-regression property with xclerc's code *)
  body : t;
  (** The code of the function's body. *)
  (* CR-soon mshinwell: inconsistent naming free_variables/free_vars here and
     above *)
  free_variables : Variable.Set.t;
  (** All variables free in the *body* of the function.  For example, a
      variable that is bound as one of the function's parameters will still
      be included in this set.  This field is present as an optimization. *)
  free_symbols : Symbol.Set.t;
  (** All symbols that occur in the function's body.  (Symbols can never be
      bound in a function's body; the only thing that binds symbols is the
      [program] constructions below.) *)
  stub : bool;
  (** A stub function is a generated function used to prepare arguments or
      return values to allow indirect calls to functions with a special calling
      convention.  For instance indirect calls to tuplified functions must go
      through a stub.  Stubs will be unconditionally inlined. *)
  dbg : Debuginfo.t;
  (** Debug info for the function declaration. *)
  inline : Lambda.inline_attribute;
  (** Inlining requirements from the source code. *)
  specialise : Lambda.specialise_attribute;
  (** Specialising requirements from the source code. *)
  is_a_functor : bool;
  (** Whether the function is known definitively to be a functor. *)
}

(** Equivalent to the similar type in [Ilambda]. *)
and switch = private {
  (* CR mshinwell: [numconsts] should move onto the default case. *)
  numconsts : Numbers.Int.Set.t;
  (** All possible values that the scrutinee might have. *)
  consts : (int * Continuation.t) list;
  (** Branches for specific values of the scrutinee. *)
  failaction : Continuation.t option;
  (** Action to take if none of the [consts] matched. *)
}

(** Like a subset of [Flambda.named], except that instead of [Variable.t]s we
    have [Symbol.t]s, and everything is a constant (i.e. with a fixed value
    known at compile time).  Values of this type describe constants that will
    be directly assigned to symbols in the object file (see below). *)
and constant_defining_value =
  | Allocated_const of Allocated_const.t
    (** A single constant.  These are never "simple constants" (type [const])
        but instead more complicated constructions. *)
  | Block of Tag.t * constant_defining_value_block_field list
    (** A pre-allocated block full of constants (either simple constants
        or references to other constants, see below). *)
  | Set_of_closures of set_of_closures
    (** A closed (and thus constant) set of closures.  (That is to say,
        [free_vars] must be empty.) *)
  | Project_closure of Symbol.t * Closure_id.t
    (** Selection of one closure from a constant set of closures.
        Analogous to the equivalent operation on expressions. *)

and constant_defining_value_block_field =
  | Symbol of Symbol.t
  | Const of const

module Constant_defining_value :
  Identifiable.S with type t = constant_defining_value

type expr = t

(** A "program" is the contents of one compilation unit.  It describes the
    various values that are assigned to symbols (and in some cases fields of
    such symbols) in the object file.  As such, it is closely related to
    the compilation of toplevel modules. *)
type program_body =
  | Let_symbol of Symbol.t * constant_defining_value * program_body
  (** Define the given symbol to have the given constant value. *)
  | Let_rec_symbol of (Symbol.t * constant_defining_value) list * program_body
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
  | Initialize_symbol of Symbol.t * Tag.t * (t * Continuation.t) list
      * program_body
  (** Define the given symbol as a constant block of the given size and
      tag; but with a possibly non-constant initializer.  The initializer
      will be executed at most once (from the entry point of the compilation
      unit). *)
  | Effect of t * Continuation.t * program_body
  (** Cause the given expression, which may have a side effect, to be
      executed.  The resulting value is discarded.  [Effect] constructions
      are never re-ordered. *)
  | End of Symbol.t
  (** [End] accepts the root symbol: the only symbol that can never be
      eliminated. *)

(* CR-someday mshinwell: consider support for [Initialize_symbol] that can
   hold unboxed numbers (e.g. floats for testsuite/tests/misc/gcwords.ml
   when the inlining annotation is removed, as it used to be). *)

type program = {
  imported_symbols : Symbol.Set.t;
  program_body : program_body;
}

(** Compute the free variables of a term.  (This is O(1) for [Let]s).
    If [ignore_uses_as_callee], all free variables inside [Apply] expressions
    are ignored.  Likewise [ignore_uses_in_project_var] for [Project_var]
    expressions.
*)
val free_variables
   : ?ignore_uses_as_callee:unit
  -> ?ignore_uses_as_argument:unit
  -> ?ignore_uses_as_continuation_argument:unit
  -> ?ignore_uses_in_project_var:unit
  -> ?ignore_uses_in_apply_cont:unit
  -> t
  -> Variable.Set.t

(** Compute the free variables of a named expression. *)
val free_variables_named
   : ?ignore_uses_in_project_var:unit
  -> named
  -> Variable.Set.t

val free_variables_of_let_cont_handlers
   : let_cont_handlers
  -> Variable.Set.t

val free_variables_of_specialised_args
   : Flambda_types0.T.specialised_args
  -> Variable.Set.t

(** Compute _all_ variables occurring inside an expression. *)
val used_variables
   : ?ignore_uses_as_callee:unit
  -> ?ignore_uses_as_argument:unit
  -> ?ignore_uses_as_continuation_argument:unit
  -> ?ignore_uses_in_project_var:unit
  -> t
  -> Variable.Set.t

(** Compute _all_ variables occurring inside a named expression. *)
val used_variables_named
   : ?ignore_uses_in_project_var:unit
  -> named
  -> Variable.Set.t

val continuation_map_of_let_handlers
   : handlers:let_cont_handlers
  -> continuation_handlers

(** [map_let_cont_handlers ~handlers ~f] is equivalent to calling [f] on
    [continuation_map_of_let_handlers ~handlers], then repacking the result
    in the same constructor (Recursive or Nonrecursive) as [handlers] *)
val map_let_cont_handlers
   : handlers:let_cont_handlers
  -> f:(continuation_handlers -> continuation_handlers)
  -> let_cont_handlers

val bound_continuations_of_let_handlers
   : handlers:let_cont_handlers
  -> Continuation.Set.t

val free_continuations_of_let_cont_handlers
   : handlers:let_cont_handlers
  -> Continuation.Set.t

(* CR mshinwell: Improve return type of this function *)
val free_continuations_of_let_cont_handlers'
   : handlers:let_cont_handlers
  -> Continuation.Set.t * Continuation.Set.t  (* free, bound *)

(* CR mshinwell: Consider if we want to cache these. *)
val free_continuations : expr -> Continuation.Set.t

val free_symbols : expr -> Symbol.Set.t

val free_symbols_named : named -> Symbol.Set.t

val free_symbols_program : program -> Symbol.Set.t

type named_reachable =
  | Reachable of named
  | Non_terminating of named
  | Unreachable

(** Used to avoid exceeding the stack limit when handling expressions with
    multiple consecutive nested [Let]-expressions.  This saves rewriting large
    simplification functions in CPS.  This function provides for the
    rewriting or elimination of expressions during the fold. *)
val fold_lets_option
   : t
  -> init:'a
  -> for_defining_expr:(
      'a
    -> Variable.t
    -> named
    -> 'a * (Variable.t * Flambda_type0.t * named) list
      * Variable.t * Flambda_type0.t * named_reachable)
  -> for_last_body:('a -> t -> t * 'b)
  (* CR-someday mshinwell: consider making [filter_defining_expr]
     optional *)
  -> filter_defining_expr:('b -> Variable.t -> named -> Variable.Set.t ->
                           'b * Variable.t * named option)
  -> t * 'b

(** Like [fold_lets_option], but just a map. *)
(* CR mshinwell: consider enhancing this in the same way as for
   [fold_lets_option] in the [defining_expr] type.  This would be useful eg
   for Ref_to_variables.  Maybe in fact there should be a new iterator that
   uses this function for such situations? *)
val map_lets
   : t
  -> for_defining_expr:(Variable.t -> named -> named)
  -> for_last_body:(t -> t)
  -> after_rebuild:(t -> t)
  -> t

(** Like [map_lets], but just an iterator. *)
val iter_lets
   : t
  -> for_defining_expr:(Variable.t -> named -> unit)
  -> for_last_body:(t -> unit)
  -> for_each_let:(t -> unit)
  -> unit

(** Creates a [Let] expression.  (This computes the free variables of the
    defining expression and the body.) *)
val create_let : Variable.t -> named -> t -> t

(** Apply the specified function [f] to the defining expression of the given
    [Let]-expression, returning a new [Let]. *)
val map_defining_expr_of_let : let_expr -> f:(named -> named) -> t

(** A module for the manipulation of terms where the recomputation of free
    variable sets is to be kept to a minimum. *)
module With_free_variables : sig
  type 'a t

  val print : Format.formatter -> _ t -> unit

  (** O(1) time. *)
  val of_defining_expr_of_let : let_expr -> named t

  (** O(1) time. *)
  val of_body_of_let : let_expr -> expr t

  (** Takes the time required to calculate the free variables of the given
      term (proportional to the size of the term, except that the calculation
      for [Let] is O(1)). *)
  val of_expr : expr -> expr t

  val of_named : named -> named t

  (** This function shouldn't be used to build a let from the [named t];
      use the [create_let_...] functions below.  It is intended to be used
      for situations such as when you want to use the contents of a [named t]
      for [Effect_analysis]. *)
  val to_named : named t -> named

  (** Takes the time required to calculate the free variables of the given
      [expr]. *)
  val create_let_reusing_defining_expr
     : Variable.t
    -> named t
    -> expr
    -> expr

  (** Takes the time required to calculate the free variables of the given
      [named].  The specified Flambda type must be fully resolved (i.e. no
      occurrences of [Load_lazily]) or a fatal error will result. *)
  val create_let_reusing_body
     : Variable.t
    -> Flambda_type0.t
    -> named
    -> expr t
    -> expr

  (** O(1) time. *)
  val create_let_reusing_both
     : Variable.t
    -> named t
    -> expr t
    -> expr

  val contents : 'a t -> 'a

  (** O(1) time. *)
  val free_variables : _ t -> Variable.Set.t
end

(** Create a suitable [expr] to represent the given switch.  (The result may
    not actually be a [Switch].) *)
val create_switch
   : scrutinee:Variable.t
  -> all_possible_values:Numbers.Int.Set.t
  -> arms:(int * Continuation.t) list
  -> default:Continuation.t option
  -> expr

(** As for [create_switch], but also returns a map showing the continuations
    that occur within the returned expression, and how many uses of each there
    are therein. *)
val create_switch'
   : scrutinee:Variable.t
  -> all_possible_values:Numbers.Int.Set.t
  -> arms:(int * Continuation.t) list
  -> default:Continuation.t option
  -> expr * (int Continuation.Map.t)

(** Create a function declaration.  This calculates the free variables and
    symbols occurring in the specified [body].

    To just change the parameters or body of a function the "update" functions
    below should be used, if possible; otherwise care must be taken to
    preserve the [closure_origin].

    When adding a stub to a function the stub should receive a new
    [closure_origin] and the renamed original function should retain its
    existing [closure_origin].
*)
val create_function_declaration
   : params:Parameter.t list
  -> continuation_param:Continuation.t
  -> return_arity:int
  -> body:t
  -> stub:bool
  -> dbg:Debuginfo.t
  -> inline:Lambda.inline_attribute
  -> specialise:Lambda.specialise_attribute
  -> is_a_functor:bool
  (* CR mshinwell for pchambart: check Closure_origin stuff *)
  -> closure_origin:Closure_origin.t
  -> function_declaration

(** Create a set of function declarations given the individual declarations. *)
val create_function_declarations
   : funs:function_declaration Variable.Map.t
  -> function_declarations

(** Change only the code of a function declaration. *)
val update_body_of_function_declaration
   : function_declaration
  -> body:expr
  -> function_declaration

(** Change only the code and parameters of a function declaration. *)
(* CR-soon mshinwell: rename this to match new update function above *)
val update_function_decl's_params_and_body
   : function_declaration
  -> params:Parameter.t list
  -> body:expr
  -> function_declaration

(** Create a set of function declarations based on another set of function
    declarations. *)
val update_function_declarations
   : function_declarations
  -> funs:function_declaration Variable.Map.t
  -> function_declarations

val import_function_declarations_for_pack
   : function_declarations
  -> (Set_of_closures_id.t -> Set_of_closures_id.t)
  -> (Set_of_closures_origin.t -> Set_of_closures_origin.t)
  -> function_declarations

(** Create a set of closures.  Checks are made to ensure that [free_vars]
    and [specialised_args] are reasonable. *)
val create_set_of_closures
   : function_decls:function_declarations
  -> free_vars:free_vars
  -> specialised_args:Flambda_types0.T.specialised_args
  -> direct_call_surrogates:Variable.t Variable.Map.t
  -> set_of_closures

(** Given a function declaration, find which of its parameters (if any)
    are used in the body. *)
val used_params : function_declaration -> Variable.Set.t

type maybe_named =
  | Is_expr of t
  | Is_named of named

(** This function is designed for the internal use of [Flambda_iterators].
    See that module for iterators to be used over Flambda terms. *)
val iter_general
   : toplevel:bool
  -> (t -> unit)
  -> (named -> unit)
  -> maybe_named
  -> unit

val print : Format.formatter -> t -> unit

val print_named : Format.formatter -> named -> unit

val print_program : Format.formatter -> program -> unit

val print_const : Format.formatter -> const -> unit

val print_constant_defining_value
   : Format.formatter
  -> constant_defining_value
  -> unit

val print_function_declaration
   : Format.formatter
  -> Variable.t * function_declaration
  -> unit

val print_function_declarations
   : Format.formatter
  -> function_declarations
  -> unit

val print_project_closure
   : Format.formatter
  -> project_closure
  -> unit

val print_move_within_set_of_closures
   : Format.formatter
  -> move_within_set_of_closures
  -> unit

val print_project_var
   : Format.formatter
  -> project_var
  -> unit

val print_set_of_closures
   : Format.formatter
  -> set_of_closures
  -> unit

val print_specialised_args
   : Format.formatter
  -> Flambda_types0.T.specialised_args
  -> unit

val print_specialised_to
   : Format.formatter
  -> specialised_to
  -> unit

val print_let_cont_handlers
   : Format.formatter
  -> let_cont_handlers
  -> unit

val compare_free_var
   : free_var
  -> free_var
  -> int

val equal_free_var
   : free_var
  -> free_var
  -> bool

val compare_specialised_to
   : specialised_to
  -> specialised_to
  -> int

val equal_specialised_to
   : specialised_to
  -> specialised_to
  -> bool

val compare_project_var : project_var -> project_var -> int

val compare_move_within_set_of_closures
   : move_within_set_of_closures
  -> move_within_set_of_closures
  -> int

val compare_project_closure : project_closure -> project_closure -> int

val compare_const : const -> const -> int
