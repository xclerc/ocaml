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

(** Utility functions for the Flambda intermediate language. *)

(** Access functions *)

(** [find_declaration f decl] raises [Not_found] if [f] is not in [decl]. *)
val find_declaration :
  Closure_id.t -> Flambda.Function_declarations.t -> Flambda.Function_declaration.t

(** [find_declaration_variable f decl] raises [Not_found] if [f] is not in
    [decl]. *)
val find_declaration_variable :
  Closure_id.t -> Flambda.Function_declarations.t -> Variable.t

(** [find_free_variable v clos] raises [Not_found] if [c] is not in [clos]. *)
val find_free_variable :
  Var_within_closure.t -> Flambda.set_of_closures -> Variable.t

(** Utility functions *)

val function_arity : Flambda.Function_declaration.t -> int

(** Variables "bound by a closure" are those variables free in the
    corresponding function's body that are neither:
    - bound as parameters of that function; nor
    - bound by the [let] binding that introduces the function declaration(s).
    In particular, if [f], [g] and [h] are being introduced by a
    simultaneous, possibly mutually-recursive [let] binding then none of
    [f], [g] or [h] are bound in any of the closures for [f], [g] and [h].
*)
val variables_bound_by_the_closure :
  Closure_id.t -> Flambda.Function_declarations.t -> Variable.Set.t

(** If [can_be_merged f1 f2] is [true], it is safe to merge switch
    branches containing [f1] and [f2]. *)
val can_be_merged : Flambda.t -> Flambda.t -> bool

val description_of_toplevel_node : Flambda.t -> string

(* Given an expression, freshen all variables within it, and form a function
   whose body is the resulting expression.  The variables specified by
   [params] will become the parameters of the function; the closure will be
   identified by [id].  [params] must only reference variables that are
   free variables of [body]. *)
(* CR-soon mshinwell: consider improving name and names of arguments
   lwhite: the params restriction seems odd, perhaps give a reason
   in the comment. *)
val make_closure_declaration
   : id:Variable.t
  -> body:Flambda.t
  -> params:Parameter.t list
  -> continuation_param:Continuation.t
  (* CR mshinwell: update comment. *)
  -> stub:bool
  -> continuation:Continuation.t
  -> Flambda.t

val toplevel_substitution
   : Variable.t Variable.Map.t
  -> Flambda.expr
  -> Flambda.expr

val toplevel_substitution_named
   : Variable.t Variable.Map.t
  -> Flambda.named
  -> Flambda.named

(** [bind [var1, expr1; ...; varN, exprN] body] binds using
    [Immutable] [Let] expressions the given [(var, expr)] pairs around the
    body. *)
val bind
   : bindings:(Variable.t * Flambda.named) list
  -> body:Flambda.t
  -> Flambda.t

val compare_const : Flambda.const -> Flambda.const -> int

val initialize_symbols
   : Flambda.program
  -> (Symbol.t * Tag.t * (Flambda.t * Continuation.t) list) list

val imported_symbols : Flambda.program -> Symbol.Set.t

val needed_import_symbols : Flambda.program -> Symbol.Set.t

val introduce_needed_import_symbols : Flambda.program -> Flambda.program

val root_symbol : Flambda.program -> Symbol.t

(** Creates a map from closure IDs to function declarations by iterating over
    all sets of closures in the given program. *)
val make_closure_map
   : Flambda.program
  -> Flambda.Function_declarations.t Closure_id.Map.t

(** Like [make_closure_map], but takes a mapping from set of closures IDs to
    function declarations, instead of a [program]. *)
val make_closure_map'
   : Flambda.Function_declarations.t Set_of_closures_id.Map.t
  -> Flambda.Function_declarations.t Closure_id.Map.t

(** The definitions of all constants that have been lifted out to [Let_symbol]
    or [Let_rec_symbol] constructions. *)
val all_lifted_constants
   : Flambda.program
  -> (Symbol.t * Flambda.constant_defining_value) list

(** Like [all_lifted_constant_symbols], but returns a map instead of a list. *)
val all_lifted_constants_as_map
   : Flambda.program
  -> Flambda.constant_defining_value Symbol.Map.t

(** The identifiers of all constant sets of closures that have been lifted out
    to [Let_symbol] or [Let_rec_symbol] constructions. *)
val all_lifted_constant_sets_of_closures
   : Flambda.program
  -> Set_of_closures_id.Set.t

(** All sets of closures in the given program (whether or not bound to a
    symbol.) *)
val all_sets_of_closures : Flambda.program -> Flambda.set_of_closures list

val all_sets_of_closures_map
   : Flambda.program
  -> Flambda.set_of_closures Set_of_closures_id.Map.t

val all_function_decls_indexed_by_set_of_closures_id
   : Flambda.program
  -> Flambda.Function_declarations.t Set_of_closures_id.Map.t

val all_function_decls_indexed_by_closure_id
   : Flambda.program
  -> Flambda.Function_declarations.t Closure_id.Map.t

val make_variable_symbol : Variable.t -> Symbol.t
val make_variables_symbol : Variable.t list -> Symbol.t

(* CR-someday pchambart: A more general version of this function might
   take a [named] instead of a symbol and be called with
   [Read_symbol_field (symbol, 0)]. *)
val substitute_read_symbol_field_for_variables
   : (Symbol.t * int option) Variable.Map.t
  -> Flambda.t
  -> Flambda.t

(** For the compilation of switch statements. *)
module Switch_storer : sig
  val mk_store : unit -> Continuation.t Switch.t_store
end

(** Within a set of function declarations there is a set of function bodies,
    each of which may (or may not) reference one of the other functions in
    the same set.  Initially such intra-set references are by [Var]s (known
    as "fun_var"s) but if the function is lifted by [Lift_constants] then the
    references will be translated to [Symbol]s.  This means that optimization
    passes that need to identify whether a given "fun_var" (i.e. a key in the
    [funs] map in a value of type [function_declarations]) is used in one of
    the function bodies need to examine the [free_symbols] as well as the
    [free_variables] members of [function_declarations].  This function makes
    that process easier by computing all used "fun_var"s in the bodies of
    the given set of function declarations, including the cases where the
    references are [Symbol]s.  The returned value is a map from "fun_var"s
    to the "fun_var"s (if any) used in the body of the function associated
    with that "fun_var".
*)
val fun_vars_referenced_in_decls
   : Flambda.Function_declarations.t
  -> backend:(module Backend_intf.S)
  -> Variable.Set.t Variable.Map.t

(** Computes the set of closure_id in the set of closures that are
    required used (transitively) the entry_point *)
val closures_required_by_entry_point
   : entry_point:Closure_id.t
  -> backend:(module Backend_intf.S)
  -> Flambda.Function_declarations.t
  -> Variable.Set.t

val all_functions_parameters : Flambda.Function_declarations.t -> Variable.Set.t

val all_free_symbols : Flambda.Function_declarations.t -> Symbol.Set.t

val contains_stub : Flambda.Function_declarations.t -> bool

(* Ensure that projection information is suitably erased from
   free_vars and specialised_args if we have deleted the variable being
   projected from. *)
val clean_free_vars_projections : Flambda.free_vars -> Flambda.free_vars
val clean_specialised_args_projections
   : Flambda.specialised_args
  -> Flambda.specialised_args

val projection_to_named : Projection.t -> Flambda.named

type specialised_to_same_as =
  | Not_specialised
  | Specialised_and_aliased_to of Variable.Set.t

(** For each parameter in a given set of function declarations and the usual
    specialised-args mapping, determine which other parameters are specialised
    to the same variable as that parameter.
    The result is presented as a map from [fun_vars] to lists, corresponding
    componentwise to the usual [params] list in the corresponding function
    declaration. *)
val parameters_specialised_to_the_same_variable
   : function_decls:Flambda.Function_declarations.t
  -> specialised_args:Flambda.specialised_to Variable.Map.t
  -> specialised_to_same_as list Variable.Map.t

type with_wrapper =
  | Unchanged of { handler : Flambda.continuation_handler; }
  | With_wrapper of {
      new_cont : Continuation.t;
      new_handler : Flambda.continuation_handler;
      wrapper_handler : Flambda.continuation_handler;
    }

val build_let_cont_with_wrappers
   : body:Flambda.t
  -> recursive:Asttypes.rec_flag
  -> with_wrappers:with_wrapper Continuation.Map.t
  -> Flambda.expr

val create_wrapper_params
   : params:Parameter.t list
  -> specialised_args:Flambda.specialised_args
  -> freshening_already_assigned:Parameter.t Parameter.Map.t
  -> Parameter.t Parameter.Map.t * Parameter.t list * Flambda.specialised_args

(** All continuations defined at toplevel within the given expression. *)
val all_defined_continuations_toplevel : Flambda.expr -> Continuation.Set.t

val count_continuation_uses_toplevel
   : Flambda.expr
  -> int Continuation.Map.t

val make_let_cont_alias
   : name:Continuation.t
  -> alias_of:Continuation.t
  -> arity:int
  -> Flambda.let_cont_handlers

val arity_of_call_kind : call_kind -> return_arity

module Reachable : sig
  type nonrec t =
    | Reachable of t
    | Non_terminating of t
    | Unreachable
end

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
    -> Named.t
    -> 'a
      * (Variable.t * Function_declarations.t Flambda_type0.T.t * Named.t) list
      * Variable.t
      * Function_declarations.t Flambda_type0.T.t
      * Named.Reachable.t)
  -> for_last_body:('a -> t -> t * 'b)
  (* CR-someday mshinwell: consider making [filter_defining_expr]
    optional *)
  -> filter_defining_expr:('b -> Variable.t -> Named.t -> Variable.Set.t ->
                          'b * Variable.t * Named.t option)
  -> t * 'b

(* CR mshinwell: consider enhancing this in the same way as for
  [fold_lets_option] in the [defining_expr] type.  This would be useful eg
  for Ref_to_variables.  Maybe in fact there should be a new iterator that
  uses this function for such situations? *)
val map_lets
  : t
  -> for_defining_expr:(Variable.t -> Named.t -> Named.t)
  -> for_last_body:(t -> t)
  -> after_rebuild:(t -> t)
  -> t
