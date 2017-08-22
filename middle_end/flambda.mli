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

(** Operations on Flambda terms whose implementations cannot break invariants
    enforced by the private types. *)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module Return_arity = Flambda.Return_arity

module Call_kind : sig
  include module type of Flambda.Call_kind

  val arity_of_call_kind : t -> Flambda.Return_arity.t
end

module Const = Flambda.Const

module Return_arity = Flambda.Return_arity

module Free_vars : sig
  include module type of Flambda.Free_vars

  (* Ensure that projection information is suitably erased from
    free_vars and specialised_args if we have deleted the variable being
    projected from. *)
  val clean_free_vars_projections : t -> t
end

module Expr : sig
  include module type of Flambda.Expr

  (** Structural equality (not alpha equivalence). *)
  val equal : t -> t -> bool

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
    -> body:t
    -> params:Parameter.t list
    -> continuation_param:Continuation.t
    (* CR mshinwell: update comment. *)
    -> stub:bool
    -> continuation:Continuation.t
    -> t

  val toplevel_substitution
     : Variable.t Variable.Map.t
    -> t
    -> t

  (* CR-someday pchambart: A more general version of this function might
    take a [named] instead of a symbol and be called with
    [Read_symbol_field (symbol, 0)]. *)
  val substitute_read_symbol_field_for_variables
     : (Symbol.t * int option) Variable.Map.t
    -> t
    -> t

  (** If [can_be_merged f1 f2] is [true], it is safe to merge switch
      branches containing [f1] and [f2]. *)
  val can_be_merged : t -> t -> bool

  val description_of_toplevel_node : t -> string

  (** [bind [var1, expr1; ...; varN, exprN] body] binds using
      [Immutable] [Let] expressions the given [(var, expr)] pairs around the
      body. *)
  val bind
     : bindings:(Variable.t * Flambda.Named.t) list
    -> body:t
    -> t

  module Reachable : sig
    type nonrec t =
      | Reachable of Flambda.Named.t
      | Non_terminating of Flambda.Named.t
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
      -> Flambda.Named.t
      -> 'a
        * (Variable.t * Flambda.Function_declarations.t Flambda_type0.T.t
            * Flambda.Named.t) list
        * Variable.t
        * Flambda.Function_declarations.t Flambda_type0.T.t
        * Reachable.t)
    -> for_last_body:('a -> Flambda.t -> Flambda.t * 'b)
    (* CR-someday mshinwell: consider making [filter_defining_expr]
       optional *)
    -> filter_defining_expr:(
        'b
      -> Variable.t
      -> Flambda.Named.t
      -> Variable.Set.t
      -> 'b * Variable.t * (Flambda.Named.t option))
    -> t * 'b

  (* CR mshinwell: consider enhancing this in the same way as for
     [fold_lets_option] in the [defining_expr] type.  This would be useful eg
     for Ref_to_variables.  Maybe in fact there should be a new iterator that
     uses this function for such situations? *)
  val map_lets
     : Flambda.Expr.t
    -> for_defining_expr:(Variable.t -> Flambda.Named.t -> Flambda.Named.t)
    -> after_rebuild:(Flambda.Expr.t -> Flambda.Expr.t)
    -> for_last_body:(Flambda.Expr.t -> Flambda.Expr.t)
    -> Flambda.Expr.t

  (** All continuations defined at toplevel within the given expression. *)
  val all_defined_continuations_toplevel : t -> Continuation.Set.t

  val count_continuation_uses_toplevel : t -> int Continuation.Map.t

  type with_wrapper =
    | Unchanged of { handler : Flambda.Continuation_handler.t; }
    | With_wrapper of {
        new_cont : Continuation.t;
        new_handler : Flambda.Continuation_handler.t;
        wrapper_handler : Flambda.Continuation_handler.t;
      }

  val build_let_cont_with_wrappers
     : body:t
    -> recursive:Asttypes.rec_flag
    -> with_wrappers:with_wrapper Continuation.Map.t
    -> t
end

module Named : sig
  include module type of Flambda.Named

  val toplevel_substitution
     : Variable.t Variable.Map.t
    -> t
    -> t

  val of_projection : Projection.t -> t
end

module Let = Flambda.Let

module Let_mutable = Flambda.Let_mutable

module Let_cont = Flambda.Let_cont

module Continuation_handler = Flambda.Continuation_handler

module Continuation_handlers = Flambda.Continuation_handlers

module Set_of_closures : sig
  (** [find_free_variable v clos] raises [Not_found] if [c] is not in [clos]. *)
  val find_free_variable
     : Var_within_closure.t
    -> t
    -> Variable.t
end

module Function_declarations : sig
  include module type of Flambda.Function_declarations

  (** [find_declaration f decl] raises [Not_found] if [f] is not in [decl]. *)
  val find_declaration
     : Closure_id.t
    -> t
    -> Flambda.Function_declaration.t

  (** [find_declaration_variable f decl] raises [Not_found] if [f] is not in
      [decl]. *)
  val find_declaration_variable
     : Closure_id.t
    -> t
    -> Variable.t

  (** Variables "bound by a closure" are those variables free in the
      corresponding function's body that are neither:
      - bound as parameters of that function; nor
      - bound by the [let] binding that introduces the function declaration(s).
      In particular, if [f], [g] and [h] are being introduced by a
      simultaneous, possibly mutually-recursive [let] binding then none of
      [f], [g] or [h] are bound in any of the closures for [f], [g] and [h].
  *)
  val variables_bound_by_the_closure
     : Closure_id.t
    -> t
    -> Variable.Set.t

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
     : t
    -> backend:(module Backend_intf.S)
    -> Variable.Set.t Variable.Map.t

  (** Computes the set of closure_id in the set of closures that are
      required used (transitively) the entry_point *)
  val closures_required_by_entry_point
     : entry_point:Closure_id.t
    -> backend:(module Backend_intf.S)
    -> t
    -> Variable.Set.t

  val all_functions_parameters : t -> Variable.Set.t

  val all_free_symbols : t -> Symbol.Set.t

  val contains_stub : t -> bool
end

module Function_declaration : sig
  include module type of Flambda.Function_declaration

  val function_arity : t -> int
end

module Typed_parameter = Flambda.Typed_parameter
