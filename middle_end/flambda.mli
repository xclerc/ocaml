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

module Return_arity : module type of Flambda0.Return_arity
module Call_kind : module type of Flambda0.Call_kind
module Const : module type of Flambda0.Const
type apply_kind = Flambda0.apply_kind
type apply = Flambda0.apply
type assign = Flambda0.assign
module Free_var = Flambda0.Free_var

module Free_vars : sig
  include module type of Flambda0.Free_vars

  (* Ensure that projection information is suitably erased from
    free_vars and specialised_args if we have deleted the variable being
    projected from. *)
  val clean_free_vars_projections : t -> t
end

module rec Expr : sig
  include module type of Flambda0.Expr

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

  val description_of_toplevel_node : t -> string

  (** [bind [var1, expr1; ...; varN, exprN] body] binds using
      [Immutable] [Let] expressions the given [(var, expr)] pairs around the
      body. *)
  val bind
     : bindings:(Variable.t * Named.t) list
    -> body:t
    -> t

  module Reachable : sig
    type nonrec t =
      | Reachable of Named.t
      | Non_terminating of Named.t
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
        * (Variable.t * Flambda_type.t
            * Named.t) list
        * Variable.t
        * Flambda_type.t
        * Reachable.t)
    -> for_last_body:('a -> t -> t * 'b)
    (* CR-someday mshinwell: consider making [filter_defining_expr]
       optional *)
    -> filter_defining_expr:(
        'b
      -> Variable.t
      -> Named.t
      -> Variable.Set.t
      -> 'b * Variable.t * (Named.t option))
    -> t * 'b

  (* CR mshinwell: consider enhancing this in the same way as for
     [fold_lets_option] in the [defining_expr] type.  This would be useful eg
     for Ref_to_variables.  Maybe in fact there should be a new iterator that
     uses this function for such situations? *)
  val map_lets
     : Expr.t
    -> for_defining_expr:(Variable.t -> Named.t -> Named.t)
    -> after_rebuild:(Expr.t -> Expr.t)
    -> for_last_body:(Expr.t -> Expr.t)
    -> Expr.t

  (** All continuations defined at toplevel within the given expression. *)
  val all_defined_continuations_toplevel : t -> Continuation.Set.t

  val count_continuation_uses_toplevel : t -> int Continuation.Map.t

  type with_wrapper =
    | Unchanged of { handler : Continuation_handler.t; }
    | With_wrapper of {
        new_cont : Continuation.t;
        new_handler : Continuation_handler.t;
        wrapper_handler : Continuation_handler.t;
      }

  val build_let_cont_with_wrappers
     : body:t
    -> recursive:Asttypes.rec_flag
    -> with_wrappers:with_wrapper Continuation.Map.t
    -> t
end and Named : sig
  include module type of Flambda0.Named

  val toplevel_substitution
     : Variable.t Variable.Map.t
    -> t
    -> t

  val of_projection : Projection.t -> t
end
and Let : module type of Flambda0.Let
and Let_mutable : module type of Flambda0.Let_mutable
and Let_cont : module type of Flambda0.Let_cont
and Let_cont_handlers : module type of Flambda0.Let_cont_handlers
and Continuation_handler : module type of Flambda0.Continuation_handler
and Continuation_handlers : module type of Flambda0.Continuation_handlers
and Set_of_closures : sig
  include module type of Flambda0.Set_of_closures

  (** [find_free_variable v clos] raises [Not_found] if [c] is not in [clos]. *)
  val find_free_variable
     : Var_within_closure.t
    -> t
    -> Variable.t
end and Function_declarations : sig
  include module type of Flambda0.Function_declarations

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
      used (transitively) by the [entry_point]. *)
  (* CR mshinwell: except it returns a set of variables... *)
  val closures_required_by_entry_point
     : entry_point:Closure_id.t
    -> backend:(module Backend_intf.S)
    -> t
    -> Variable.Set.t

  val all_functions_parameters : t -> Variable.Set.t

  val all_free_symbols : t -> Symbol.Set.t

  val contains_stub : t -> bool
end and Function_declaration : sig
  include module type of Flambda0.Function_declaration

  val function_arity : t -> int

  (** The number of variables in the function's closure.  Such variables are
      taken to be the free variables of the function's body but ignoring
      variables that are either function parameters or the name of one of
      the other functions simultaneously-defined with [t]. *)
  val num_variables_in_closure
     : t
    -> function_decls:Function_declarations.t
    -> int

  (** Structural equality (not alpha equivalence). *)
  val equal : t -> t -> bool
end

module Typed_parameter : module type of Flambda0.Typed_parameter
