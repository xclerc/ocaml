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

type apply_kind = Flambda0.apply_kind
type apply = Flambda0.apply
type assign = Flambda0.assign

module Call_kind : module type of Flambda0.Call_kind
module Const : module type of Flambda0.Const
module Continuation_handler : module type of Flambda0.Continuation_handler
module Continuation_handlers : module type of Flambda0.Continuation_handlers
module Free_var : module type of Flambda0.Free_var
module Let : module type of Flambda0.Let
module Let_cont : module type of Flambda0.Let_cont
module Let_cont_handlers : module type of Flambda0.Let_cont_handlers
module Let_mutable : module type of Flambda0.Let_mutable
module Return_arity : module type of Flambda0.Return_arity
module Switch : module type of Flambda0.Switch
module Trap_action : module type of Flambda0.Trap_action
module Typed_parameter : module type of Flambda0.Typed_parameter
module With_free_variables : module type of Flambda0.With_free_variables

module Free_vars : sig
  include module type of Flambda0.Free_vars

  (* Ensure that projection information is suitably erased if we have deleted
     the variable being projected from. *)
  val clean_projections : t -> t
end

module Reachable : sig
  type nonrec t =
    | Reachable of Flambda0.Named.t
    | Non_terminating of Flambda0.Named.t
    | Unreachable
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
    -> params:Typed_parameter.t list
    -> continuation_param:Continuation.t
    (* CR mshinwell: update comment. *)
    -> stub:bool
    -> continuation:Continuation.t
    -> return_arity:Flambda0.Return_arity.t
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
     : bindings:(Variable.t * Flambda_kind.t * Named.t) list
    -> body:t
    -> t

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

  (* CR-soon mshinwell: we need to document whether these iterators follow any
    particular order. *)
  module Iterators : sig
    val iter : (t -> unit) -> (Named.t -> unit) -> t -> unit

    val iter_lets
       : t
      -> for_defining_expr:(Variable.t -> Flambda_kind.t -> Named.t -> unit)
      -> for_last_body:(t -> unit)
      -> for_each_let:(t -> unit)
      -> unit

    (** Apply the given functions to the immediate subexpressions of the given
        Flambda expression. *)
    val iter_subexpressions
       : (t -> unit)
      -> (Named.t -> unit)
      -> t
      -> unit
        
    val iter_expr : (t -> unit) -> t -> unit

    val iter_named : (Named.t -> unit) -> t -> unit
    
    val iter_all_immutable_let_and_let_rec_bindings
       : t
      -> f:(Variable.t -> Named.t -> unit)
      -> unit

    val iter_sets_of_closures : (Set_of_closures.t -> unit) -> t -> unit

    (** Iterators, mappers and folders in [Toplevel_only] modules never
        recurse into the bodies of functions. *) 
    module Toplevel_only : sig 
      val iter
        : (t -> unit)
       -> (Named.t -> unit)
       -> t
       -> unit

      val iter_all_immutable_let_and_let_rec_bindings
         : t
        -> f:(Variable.t -> Named.t -> unit)
        -> unit
    end
  end
    
  module Mappers : sig
    val map : (t -> t) -> (Named.t -> Named.t) -> t -> t

    val map_lets
       : t
      -> for_defining_expr:(Variable.t -> Flambda_kind.t -> Named.t -> Named.t)
      -> for_last_body:(t -> t)
      -> after_rebuild:(t -> t)
      -> t

    val map_subexpressions
       : (t -> t)
      -> (Variable.t -> Named.t -> Named.t)
      -> t
      -> t

    val map_expr : (t -> t) -> t -> t

    val map_symbols : t -> f:(Symbol.t -> Symbol.t) -> t

    val map_sets_of_closures
       : t
      -> f:(Set_of_closures.t -> Set_of_closures.t)
      -> t
  
    val map_apply : t -> f:(apply -> apply) -> t

    val map_project_var_to_named_opt
       : t
      -> f:(Projection.Project_var.t -> Named.t option)
      -> t

    val map_all_immutable_let_and_let_rec_bindings
       : t
      -> f:(Variable.t -> Named.t -> Named.t)
      -> t
         
    module Toplevel_only : sig 
      val map : (t -> t) -> (Named.t -> Named.t) -> t -> t

      val map_expr : (t -> t) -> t -> t
  
      val map_sets_of_closures
         : t
        -> f:(Set_of_closures.t -> Set_of_closures.t)
        -> t
    end
  end

  module Folders : sig
    (** Used to avoid exceeding the stack limit when handling expressions with
        multiple consecutive nested [Let]-expressions. This saves rewriting
        large simplification functions in CPS. This function provides for the
        rewriting or elimination of expressions during the fold. *)
    val fold_lets_option
        : t
      -> init:'a
      -> for_defining_expr:(
          'a
        -> Variable.t
        -> Flambda_kind.t
        -> Named.t
        -> 'a
          * (Variable.t * Flambda_kind.t * Named.t) list
          * Variable.t
          * Flambda_kind.t
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
  end
end and Named : sig
  include module type of Flambda0.Named

  val toplevel_substitution
     : Variable.t Variable.Map.t
    -> t
    -> t

  val of_projection : Projection.t -> Debuginfo.t -> t

  module Iterators : sig
    val iter : (Expr.t -> unit) -> (t -> unit) -> t -> unit
    
    val iter_named : (t -> unit) -> t -> unit

    module Toplevel_only : sig
      val iter : (Expr.t -> unit) -> (t -> unit) -> t -> unit
    end
  end
end
and Set_of_closures : sig
  include module type of Flambda0.Set_of_closures

  (** [find_free_variable v clos] raises [Not_found] if [c] is not in [clos]. *)
  val find_free_variable
     : Var_within_closure.t
    -> t
    -> Variable.t

  module Mappers : sig
    val map_symbols
       : t
      -> f:(Symbol.t -> Symbol.t)
      -> t

    val map_function_bodies
       : ?ignore_stubs:unit
      -> t
      -> f:(Expr.t -> Expr.t)
      -> t
  end

  module Folders : sig
    val fold_function_decls_ignoring_stubs
       : t
      -> init:'a
      -> f:(fun_var:Variable.t
        -> function_decl:Function_declaration.t
        -> 'a
        -> 'a)
      -> 'a
  end
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
