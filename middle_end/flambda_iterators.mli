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

(* CR-soon mshinwell: we need to document whether these iterators follow any
   particular order. *)

(* CR mshinwell: We could now just move these into flambda.ml. *)

(** Apply the given functions to the immediate subexpressions of the given
    Flambda expression.  For avoidance of doubt, if a subexpression is
    [Expr], it is passed to the function taking [Flambda0.Named.t], rather
    than being followed and passed to the function taking [Flambda0.Expr.t]. *)
val apply_on_subexpressions
   : (Flambda0.Expr.t -> unit)
  -> (Flambda0.Named.t -> unit)
  -> Flambda0.Expr.t
  -> unit

val map_subexpressions
   : (Flambda0.Expr.t -> Flambda0.Expr.t)
  -> (Variable.t -> Flambda0.Named.t -> Flambda0.Named.t)
  -> Flambda0.Expr.t
  -> Flambda0.Expr.t

(* CR-soon lwhite: add comment to clarify that these recurse unlike the
   ones above *)
val iter
   : (Flambda0.Expr.t -> unit)
  -> (Flambda0.Named.t -> unit)
  -> Flambda0.Expr.t
  -> unit

val iter_expr
   : (Flambda0.Expr.t -> unit)
  -> Flambda0.Expr.t
  -> unit

val iter_on_named
   : (Flambda0.Expr.t -> unit)
  -> (Flambda0.Named.t -> unit)
  -> Flambda0.Named.t
  -> unit

(* CR-someday mshinwell: we might need to add the corresponding variable to
   the parameters of the user function for [iter_named] *)
val iter_named
   : (Flambda0.Named.t -> unit)
  -> Flambda0.Expr.t
  -> unit

(* CR-someday lwhite: These names are pretty indecipherable, perhaps
   create submodules for the normal and "on_named" variants of each
   function. *)

val iter_named_on_named
   : (Flambda0.Named.t -> unit)
  -> Flambda0.Named.t
  -> unit

(** [iter_toplevel f t] applies [f] on every toplevel subexpression of [t].
    In particular, it never applies [f] to the body of a function (which
    will always be contained within an [Set_of_closures] expression). *)
val iter_toplevel
   : (Flambda0.Expr.t -> unit)
  -> (Flambda0.Named.t -> unit)
  -> Flambda0.Expr.t
  -> unit

val iter_named_toplevel
   : (Flambda0.Expr.t -> unit)
  -> (Flambda0.Named.t -> unit)
  -> Flambda0.Named.t
  -> unit

val iter_on_sets_of_closures
   : (Flambda0.Set_of_closures.t -> unit)
  -> Flambda0.Expr.t
  -> unit

val iter_on_set_of_closures_of_program
   : Flambda_static0.Program.t
  -> f:(constant:bool -> Flambda0.Set_of_closures.t -> unit)
  -> unit

val iter_all_immutable_let_and_let_rec_bindings
   : Flambda0.Expr.t
  -> f:(Variable.t -> Flambda0.Named.t -> unit)
  -> unit

val iter_all_toplevel_immutable_let_and_let_rec_bindings
   : Flambda0.Expr.t
  -> f:(Variable.t -> Flambda0.Named.t -> unit)
  -> unit

(** Iterate over all expressions occurring directly at the toplevel of the
    program.  Note that the only function bodies iterated over are those
    bound to a symbol.  (That is to say, a function body in a set of closures
    [constant_defining_value] will be iterated over---but any subfunctions in
    the body will not be.  Likewise any function body defined by a normal
    [Let] will not be iterated over.)  If you want to iterate over those
    things as well, use [iter_exprs_at_toplevels_in_program]. *)
val iter_exprs_at_toplevel_of_program
   : Flambda_static0.Program.t
  -> f:(continuation_arity:Flambda0.Return_arity.t
    -> Continuation.t
    -> Flambda0.Expr.t
    -> unit)
  -> unit

(** Iterate over all toplevel expressions in the program:
    - bodies of functions, whether bound to symbols or not, including any
      subfunctions; and
    - [Effect] expressions. *)
val iter_exprs_at_toplevels_in_program
   : Flambda_static0.Program.t
  -> f:(continuation_arity:Flambda0.Return_arity.t
    -> Continuation.t
    -> Flambda0.Expr.t
    -> unit)
  -> unit

val iter_named_of_program
   : Flambda_static0.Program.t
  -> f:(Flambda0.Named.t -> unit)
  -> unit

val iter_constant_defining_values_on_program
  : Flambda_static0.Program.t
  -> f:(Flambda_static0.Constant_defining_value.t -> unit)
  -> unit

val iter_apply_on_program
   : Flambda_static0.Program.t
  -> f:(Flambda0.apply -> unit)
  -> unit

val map
   : (Flambda0.Expr.t -> Flambda0.Expr.t)
  -> (Flambda0.Named.t -> Flambda0.Named.t)
  -> Flambda0.Expr.t
  -> Flambda0.Expr.t

val map_expr
   : (Flambda0.Expr.t -> Flambda0.Expr.t)
  -> Flambda0.Expr.t
  -> Flambda0.Expr.t

val map_named
   : (Flambda0.Named.t -> Flambda0.Named.t)
  -> Flambda0.Expr.t
  -> Flambda0.Expr.t

val map_toplevel
   : (Flambda0.Expr.t -> Flambda0.Expr.t)
  -> (Flambda0.Named.t -> Flambda0.Named.t)
  -> Flambda0.Expr.t
  -> Flambda0.Expr.t

val map_toplevel_expr
   : (Flambda0.Expr.t -> Flambda0.Expr.t)
  -> Flambda0.Expr.t
  -> Flambda0.Expr.t

val map_toplevel_named
   : (Flambda0.Named.t -> Flambda0.Named.t)
  -> Flambda0.Expr.t
  -> Flambda0.Expr.t

val map_symbols
   : Flambda0.Expr.t
  -> f:(Symbol.t -> Symbol.t)
  -> Flambda0.Expr.t

val map_symbols_on_set_of_closures
  : Flambda0.Set_of_closures.t
  -> f:(Symbol.t -> Symbol.t)
  -> Flambda0.Set_of_closures.t

val map_toplevel_sets_of_closures
   : Flambda0.Expr.t
  -> f:(Flambda0.Set_of_closures.t -> Flambda0.Set_of_closures.t)
  -> Flambda0.Expr.t

val map_apply
   : Flambda0.Expr.t
  -> f:(Flambda0.apply -> Flambda0.apply)
  -> Flambda0.Expr.t

val map_function_bodies
   : ?ignore_stubs:unit
  -> Flambda0.Set_of_closures.t
  -> f:(Flambda0.Expr.t -> Flambda0.Expr.t)
  -> Flambda0.Set_of_closures.t

val map_sets_of_closures
   : Flambda0.Expr.t
  -> f:(Flambda0.Set_of_closures.t -> Flambda0.Set_of_closures.t)
  -> Flambda0.Expr.t

val map_sets_of_closures_of_program
   : Flambda_static0.Program.t
  -> f:(Flambda0.Set_of_closures.t -> Flambda0.Set_of_closures.t)
  -> Flambda_static0.Program.t

val map_project_var_to_named_opt
   : Flambda0.Expr.t
  -> f:(Projection.Project_var.t -> Flambda0.Named.t option)
  -> Flambda0.Expr.t

val map_exprs_at_toplevel_of_program
   : Flambda_static0.Program.t
  -> f:(Flambda0.Expr.t -> Flambda0.Expr.t)
  -> Flambda_static0.Program.t

val map_named_of_program
   : Flambda_static0.Program.t
  -> f:(Variable.t -> Flambda0.Named.t -> Flambda0.Named.t)
  -> Flambda_static0.Program.t

val map_all_immutable_let_and_let_rec_bindings
   : Flambda0.Expr.t
  -> f:(Variable.t -> Flambda0.Named.t -> Flambda0.Named.t)
  -> Flambda0.Expr.t

val fold_function_decls_ignoring_stubs
   : Flambda0.Set_of_closures.t
  -> init:'a
  -> f:(fun_var:Variable.t
    -> function_decl:Flambda0.Function_declaration.t
    -> 'a
    -> 'a)
  -> 'a
