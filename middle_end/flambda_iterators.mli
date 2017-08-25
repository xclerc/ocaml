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

(** Apply the given functions to the immediate subexpressions of the given
    Flambda expression.  For avoidance of doubt, if a subexpression is
    [Expr], it is passed to the function taking [Flambda.Named.t], rather
    than being followed and passed to the function taking [Flambda.Expr.t]. *)
val apply_on_subexpressions
   : (Flambda.Expr.t -> unit)
  -> (Flambda.Named.t -> unit)
  -> Flambda.Expr.t
  -> unit

val map_subexpressions
   : (Flambda.Expr.t -> Flambda.Expr.t)
  -> (Variable.t -> Flambda.Named.t -> Flambda.Named.t)
  -> Flambda.Expr.t
  -> Flambda.Expr.t

(* CR-soon lwhite: add comment to clarify that these recurse unlike the
   ones above *)
val iter
   : (Flambda.Expr.t -> unit)
  -> (Flambda.Named.t -> unit)
  -> Flambda.Expr.t
  -> unit

val iter_expr
   : (Flambda.Expr.t -> unit)
  -> Flambda.Expr.t
  -> unit

val iter_on_named
   : (Flambda.Expr.t -> unit)
  -> (Flambda.Named.t -> unit)
  -> Flambda.Named.t
  -> unit

(* CR-someday mshinwell: we might need to add the corresponding variable to
   the parameters of the user function for [iter_named] *)
val iter_named
   : (Flambda.Named.t -> unit)
  -> Flambda.Expr.t
  -> unit

(* CR-someday lwhite: These names are pretty indecipherable, perhaps
   create submodules for the normal and "on_named" variants of each
   function. *)

val iter_named_on_named
   : (Flambda.Named.t -> unit)
  -> Flambda.Named.t
  -> unit

(** [iter_toplevel f t] applies [f] on every toplevel subexpression of [t].
    In particular, it never applies [f] to the body of a function (which
    will always be contained within an [Set_of_closures] expression). *)
val iter_toplevel
   : (Flambda.Expr.t -> unit)
  -> (Flambda.Named.t -> unit)
  -> Flambda.Expr.t
  -> unit

val iter_named_toplevel
   : (Flambda.Expr.t -> unit)
  -> (Flambda.Named.t -> unit)
  -> Flambda.Named.t
  -> unit

val iter_on_sets_of_closures
   : (Flambda.Set_of_closures.t -> unit)
  -> Flambda.Expr.t
  -> unit

val iter_on_set_of_closures_of_program
   : Flambda_static.Program.t
  -> f:(constant:bool -> Flambda.Set_of_closures.t -> unit)
  -> unit

val iter_all_immutable_let_and_let_rec_bindings
   : Flambda.Expr.t
  -> f:(Variable.t -> Flambda.Named.t -> unit)
  -> unit

val iter_all_toplevel_immutable_let_and_let_rec_bindings
   : Flambda.Expr.t
  -> f:(Variable.t -> Flambda.Named.t -> unit)
  -> unit

(** Iterate over all expressions occurring directly at the toplevel of the
    program.  Note that the only function bodies iterated over are those
    bound to a symbol.  (That is to say, a function body in a set of closures
    [constant_defining_value] will be iterated over---but any subfunctions in
    the body will not be.  Likewise any function body defined by a normal
    [Let] will not be iterated over.)  If you want to iterate over those
    things as well, use [iter_exprs_at_toplevels_in_program]. *)
val iter_exprs_at_toplevel_of_program
   : Flambda_static.Program.t
  -> f:(continuation_arity:int -> Continuation.t -> Flambda.Expr.t -> unit)
  -> unit

(** Iterate over all toplevel expressions in the program:
    - bodies of functions, whether bound to symbols or not, including any
      subfunctions; and
    - [Effect] expressions. *)
val iter_exprs_at_toplevels_in_program
   : Flambda_static.Program.t
  -> f:(continuation_arity:int -> Continuation.t -> Flambda.Expr.t -> unit)
  -> unit

val iter_named_of_program
   : Flambda_static.Program.t
  -> f:(Flambda.Named.t -> unit)
  -> unit

val iter_constant_defining_values_on_program
  : Flambda_static.Program.t
  -> f:(Flambda_static.Constant_defining_value.t -> unit)
  -> unit

val iter_apply_on_program
   : Flambda_static.Program.t
  -> f:(Flambda.apply -> unit)
  -> unit

val map
   : (Flambda.Expr.t -> Flambda.Expr.t)
  -> (Flambda.Named.t -> Flambda.Named.t)
  -> Flambda.Expr.t
  -> Flambda.Expr.t

val map_expr
   : (Flambda.Expr.t -> Flambda.Expr.t)
  -> Flambda.Expr.t
  -> Flambda.Expr.t

val map_named
   : (Flambda.Named.t -> Flambda.Named.t)
  -> Flambda.Expr.t
  -> Flambda.Expr.t

val map_toplevel
   : (Flambda.Expr.t -> Flambda.Expr.t)
  -> (Flambda.Named.t -> Flambda.Named.t)
  -> Flambda.Expr.t
  -> Flambda.Expr.t

val map_toplevel_expr
   : (Flambda.Expr.t -> Flambda.Expr.t)
  -> Flambda.Expr.t
  -> Flambda.Expr.t

val map_toplevel_named
   : (Flambda.Named.t -> Flambda.Named.t)
  -> Flambda.Expr.t
  -> Flambda.Expr.t

val map_symbols
   : Flambda.Expr.t
  -> f:(Symbol.t -> Symbol.t)
  -> Flambda.Expr.t

val map_symbols_on_set_of_closures
  : Flambda.Set_of_closures.t
  -> f:(Symbol.t -> Symbol.t)
  -> Flambda.Set_of_closures.t

val map_toplevel_sets_of_closures
   : Flambda.Expr.t
  -> f:(Flambda.Set_of_closures.t -> Flambda.Set_of_closures.t)
  -> Flambda.Expr.t

val map_apply
   : Flambda.Expr.t
  -> f:(Flambda.apply -> Flambda.apply)
  -> Flambda.Expr.t

val map_function_bodies
   : ?ignore_stubs:unit
  -> Flambda.Set_of_closures.t
  -> f:(Flambda.Expr.t -> Flambda.Expr.t)
  -> Flambda.Set_of_closures.t

val map_sets_of_closures
   : Flambda.Expr.t
  -> f:(Flambda.Set_of_closures.t -> Flambda.Set_of_closures.t)
  -> Flambda.Expr.t

val map_sets_of_closures_of_program
   : Flambda_static.Program.t
  -> f:(Flambda.Set_of_closures.t -> Flambda.Set_of_closures.t)
  -> Flambda_static.Program.t

val map_project_var_to_named_opt
   : Flambda.Expr.t
  -> f:(Flambda.project_var -> Flambda.Named.t option)
  -> Flambda.Expr.t

val map_exprs_at_toplevel_of_program
   : Flambda_static.Program.t
  -> f:(Flambda.Expr.t -> Flambda.Expr.t)
  -> Flambda_static.Program.t

val map_named_of_program
   : Flambda_static.Program.t
  -> f:(Variable.t -> Flambda.Named.t -> Flambda.Named.t)
  -> Flambda_static.Program.t

val map_all_immutable_let_and_let_rec_bindings
   : Flambda.Expr.t
  -> f:(Variable.t -> Flambda.Named.t -> Flambda.Named.t)
  -> Flambda.Expr.t

val fold_function_decls_ignoring_stubs
   : Flambda.Set_of_closures.t
  -> init:'a
  -> f:(fun_var:Variable.t
    -> function_decl:Flambda.Function_declaration.t
    -> 'a
    -> 'a)
  -> 'a
