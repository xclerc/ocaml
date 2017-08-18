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

(** Environments, following the lexical scope of the program, used during
    simplification.  (See simplify.ml.) *)
type t

val invariant : t -> unit

(** Create a new environment.  If [never_inline] is true then the returned
    environment will prevent [Simplify] from inlining.  The
    [backend] parameter is used for passing information about the compiler
    backend being used.
    Newly-created environments have inactive [Freshening]s (see below) and do
    not initially hold any approximation information. *)
val create
   : never_inline:bool
  -> allow_continuation_inlining:bool
  -> allow_continuation_specialisation:bool
  -> backend:(module Backend_intf.S)
  -> round:int
  -> t

(** Obtain the first-class module that gives information about the
    compiler backend being used for compilation. *)
val backend : t -> (module Backend_intf.S)

(** Obtain the really_import_approx function from the backend module. *)
val really_import_approx
   : t
  -> (Simple_value_approx.t -> Simple_value_approx.t)

(** Which simplification round we are currently in. *)
val round : t -> int

(** Add the approximation of a variable---that is to say, some knowledge
    about the value(s) the variable may take on at runtime---to the
    environment. *)
val add : t -> Variable.t -> Value_kind.t -> Simple_value_approx.t -> t

val add_outer_scope
   : t
  -> Variable.t
  -> Value_kind.t
  -> Simple_value_approx.t
  -> t

(** Like [add], but for mutable variables. *)
val add_mutable : t -> Mutable_variable.t -> Simple_value_approx.t -> t

val add_continuation : t -> Continuation.t -> Continuation_approx.t -> t

val find_continuation : t -> Continuation.t -> Continuation_approx.t

val mem_continuation : t -> Continuation.t -> bool

(** Find the approximation of a given variable, raising a fatal error if
    the environment does not know about the variable.  Use [find_opt]
    instead if you need to catch the failure case. *)
val find_exn : t -> Variable.t -> Simple_value_approx.t * Value_kind.t

(** Like [find_exn], but for mutable variables. *)
val find_mutable_exn : t -> Mutable_variable.t -> Simple_value_approx.t

type scope = Current | Outer

val find_with_scope_exn : t -> Variable.t -> scope * Simple_value_approx.t

(** Like [find_exn], but intended for use where the "not present in
    environment" case is to be handled by the caller. *)
val find_opt : t -> Variable.t -> Simple_value_approx.t option

(** Like [find_exn], but for a list of variables. *)
val find_list_exn : t -> Variable.t list -> Simple_value_approx.t list

val vars_in_scope : t -> Variable.Set.t

val does_not_bind : t -> Variable.t list -> bool

val does_not_freshen : t -> Variable.t list -> bool

val add_symbol : t -> Symbol.t -> Simple_value_approx.t -> t
val redefine_symbol : t -> Symbol.t -> Simple_value_approx.t -> t
val find_symbol_exn : t -> Symbol.t -> Simple_value_approx.t
val find_symbol_opt : t -> Symbol.t -> Simple_value_approx.t option
val find_symbol_fatal : t -> Symbol.t -> Simple_value_approx.t

(* Like [find_symbol_exn], but load the symbol approximation using
   the backend if not available in the environment. *)
val find_or_load_symbol : t -> Symbol.t -> Simple_value_approx.t

(** Note that the given [bound_to] holds the given [projection]. *)
val add_projection
   : t
  -> projection:Projection.t
  -> bound_to:Variable.t
  -> t

(** Determine if the environment knows about a variable that is bound
    to the given [projection]. *)
val find_projection
   : t
  -> projection:Projection.t
  -> Variable.t option

(** Whether the environment has an approximation for the given variable. *)
val mem : t -> Variable.t -> bool

(** Return the freshening that should be applied to variables when
    rewriting code (in [Simplify], etc.) using the given
    environment. *)
val freshening : t -> Freshening.t

(** Set the freshening that should be used as per [freshening], above. *)
val set_freshening : t -> Freshening.t -> t

(** Causes every bound variable in code rewritten during inlining and
    simplification, using the given environment, to be freshened.  This is
    used when descending into subexpressions substituted into existing
    expressions. *)
val activate_freshening : t -> t

(** Erase all variable approximation information and freshening information
    from the given environment.  However, the freshening activation state
    is preserved.  This function is used when rewriting inside a function
    declaration, to avoid (due to a compiler bug) accidental use of
    variables from outer scopes that are not accessible. *)
val local : t -> t

(** Determine whether the inliner is currently inside a function body from
    the given set of closures.  This is used to detect whether a given
    function call refers to a function which exists somewhere on the current
    inlining stack. *)
val inside_set_of_closures_declaration : Set_of_closures_origin.t -> t -> bool

(** Not inside a closure declaration.
    Toplevel code is the one evaluated when the compilation unit is
    loaded *)
val at_toplevel : t -> bool

val is_inside_branch : t -> bool
val branch_depth : t -> int
val inside_branch : t -> t

val increase_closure_depth : t -> t

(** Mark that call sites contained within code rewritten using the given
    environment should never be replaced by inlined (or unrolled) versions
    of the callee(s). *)
val set_never_inline : t -> t

(** Equivalent to [set_never_inline] but only applies to code inside
    a set of closures. *)
val set_never_inline_inside_closures : t -> t

(** Unset the restriction from [set_never_inline_inside_closures] *)
val unset_never_inline_inside_closures : t -> t

(** Equivalent to [set_never_inline] but does not apply to code inside
    a set of closures. *)
val set_never_inline_outside_closures : t -> t

(** Unset the restriction from [set_never_inline_outside_closures] *)
val unset_never_inline_outside_closures : t -> t

(** Return whether [set_never_inline] is currently in effect on the given
    environment. *)
val never_inline : t -> bool

val never_inline_continuations : t -> bool
val never_specialise_continuations : t -> bool
val never_unbox_continuations : t -> bool

val disallow_continuation_inlining : t -> t
val disallow_continuation_specialisation : t -> t

(** Allow terms to be simplified under less precise approximation
    assumptions (see [less_precise_approximations] below). *)
val allow_less_precise_approximations : t -> t

(** Whether it is permissible for a term to be simplified under assumptions
    of less precise approximations than were used last time such term
    was simplified.  The process of simplification in such an environment
    is a "type inference only" procedure and the code resulting from it
    must be discarded.  Used when simplifying recursive continuations. *)
val less_precise_approximations : t -> bool

val inlining_level : t -> int

(** Mark that this environment is used to rewrite code for inlining. This is
    used by the inlining heuristics to decide whether to continue.
    Unconditionally inlined does not take this into account. *)
val inlining_level_up : t -> t

(** Whether we are actively unrolling a given function. *)
val actively_unrolling : t -> Set_of_closures_origin.t -> int option

(** Start actively unrolling a given function [n] times. *)
val start_actively_unrolling : t -> Set_of_closures_origin.t -> int -> t

(** Unroll a function currently actively being unrolled. *)
val continue_actively_unrolling : t -> Set_of_closures_origin.t -> t

(** Whether it is permissible to unroll a call to a recursive function
    in the given environment. *)
val unrolling_allowed : t -> Set_of_closures_origin.t -> bool

(** Whether the given environment is currently being used to rewrite the
    body of an unrolled recursive function. *)
val inside_unrolled_function : t -> Set_of_closures_origin.t -> t

(** Whether it is permissible to inline a call to a function in the given
    environment. *)
val inlining_allowed : t -> Closure_origin.t -> bool

(** Whether the given environment is currently being used to rewrite the
    body of an inlined function. *)
(* CR mshinwell: comment wrong? *)
val inside_inlined_function : t -> Closure_origin.t -> t

(** If collecting inlining statistics, record that the inliner is about to
    descend into [closure_id].  This information enables us to produce a
    stack of closures that form a kind of context around an inlining
    decision point. *)
val note_entering_closure
   : t
  -> closure_id:Closure_id.t
  -> dbg:Debuginfo.t
  -> t

 (** If collecting inlining statistics, record that the inliner is about to
     descend into a call to [closure_id].  This information enables us to
     produce a stack of closures that form a kind of context around an
     inlining decision point. *)
val note_entering_call
   : t
  -> closure_id:Closure_id.t
  -> dbg:Debuginfo.t
  -> t

 (** If collecting inlining statistics, record that the inliner is about to
     descend into an inlined function call.  This requires that the inliner
     has already entered the call with [note_entering_call]. *)
val note_entering_inlined : t -> t

 (** If collecting inlining statistics, record that the inliner is about to
     descend into a specialised function definition.  This requires that the
     inliner has already entered the call with [note_entering_call]. *)
val note_entering_specialised : t -> closure_ids:Closure_id.Set.t -> t

(** Update a given environment to record that the inliner is about to
    descend into [closure_id] and pass the resulting environment to [f].
    If [inline_inside] is [false] then the environment passed to [f] will be
    marked as [never_inline] (see above). *)
val enter_closure
   : t
  -> closure_id:Closure_id.t
  -> inline_inside:bool
  -> dbg:Debuginfo.t
  -> f:(t -> 'a)
  -> 'a

 (** If collecting inlining statistics, record an inlining decision for the
     call at the top of the closure stack stored inside the given
     environment. *)
val record_decision
   : t
  -> Inlining_stats_types.Decision.t
  -> unit

(** Print a human-readable version of the given environment. *)
val print : Format.formatter -> t -> unit

(** The environment stores the call-site being inlined to produce
    precise location information. This function sets the current
    call-site being inlined.  *)
val set_inline_debuginfo : t -> dbg:Debuginfo.t -> t

(** Appends the locations of inlined call-sites to the [~dbg] argument *)
val add_inlined_debuginfo : t -> dbg:Debuginfo.t -> Debuginfo.t

val continuations_in_scope : t -> Continuation_approx.t Continuation.Map.t
