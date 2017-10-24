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

type t = {
  backend : (module Backend_intf.S);
  simplify_toplevel:(
       t
    -> Simplify_result.t
    -> Flambda.Expr.t
    -> continuation:Continuation.t
    -> descr:string
    -> Flambda.Expr.t * Simplify_result.t);
  simplify_expr:(
       t
    -> Simplify_result.t
    -> Flambda.Expr.t
    -> Flambda.Expr.t * Simplify_result.t);
  simplify_apply_cont_to_cont:(
       ?don't_record_use:unit
    -> t
    -> Simplify_result.t
    -> Continuation.t
    -> arg_tys:Flambda_type.t list
    -> Continuation.t * Simplify_result.t);
  round : int;
  variables : Flambda_type.t Variable.Map.t;
  mutable_variables : Flambda_type.t Mutable_variable.Map.t;
  symbols : Flambda_type.Of_symbol.t Symbol.Map.t;
  continuations : Continuation_approx.t Continuation.Map.t;
  projections : Variable.t Projection.Map.t;
  current_functions : Set_of_closures_origin.Set.t;
  (* The functions currently being declared: used to avoid inlining
     recursively *)
  inlining_level : int;
  (* Number of times "inline" has been called recursively *)
  inside_branch : int;
  freshening : Freshening.t;
  never_inline : bool;
  never_inline_inside_closures : bool;
  never_inline_outside_closures : bool;
  allow_continuation_inlining : bool;
  allow_continuation_specialisation : bool;
  unroll_counts : int Set_of_closures_origin.Map.t;
  inlining_counts : int Closure_origin.Map.t;
  actively_unrolling : int Set_of_closures_origin.Map.t;
  closure_depth : int;
  inlining_stats_closure_stack : Inlining_stats.Closure_stack.t;
  inlined_debuginfo : Debuginfo.t;
}

let create ~never_inline ~allow_continuation_inlining
      ~allow_continuation_specialisation ~round ~backend
      ~simplify_toplevel ~simplify_expr ~simplify_apply_cont_to_cont =
  { backend;
    round;
    variables = Variable.Map.empty;
    mutable_variables = Mutable_variable.Map.empty;
    symbols = Symbol.Map.empty;
    continuations = Continuation.Map.empty;
    projections = Projection.Map.empty;
    current_functions = Set_of_closures_origin.Set.empty;
    inlining_level = 0;
    inside_branch = 0;
    freshening = Freshening.empty;
    never_inline;
    never_inline_inside_closures = false;
    never_inline_outside_closures = false;
    allow_continuation_inlining;
    allow_continuation_specialisation;
    unroll_counts = Set_of_closures_origin.Map.empty;
    inlining_counts = Closure_origin.Map.empty;
    actively_unrolling = Set_of_closures_origin.Map.empty;
    closure_depth = 0;
    inlining_stats_closure_stack =
      Inlining_stats.Closure_stack.create ();
    inlined_debuginfo = Debuginfo.none;
    simplify_toplevel;
    simplify_expr;
    simplify_apply_cont_to_cont;
  }

let print ppf t =
  Format.fprintf ppf
    "Environment maps: %a@.Projections: %a@.Freshening: %a@.\
      Continuations: %a@.Currently inside functions: %a@.\
      Never inline: %b@.Never inline inside closures: %b@.\
      Never inline outside closures: %b@."
    Variable.Set.print (Variable.Map.keys t.variables)
    (Projection.Map.print Variable.print) t.projections
    Freshening.print t.freshening
    (Continuation.Map.print Continuation_approx.print) t.continuations
    Set_of_closures_origin.Set.print t.current_functions
    t.never_inline
    t.never_inline_inside_closures
    t.never_inline_outside_closures

let backend t = t.backend
let importer t = t.backend
let round t = t.round
let simplify_toplevel t = t.simplify_toplevel
let simplify_expr t = t.simplify_expr
let simplify_apply_cont_to_cont t = t.simplify_apply_cont_to_cont

let local env =
  { env with
    variables = Variable.Map.empty;
    continuations = Continuation.Map.empty;
    projections = Projection.Map.empty;
    freshening = Freshening.empty_preserving_activation_state env.freshening;
    inlined_debuginfo = Debuginfo.none;
  }

let mem t var = Variable.Map.mem var t.variables

let add t var ty =
  let ty = Flambda_type.augment_with_variable ty var in
  let variables = Variable.Map.add var ty t.variables in
  { t with variables; }

let add_mutable t mut_var ty =
  { t with mutable_variables =
    Mutable_variable.Map.add mut_var ty t.mutable_variables;
  }

let find_symbol_exn t symbol =
  match Symbol.Map.find symbol t.symbols with
  | exception Not_found ->
    if Compilation_unit.equal
        (Compilation_unit.get_current_exn ())
        (Symbol.compilation_unit symbol)
    then begin
      Misc.fatal_errorf "Symbol %a from the current compilation unit is \
          unbound.  Maybe there is a missing [Let_symbol] or similar?"
        Symbol.print symbol
    end;
    Flambda_type.symbol_loaded_lazily symbol
  | ty -> ty

let add_projection t ~projection ~bound_to =
  { t with
    projections =
      Projection.Map.add projection bound_to t.projections;
  }

let find_projection t ~projection =
  match Projection.Map.find projection t.projections with
  | exception Not_found -> None
  | var -> Some var

let add_continuation t cont ty =
  { t with
    continuations = Continuation.Map.add cont ty t.continuations;
  }

let find_continuation t cont =
  match Continuation.Map.find cont t.continuations with
  | exception Not_found ->
    Misc.fatal_errorf "Unbound continuation %a.\n@ \n%a\n%!"
      Continuation.print cont
      print t
  | ty -> ty

let mem_continuation t cont =
  Continuation.Map.mem cont t.continuations

let does_not_bind t vars =
  not (List.exists (fun var -> mem t var) vars)

let does_not_freshen t vars =
  Freshening.does_not_freshen t.freshening vars

let add_symbol t symbol ty =
  match find_symbol_exn t symbol with
  | exception Not_found ->
    { t with
      symbols = Symbol.Map.add symbol ty t.symbols;
    }
  | _ ->
    Misc.fatal_errorf "Attempt to redefine symbol %a (to %a) in environment \
        for [Simplify]"
      Symbol.print symbol
      Flambda_type.print ty

let redefine_symbol t symbol ty =
  match find_symbol_exn t symbol with
  | exception Not_found ->
    Misc.fatal_errorf "Cannot redefine undefined symbol %a"
      Symbol.print symbol
  | _ ->
    { t with
      symbols = Symbol.Map.add symbol ty t.symbols;
    }

let find_exn t id =
  try
    really_import_ty_with_scope t
      (Variable.Map.find id t.variables)
  with Not_found ->
    Misc.fatal_errorf "Env.find_with_scope_exn: Unbound variable \
        %a@.%s@. Environment: %a@."
      Variable.print id
      (Printexc.raw_backtrace_to_string (Printexc.get_callstack max_int))
      print t

let find_mutable_exn t mut_var =
  try Mutable_variable.Map.find mut_var t.mutable_variables
  with Not_found ->
    Misc.fatal_errorf "Env.find_mutable_exn: Unbound variable \
        %a@.%s@. Environment: %a@."
      Mutable_variable.print mut_var
      (Printexc.raw_backtrace_to_string (Printexc.get_callstack max_int))
      print t

let find_list_exn t vars =
  List.map (fun var -> find_exn t var) vars

let variables_in_scope t = Variable.Map.keys t.variables

let find_opt t id =
  try Some (really_import_ty t
              (snd (Variable.Map.find id t.variables)))
  with Not_found -> None

let activate_freshening t =
  { t with freshening = Freshening.activate t.freshening }

(* CR-someday mshinwell: consider changing name to remove "declaration".
   Also, isn't this the inlining stack?  Maybe we can use that instead. *)
let enter_set_of_closures_declaration t origin =
(*
Format.eprintf "Entering decl: have %a, adding %a, result %a\n%!"
Set_of_closures_origin.Set.print t.current_functions
Set_of_closures_origin.print origin
Set_of_closures_origin.Set.print
  (Set_of_closures_origin.Set.add origin t.current_functions);
*)
  { t with
    current_functions =
      Set_of_closures_origin.Set.add origin t.current_functions; }

let inside_set_of_closures_declaration origin t =
  Set_of_closures_origin.Set.mem origin t.current_functions

let at_toplevel t =
  t.closure_depth = 0

let is_inside_branch env = env.inside_branch > 0

let branch_depth env = env.inside_branch

let inside_branch t =
  { t with inside_branch = t.inside_branch + 1 }

let set_freshening t freshening  =
  { t with freshening; }

let increase_closure_depth t =
  let ty =
    Variable.Map.map (fun (_scope, ty) -> Outer, ty) t.variables
  in
  { t with
    ty;
    closure_depth = t.closure_depth + 1;
  }

let set_never_inline t =
  if t.never_inline then t
  else { t with never_inline = true }

let set_never_inline_inside_closures t =
  if t.never_inline_inside_closures then t
  else { t with never_inline_inside_closures = true }

let unset_never_inline_inside_closures t =
  if t.never_inline_inside_closures then
    { t with never_inline_inside_closures = false }
  else t

let set_never_inline_outside_closures t =
  if t.never_inline_outside_closures then t
  else { t with never_inline_outside_closures = true }

let unset_never_inline_outside_closures t =
  if t.never_inline_outside_closures then
    { t with never_inline_outside_closures = false }
  else t

let inlining_level_up env =
  let max_level =
    Clflags.Int_arg_helper.get ~key:(env.round) !Clflags.inline_max_depth
  in
  if (env.inlining_level + 1) > max_level then begin
    (* CR mshinwell: Is this a helpful error?  Should we just make this
       robust? *)
    Misc.fatal_error "Inlining level increased above maximum"
  end;
  { env with inlining_level = env.inlining_level + 1 }

let actively_unrolling t origin =
  match Set_of_closures_origin.Map.find origin t.actively_unrolling with
  | count -> Some count
  | exception Not_found -> None

let start_actively_unrolling t origin i =
  let actively_unrolling =
    Set_of_closures_origin.Map.add origin i t.actively_unrolling
  in
  { t with actively_unrolling }

let continue_actively_unrolling t origin =
  let unrolling =
    try
      Set_of_closures_origin.Map.find origin t.actively_unrolling
    with Not_found ->
      Misc.fatal_error "Unexpected actively unrolled function";
  in
  let actively_unrolling =
    Set_of_closures_origin.Map.add origin (unrolling - 1) t.actively_unrolling
  in
  { t with actively_unrolling }

let unrolling_allowed t origin =
  let unroll_count =
    try
      Set_of_closures_origin.Map.find origin t.unroll_counts
    with Not_found ->
      Clflags.Int_arg_helper.get
        ~key:t.round !Clflags.inline_max_unroll
  in
  unroll_count > 0

let inside_unrolled_function t origin =
  let unroll_count =
    try
      Set_of_closures_origin.Map.find origin t.unroll_counts
    with Not_found ->
      Clflags.Int_arg_helper.get
        ~key:t.round !Clflags.inline_max_unroll
  in
  let unroll_counts =
    Set_of_closures_origin.Map.add
      origin (unroll_count - 1) t.unroll_counts
  in
  { t with unroll_counts }

let inlining_allowed t id =
  let inlining_count =
    try
      Closure_origin.Map.find id t.inlining_counts
    with Not_found ->
      max 1 (Clflags.Int_arg_helper.get
               ~key:t.round !Clflags.inline_max_unroll)
  in
  inlining_count > 0

let inside_inlined_function t id =
  let inlining_count =
    try
      Closure_origin.Map.find id t.inlining_counts
    with Not_found ->
      max 1 (Clflags.Int_arg_helper.get
               ~key:t.round !Clflags.inline_max_unroll)
  in
  let inlining_counts =
    Closure_origin.Map.add id (inlining_count - 1) t.inlining_counts
  in
  { t with inlining_counts }

let inlining_level t = t.inlining_level
let freshening t = t.freshening
let never_inline t = t.never_inline || t.never_inline_outside_closures

let disallow_continuation_inlining t =
  { t with allow_continuation_inlining = false; }

let never_inline_continuations t =
  not t.allow_continuation_inlining

let disallow_continuation_specialisation t =
  { t with allow_continuation_specialisation = false; }

let never_specialise_continuations t =
  not t.allow_continuation_specialisation

(* CR mshinwell: may want to split this out properly *)
let never_unbox_continuations = never_specialise_continuations

let note_entering_closure t ~closure_id ~dbg =
  if t.never_inline then t
  else
    { t with
      inlining_stats_closure_stack =
        Inlining_stats.Closure_stack.note_entering_closure
          t.inlining_stats_closure_stack ~closure_id ~dbg;
    }

let note_entering_call t ~closure_id ~dbg =
  if t.never_inline then t
  else
    { t with
      inlining_stats_closure_stack =
        Inlining_stats.Closure_stack.note_entering_call
          t.inlining_stats_closure_stack ~closure_id ~dbg;
    }

let note_entering_inlined t =
  if t.never_inline then t
  else
    { t with
      inlining_stats_closure_stack =
        Inlining_stats.Closure_stack.note_entering_inlined
          t.inlining_stats_closure_stack;
    }

let note_entering_specialised t ~closure_ids =
  if t.never_inline then t
  else
    { t with
      inlining_stats_closure_stack =
        Inlining_stats.Closure_stack.note_entering_specialised
          t.inlining_stats_closure_stack ~closure_ids;
    }

let enter_closure t ~closure_id ~inline_inside ~dbg ~f =
  let t =
    if inline_inside && not t.never_inline_inside_closures then t
    else set_never_inline t
  in
  let t = unset_never_inline_outside_closures t in
  f (note_entering_closure t ~closure_id ~dbg)

let record_decision t decision =
  Inlining_stats.record_decision decision
    ~closure_stack:t.inlining_stats_closure_stack

let set_inline_debuginfo t ~dbg =
  { t with inlined_debuginfo = dbg }

let add_inlined_debuginfo t ~dbg =
  Debuginfo.concat t.inlined_debuginfo dbg

let continuations_in_scope t = t.continuations

let invariant t =
  if !Clflags.flambda_invariant_checks then begin
    (* Make sure that freshening a continuation through the given
       environment doesn't yield a continuation not bound by the
       environment. *)
    let from_freshening =
      Freshening.range_of_continuation_freshening t.freshening
    in
    Continuation.Set.iter (fun cont ->
        match Continuation.Map.find cont t.continuations with
        | exception Not_found ->
          Misc.fatal_errorf "The freshening in this environment maps to \
              continuation %a, but that continuation is unbound:@;%a"
            Continuation.print cont
            print t
        | _ -> ())
      from_freshening
  end
