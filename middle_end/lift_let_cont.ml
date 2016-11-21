(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2016 OCamlPro SAS                                          *)
(*   Copyright 2016 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

type thing_to_lift =
  | Let of Variable.t * Flambda.named Flambda.With_free_variables.t
  | Let_mutable of Mutable_variable.t * Variable.t * Lambda.value_kind
  | Let_cont of Continuation.t * Flambda.let_cont_handler

let bind_things_to_lift ~rev_things ~around =
  List.fold_left (fun body (thing : thing_to_lift) : Flambda.expr ->
      match thing with
      | Let (var, defining_expr) ->
        Flambda.With_free_variables.create_let_reusing_defining_expr var
          defining_expr body
      | Let_mutable (var, initial_value, contents_kind) ->
        Let_mutable { var; initial_value; contents_kind; body; }
      | Let_cont (name, handler) ->
        Let_cont { name; body; handler; })
    around
    rev_things

module State = struct
  type t = {
    constants : (Variable.t * Flambda.named) list;
    to_be_lifted : (Continuation.t * Flambda.let_cont_handler) list;
    to_remain : thing_to_lift list;
    continuations_to_remain : Continuation.Set.t;
    variables_to_remain : Variable.Set.t;
    mutable_variables_to_remain : Mutable_variable.Set.t;
    (* [mutable_variables_used] is here to work around the fact that we don't
       have functions (or keep track of) mutable variable usage in [Flambda].
       This seems fine given that the longer-term plan is to remove mutable
       variables from Flambda entirely. *)
    mutable_variables_used : Mutable_variable.Set.t;
  }

  let create () = {
    constants = [];
    to_be_lifted = [];
    to_remain = [];
    continuations_to_remain = Continuation.Set.empty;
    variables_to_remain = Variable.Set.empty;
    mutable_variables_to_remain = Mutable_variable.Set.empty;
    mutable_variables_used = Mutable_variable.Set.empty;
  }

  let add_constant t ~var ~defining_expr =
    { t with
      constants = (var, defining_expr) :: t.constants;
    }

  let add_constants_from_state t ~from =
    { t with
      constants = from.constants @ t.constants;
    }

  let lift_continuation t ~name ~handler =
(*
Format.eprintf "Continuation %a lifted\n%!" Continuation.print name;
*)
    { t with
      to_be_lifted = (name, handler) :: t.to_be_lifted;
    }

  let to_remain t (thing : thing_to_lift) =
    let continuations_to_remain =
      match thing with
      | Let _ | Let_mutable _ -> t.continuations_to_remain
      | Let_cont (name, _) ->
(*
Format.eprintf "Continuation %a remaining\n%!" Continuation.print name;
*)
        Continuation.Set.add name t.continuations_to_remain
    in
    let variables_to_remain =
      match thing with
      | Let (var, _) -> Variable.Set.add var t.variables_to_remain
      | Let_mutable _ | Let_cont _ -> t.variables_to_remain
    in
    let mutable_variables_to_remain =
      match thing with
      | Let_mutable (var, _, _) ->
        Mutable_variable.Set.add var t.mutable_variables_to_remain
      | Let _ | Let_cont _ -> t.mutable_variables_to_remain
    in
    { t with
      to_remain = thing :: t.to_remain;
      continuations_to_remain;
      variables_to_remain;
      mutable_variables_to_remain;
    }

  let can_lift_if_using_continuation t cont =
    not (Continuation.Set.mem cont t.continuations_to_remain)

  let can_lift_if_using_continuations t conts =
    Continuation.Set.is_empty
      (Continuation.Set.inter conts t.continuations_to_remain)

  let can_lift_if_using_variables t vars =
    Variable.Set.is_empty (Variable.Set.inter vars t.variables_to_remain)

  let can_lift_if_using_mutable_variables t vars =
    Mutable_variable.Set.is_empty (
      Mutable_variable.Set.inter vars t.mutable_variables_to_remain)

  let constants t = t.constants
  let rev_to_be_lifted t = t.to_be_lifted
  let rev_to_remain t = t.to_remain

  let use_mutable_variable t var =
    { t with
      mutable_variables_used =
        Mutable_variable.Set.add var t.mutable_variables_used;
    }

  let forget_mutable_variable t var =
    { t with
      mutable_variables_used =
        Mutable_variable.Set.remove var t.mutable_variables_used;
    }

  let mutable_variables_used t = t.mutable_variables_used
end

let rec lift_expr (expr : Flambda.expr) ~state =
  match expr with
  | Let ({ var; defining_expr; body; } as let_expr) ->
    begin match defining_expr with
    | Const _ | Symbol _ ->
      let state = State.add_constant state ~var ~defining_expr in
      lift_expr body ~state
    | Var _ | Prim _ | Assign _ | Read_mutable _ | Read_symbol_field _
    | Allocated_const _ | Set_of_closures _ | Project_closure _
    | Move_within_set_of_closures _ | Project_var _ | Proved_unreachable ->
      let defining_expr, state =
        match defining_expr with
        | Set_of_closures set_of_closures ->
          let set_of_closures = lift_set_of_closures set_of_closures in
          let defining_expr : Flambda.named = Set_of_closures set_of_closures in
          Flambda.With_free_variables.of_named defining_expr, state
        | Read_mutable mut_var ->
          let state = State.use_mutable_variable state mut_var in
          Flambda.With_free_variables.of_defining_expr_of_let let_expr, state
        | _ ->
          Flambda.With_free_variables.of_defining_expr_of_let let_expr, state
      in
      let state = State.to_remain state (Let (var, defining_expr)) in
      lift_expr body ~state
    end
  | Let_mutable { var; initial_value; contents_kind; body; } ->
    let state =
      State.to_remain state (Let_mutable (var, initial_value, contents_kind))
    in
    let expr, state = lift_expr body ~state in
    expr, State.forget_mutable_variable state var
  | Let_cont { name; body; handler = (Alias alias_of) as handler; } ->
    let state =
      if State.can_lift_if_using_continuation state alias_of then
        State.lift_continuation state ~name ~handler
      else
        State.to_remain state (Let_cont (name, handler))
    in
    lift_expr body ~state
  | Let_cont { name; body; handler =
      Handler { params; recursive; handler; } } ->
(*
Format.eprintf "Lifting handler for %a\n%!" Continuation.print name;
*)
    let handler_terminator, handler_state =
      lift_expr handler ~state:(State.create ())
    in
(*
Format.eprintf "Finished handler for %a\n%!" Continuation.print name;
*)
    let state =
      State.add_constants_from_state state ~from:handler_state
    in
    let to_be_lifted = List.rev (State.rev_to_be_lifted handler_state) in
(*
let name' = name in
*)
    let state, handler_state =
      List.fold_left (fun (state, handler_state) (name, handler) ->
          let fcs =
            Flambda.free_continuations_of_let_cont_handler ~name ~handler
          in
          let fvs =
            Flambda.free_variables_of_let_cont_handler handler
          in
          let doesn't_use_params =
            Variable.Set.is_empty (
              Variable.Set.inter (Variable.Set.of_list params) fvs)
          in
(*
Format.eprintf "Considering lifting %a outside %a.  fvs %a DUP %b\n%!"
  Continuation.print name
  Continuation.print name'
  Variable.Set.print fvs
  doesn't_use_params;
*)
          (* Note that we don't have to check any uses of mutable variables
             in [handler], since any such uses would prevent [handler] from
             being in [to_be_lifted]. *)
          if State.can_lift_if_using_continuations state fcs
            && State.can_lift_if_using_variables state fvs
            && doesn't_use_params
          then
            State.lift_continuation state ~name ~handler, handler_state
          else
            state, State.to_remain handler_state (Let_cont (name, handler)))
        (state, handler_state)
        to_be_lifted
    in
    let rev_to_remain = State.rev_to_remain handler_state in
    let handler =
      bind_things_to_lift ~rev_things:rev_to_remain ~around:handler_terminator
    in
(*
Format.eprintf "New handler for %a is:\n%a\n"
  Continuation.print name Flambda.print handler;
*)
    let handler : Flambda.let_cont_handler =
      Handler {
        params;
        recursive;
        handler;
      }
    in
    let fcs = Flambda.free_continuations_of_let_cont_handler ~name ~handler in
    let fvs = Flambda.free_variables_of_let_cont_handler handler in
    let fvs_mut = State.mutable_variables_used handler_state in
    let state =
      if State.can_lift_if_using_continuations state fcs
        && State.can_lift_if_using_variables state fvs
        && State.can_lift_if_using_mutable_variables state fvs_mut
      then
        State.lift_continuation state ~name ~handler
      else
        State.to_remain state (Let_cont (name, handler))
    in
    lift_expr body ~state
  | Apply _ | Apply_cont _ | Switch _ -> expr, state

and lift_set_of_closures (set_of_closures : Flambda.set_of_closures) =
  let funs =
    Variable.Map.map (fun
            (function_decl : Flambda.function_declaration) ->
        Flambda.create_function_declaration
          ~params:function_decl.params
          ~continuation_param:function_decl.continuation_param
          ~body:(lift function_decl.body)
          ~stub:function_decl.stub
          ~dbg:function_decl.dbg
          ~inline:function_decl.inline
          ~specialise:function_decl.specialise
          ~is_a_functor:function_decl.is_a_functor)
      set_of_closures.function_decls.funs
  in
  let function_decls =
    Flambda.update_function_declarations
      set_of_closures.function_decls ~funs
  in
  Flambda.create_set_of_closures ~function_decls
    ~free_vars:set_of_closures.free_vars
    ~specialised_args:set_of_closures.specialised_args
    ~direct_call_surrogates:set_of_closures.direct_call_surrogates

and lift (expr : Flambda.t) =
  let expr, state = lift_expr expr ~state:(State.create ()) in
  let expr =
    bind_things_to_lift ~rev_things:(State.rev_to_remain state) ~around:expr
  in
  let expr =
    List.fold_left (fun body (name, handler) : Flambda.t ->
        Let_cont { name; body; handler; })
      expr
      (State.rev_to_be_lifted state)
  in
  List.fold_left (fun expr (var, const) ->
      Flambda.create_let var const expr)
    expr
    (State.constants state)

let run program =
  Flambda_iterators.map_exprs_at_toplevel_of_program program ~f:lift
