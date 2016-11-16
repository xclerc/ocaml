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

(* CR mshinwell: We should also do:
     let x = <named> in
     let_cont k = <handler> in
     <body>
   -->
     let_cont k =
       let x = ... in <handler>
     in
     <body>

  when <named> has only generative effects and x is not free in <body>
  and k is non-recursive.
*)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

type thing_to_lift =
  | Let of Variable.t * Flambda.named Flambda.With_free_variables.t
  | Let_mutable of Mutable_variable.t * Variable.t * Lambda.value_kind
  | Let_cont of Continuation.t * Flambda.let_cont_handler

let free_continuations_and_variables_of_thing_to_lift (thing : thing_to_lift) =
  match thing with
  | Let (_var, named) ->
    Continuation.Set.empty, Flambda.With_free_variables.free_variables named
  | Let_mutable (_mut_var, var, _kind) ->
    Continuation.Set.empty, Variable.Set.singleton var
  | Let_cont (name, handler) ->
    Flambda.free_continuations_of_let_cont_handler ~name ~handler,
      Flambda.free_variables_of_let_cont_handler handler

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
  }

  let create () = {
    constants = [];
    to_be_lifted = [];
    to_remain = [];
    continuations_to_remain = Continuation.Set.empty;
    variables_to_remain = Variable.Set.empty;
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
    { t with
      to_be_lifted = (name, handler) :: t.to_be_lifted;
    }

  let to_remain t (thing : thing_to_lift) =
    let fcs, fvs = free_continuations_and_variables_of_thing_to_lift thing in
    let continuations_to_remain =
      Continuation.Set.union fcs t.continuations_to_remain
    in
    let variables_to_remain =
      Variable.Set.union fvs t.variables_to_remain
    in
    { t with
      to_remain = thing :: t.to_remain;
      continuations_to_remain;
      variables_to_remain;
    }

  let can_lift_if_using_continuation t cont =
    not (Continuation.Set.mem cont t.continuations_to_remain)

  let can_lift_if_using_continuations t conts =
    Continuation.Set.is_empty
      (Continuation.Set.inter conts t.continuations_to_remain)

  let can_lift_if_using_variables t vars =
    Variable.Set.is_empty (Variable.Set.inter vars t.variables_to_remain)

  let constants t = t.constants
  let rev_to_be_lifted t = t.to_be_lifted
  let rev_to_remain t = t.to_remain
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
      let defining_expr =
        match defining_expr with
        | Set_of_closures set_of_closures ->
          let set_of_closures = lift_set_of_closures set_of_closures in
          let defining_expr : Flambda.named = Set_of_closures set_of_closures in
          Flambda.With_free_variables.of_named defining_expr
        | _ -> Flambda.With_free_variables.of_defining_expr_of_let let_expr
      in
      let state = State.to_remain state (Let (var, defining_expr)) in
      lift_expr body ~state
    end
  | Let_mutable { var; initial_value; contents_kind; body; } ->
    let state =
      State.to_remain state (Let_mutable (var, initial_value, contents_kind))
    in
    lift_expr body ~state
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
    let handler_terminator, handler_state =
      lift_expr handler ~state:(State.create ())
    in
    let state =
      State.add_constants_from_state state ~from:handler_state
    in
    let to_be_lifted = List.rev (State.rev_to_be_lifted handler_state) in
    let state =
      List.fold_left (fun state (name, handler) ->
          let fcs =
            Flambda.free_continuations_of_let_cont_handler ~name ~handler
          in
          let fvs =
            Flambda.free_variables_of_let_cont_handler handler
          in
          if State.can_lift_if_using_continuations state fcs
            && State.can_lift_if_using_variables state fvs
          then
            State.lift_continuation state ~name ~handler
          else
            State.to_remain state (Let_cont (name, handler)))
        state
        to_be_lifted
    in
    let rev_to_remain = State.rev_to_remain handler_state in
    let handler =
      bind_things_to_lift ~rev_things:rev_to_remain ~around:handler_terminator
    in
    let fcs = Flambda.free_continuations handler in
    let fvs = Flambda.free_variables handler in
    let handler : Flambda.continuation_handler =
      { params;
        recursive;
        handler;
      }
    in
    let state =
      if State.can_lift_if_using_continuations state fcs
        && State.can_lift_if_using_variables state fvs
      then
        State.lift_continuation state ~name ~handler:(Handler handler)
      else
        State.to_remain state (Let_cont (name, Handler handler))
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

and lift_constant_defining_value (def : Flambda.constant_defining_value)
      : Flambda.constant_defining_value =
  match def with
  | Allocated_const _ | Block _ | Project_closure _ -> def
  | Set_of_closures set_of_closures ->
    Set_of_closures (lift_set_of_closures set_of_closures)

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

let rec lift_program_body (body : Flambda.program_body) : Flambda.program_body =
  match body with
  | Let_symbol (sym, defining_value, body) ->
    let defining_value = lift_constant_defining_value defining_value in
    Let_symbol (sym, defining_value, lift_program_body body)
  | Let_rec_symbol (bindings, body) ->
    let bindings =
      List.map (fun (sym, defining_value) ->
          let defining_value = lift_constant_defining_value defining_value in
          sym, defining_value)
        bindings
    in
    Let_rec_symbol (bindings, lift_program_body body)
  | Initialize_symbol (sym, tag, fields, body) ->
    let fields = List.map (fun (expr, cont) -> lift expr, cont) fields in
    Initialize_symbol (sym, tag, fields, lift_program_body body)
  | Effect (expr, cont, body) ->
    let expr = lift expr in
    Effect (expr, cont, lift_program_body body)
  | End _ -> body

let run (program : Flambda.program) =
  { program with
    program_body = lift_program_body program.program_body;
  }
