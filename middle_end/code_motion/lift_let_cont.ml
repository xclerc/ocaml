(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2016--2017 OCamlPro SAS                                    *)
(*   Copyright 2016--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module Constant_or_symbol = struct
  type t =
    | Constant of Flambda.Const.t
    | Symbol of Symbol.Of_kind_value.t

  include Identifiable.Make (struct
    type nonrec t = t

    let compare t1 t2 =
      match t1, t2 with
      | Constant c1, Constant c2 -> Flambda.Const.compare c1 c2
      | Symbol s1, Symbol s2 -> Symbol.Of_kind_value.compare s1 s2
      | Constant _, _ -> (-1)
      | _, Constant _ -> 1

    let equal t1 t2 = (compare t1 t2) = 0

    let hash t =
      match t with
      | Constant c -> Hashtbl.hash (0, Flambda.Const.hash c)
      | Symbol s -> Hashtbl.hash (1, Symbol.Of_kind_value.hash s)

    let print ppf t =
      match t with
      | Constant c ->
        Format.fprintf ppf "(Constant %a)" Flambda.Const.print c
      | Symbol s ->
        Format.fprintf ppf "(Symbol %a)" Symbol.Of_kind_value.print s
  end)

  let to_named t : Flambda.Named.t =
    match t with
    | Constant const -> Const const
    | Symbol sym -> Symbol sym
end

type thing_to_lift =
  | Let of Variable.t * Flambda.Named.t Flambda.With_free_variables.t
  | Let_mutable of Mutable_variable.t * Variable.t * Flambda_type.t
  | Let_cont of Flambda.Let_cont_handlers.t

let bind_things_to_remain ~rev_things ~around =
  List.fold_left (fun body (thing : thing_to_lift) : Flambda.Expr.t ->
      match thing with
      | Let (var, defining_expr) ->
        Flambda.With_free_variables.create_let_reusing_defining_expr var
          defining_expr body
      | Let_mutable (var, initial_value, contents_type) ->
        Let_mutable { var; initial_value; contents_type; body; }
      | Let_cont handlers ->
        Let_cont { body; handlers; })
    around
    rev_things

module State = struct
  type t = {
    constants : (Variable.t * Flambda.Named.t) list;
    to_be_lifted : Flambda.Let_cont_handlers.t list;
    to_remain : thing_to_lift list;
    continuations_to_remain : Continuation.Set.t;
    variables_to_remain : Variable.Set.t;
    (* [mutable_variables_used] is here to work around the fact that we don't
       have functions (or keep track of) mutable variable usage in [Flambda].
       This seems fine given that the longer-term plan is to remove mutable
       variables from Flambda entirely. *)
    mutable_variables_used : Mutable_variable.Set.t;
  }

  let create ~variables_to_remain ~continuations_to_remain =
    { constants = [];
      to_be_lifted = [];
      to_remain = [];
      continuations_to_remain;
      variables_to_remain = Variable.Set.of_list variables_to_remain;
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

  let lift_continuations t ~handlers =
    { t with
      to_be_lifted = handlers :: t.to_be_lifted;
    }

  let to_remain t (thing : thing_to_lift) =
    let continuations_to_remain =
      match thing with
      | Let _ | Let_mutable _ -> t.continuations_to_remain
      | Let_cont (Nonrecursive { name; _ }) ->
        Continuation.Set.add name t.continuations_to_remain
      | Let_cont (Recursive handlers) ->
        Continuation.Set.union (Continuation.Map.keys handlers)
          t.continuations_to_remain
    in
    let variables_to_remain =
      match thing with
      | Let (var, _) -> Variable.Set.add var t.variables_to_remain
      | Let_mutable _ | Let_cont _ -> t.variables_to_remain
    in
    { t with
      to_remain = thing :: t.to_remain;
      continuations_to_remain;
      variables_to_remain;
    }

  let can_lift_if_using_continuations t conts =
    Continuation.Set.is_empty
      (Continuation.Set.inter conts t.continuations_to_remain)

  let can_lift_if_using_variables t vars =
    Variable.Set.is_empty (Variable.Set.inter vars t.variables_to_remain)

  let constants t = t.constants
  let rev_to_be_lifted t = t.to_be_lifted
  let rev_to_remain t = t.to_remain

  let use_mutable_variable t mut_var =
    { t with
      mutable_variables_used =
        Mutable_variable.Set.add mut_var t.mutable_variables_used;
    }

  let use_mutable_variables t mut_vars =
    { t with
      mutable_variables_used =
        Mutable_variable.Set.union mut_vars t.mutable_variables_used;
    }

  let forget_mutable_variable t var =
    { t with
      mutable_variables_used =
        Mutable_variable.Set.remove var t.mutable_variables_used;
    }

  let mutable_variables_used t = t.mutable_variables_used

  let uses_no_mutable_variables t =
    Mutable_variable.Set.is_empty t.mutable_variables_used
end

let rec lift_let_cont ~importer ~body ~handlers ~state
      ~(recursive : Asttypes.rec_flag) =
  let bound_recursively =
    match recursive with
    | Nonrecursive -> Continuation.Set.empty
    | Recursive -> Continuation.Map.keys handlers
  in
  let handler_terminators_and_states =
    Continuation.Map.map (fun (handler : Flambda.Continuation_handler.t) ->
        let state =
          (* XXX here and elsewhere, check if we need to take account of
             free variables in the types. *)
          State.create
            ~variables_to_remain:
              (Flambda.Typed_parameter.List.vars handler.params)
            ~continuations_to_remain:bound_recursively
        in
        let handler_terminator, state =
          lift_expr ~importer handler.handler ~state
        in
        handler, handler_terminator, state)
      handlers
  in
  let state =
    Continuation.Map.fold (fun _cont (_handler, _expr, handler_state) state ->
        State.add_constants_from_state state ~from:handler_state)
      handler_terminators_and_states
      state
  in
  let state, handlers, cannot_lift =
    Continuation.Map.fold (fun cont (handler, handler_terminator, handler_state)
            (state, handlers, cannot_lift) ->
        (* There are two separate things here:
           1. Lifting of continuations out of the handler.
           2. Lifting of the handler itself (which may only be done if
              all simultaneously-defined handlers can also be lifted). *)
        let state =
          List.fold_left (fun state handlers ->
              let fcs = Flambda.Let_cont_handlers.free_continuations handlers in
              let fvs = Flambda.Let_cont_handlers.free_variables handlers in
              (* Note that we don't have to check any uses of mutable variables
                 in [handler], since any such uses would prevent [handler] from
                 being in [to_be_lifted]. *)
              if State.can_lift_if_using_continuations state fcs
                && State.can_lift_if_using_variables state fvs
              then
                State.lift_continuations state ~handlers
              else
                State.to_remain state (Let_cont handlers))
            state
            (List.rev (State.rev_to_be_lifted handler_state))
        in
        let rev_to_remain = State.rev_to_remain handler_state in
        let new_handler =
          bind_things_to_remain ~rev_things:rev_to_remain
            ~around:handler_terminator
        in
        let handler : Flambda.Continuation_handler.t =
          { handler with
            handler = new_handler;
          }
        in
        let handlers = Continuation.Map.add cont handler handlers in
(*
        let fvs_specialised_args =
          Flambda.Expr.free_variables_of_specialised_args
            handler.specialised_args
        in
*)
        let fvs_mut = State.mutable_variables_used handler_state in
        let state =
          State.use_mutable_variables state fvs_mut
        in
        let cannot_lift =
          cannot_lift
            || not (State.uses_no_mutable_variables handler_state)
(*
            || not (State.can_lift_if_using_variables state
              fvs_specialised_args)
*)
        in
        state, handlers, cannot_lift)
      handler_terminators_and_states
      (state, Continuation.Map.empty, false)
  in
  let handlers : Flambda.Let_cont_handlers.t =
    match recursive with
    | Recursive -> Recursive handlers
    | Nonrecursive ->
      match Continuation.Map.bindings handlers with
      | [name, handler] -> Nonrecursive { name; handler; }
      | _ -> assert false
  in
  let fcs = Flambda.Let_cont_handlers.free_continuations handlers in
  let fvs = Flambda.Let_cont_handlers.free_variables handlers in
  let can_lift_handler =
    (not cannot_lift)
      && State.can_lift_if_using_continuations state fcs
      && State.can_lift_if_using_variables state fvs
  in
  let state =
    if can_lift_handler then State.lift_continuations state ~handlers
    else State.to_remain state (Let_cont handlers)
  in
  lift_expr ~importer body ~state

and lift_expr ~importer (expr : Flambda.Expr.t) ~state =
  match expr with
  | Let ({ var; defining_expr; body; } as let_expr) ->
    begin match defining_expr with
    | Const _ | Symbol _ ->
      let state = State.add_constant state ~var ~defining_expr in
      lift_expr ~importer body ~state
    | Var _ | Prim _ | Assign _ | Read_mutable _ | Field_of_symbol _
    | Allocated_const _ | Set_of_closures _ | Project_closure _
    | Move_within_set_of_closures _ | Project_var _ ->
      let defining_expr, state =
        match defining_expr with
        | Set_of_closures set_of_closures ->
          let set_of_closures =
            lift_set_of_closures ~importer set_of_closures
          in
          let defining_expr : Flambda.Named.t =
            Set_of_closures set_of_closures
          in
          Flambda.With_free_variables.of_named (Flambda_kind.value Must_scan)
            defining_expr, state
        | Read_mutable mut_var ->
          let state = State.use_mutable_variable state mut_var in
          Flambda.With_free_variables.of_defining_expr_of_let let_expr, state
        | Assign { being_assigned; new_value = _; } ->
          let state = State.use_mutable_variable state being_assigned in
          Flambda.With_free_variables.of_defining_expr_of_let let_expr, state
        | _ ->
          Flambda.With_free_variables.of_defining_expr_of_let let_expr, state
      in
      let state = State.to_remain state (Let (var, defining_expr)) in
      lift_expr ~importer body ~state
    end
  | Let_mutable { var; initial_value; contents_type; body; } ->
    let state =
      State.to_remain state (Let_mutable (var, initial_value, contents_type))
    in
    let expr, state = lift_expr ~importer body ~state in
    expr, State.forget_mutable_variable state var
  | Let_cont { body; handlers = Nonrecursive ({ name; handler; }); }
      when handler.is_exn_handler ->
    (* Don't lift anything out of the scope of an exception handler.
       Otherwise we might end up with lifted blocks that could jump (in the
       case of an exception) to a continuation that isn't in scope. *)
    (* CR mshinwell: Maybe we should think about this some more *)
    let handlers : Flambda.Let_cont_handlers.t =
      Nonrecursive {
        name;
        handler = {
          handler with
          handler = lift ~importer handler.handler;
        }
      }
    in
    let body = lift ~importer body in
    Flambda.Expr.Let_cont { body; handlers; }, state
  | Let_cont { body; handlers = Recursive handlers; }
      when Continuation.Map.exists
        (fun _ (handler : Flambda.Continuation_handler.t) ->
          handler.is_exn_handler)
        handlers ->
    let handlers : Flambda.Let_cont_handlers.t =
      Recursive (Continuation.Map.map (
          fun (handler : Flambda.Continuation_handler.t)
                  : Flambda.Continuation_handler.t ->
            { handler with
              handler = lift ~importer handler.handler;
            })
        handlers)
    in
    let body = lift ~importer body in
    Flambda.Expr.Let_cont { body; handlers; }, state
  | Let_cont { body; handlers; } ->
    let recursive = match handlers with
      | Nonrecursive _ -> Asttypes.Nonrecursive
      | Recursive _ -> Asttypes.Recursive
    in
    let handlers = Flambda.Let_cont_handlers.to_continuation_map handlers in
    lift_let_cont ~importer ~body ~handlers ~state ~recursive
  | Apply _ | Apply_cont _ | Switch _ | Invalid _ -> expr, state

and lift_set_of_closures ~importer
      (set_of_closures : Flambda.Set_of_closures.t) =
  let funs =
    Closure_id.Map.map (fun
            (function_decl : Flambda.Function_declaration.t) ->
        Flambda.Function_declaration.update_body function_decl
          ~body:(lift ~importer function_decl.body))
      set_of_closures.function_decls.funs
  in
  let function_decls =
    Flambda.Function_declarations.update
      set_of_closures.function_decls ~funs
  in
  Flambda.Set_of_closures.create ~function_decls
    ~free_vars:set_of_closures.free_vars
    ~direct_call_surrogates:set_of_closures.direct_call_surrogates

and lift ~importer (expr : Flambda.Expr.t) =
  let state =
    State.create ~variables_to_remain:[]
      ~continuations_to_remain:Continuation.Set.empty
  in
  let expr, state = lift_expr ~importer expr ~state in
  let expr =
    bind_things_to_remain ~rev_things:(State.rev_to_remain state) ~around:expr
  in
  let expr =
    List.fold_left (fun body handlers : Flambda.Expr.t ->
        Let_cont { body; handlers; })
      expr
      (State.rev_to_be_lifted state)
  in
  let constants, subst =
    List.fold_left (fun (constants, subst) (var, (const : Flambda.Named.t)) ->
        let const : Constant_or_symbol.t =
          match const with
          | Const const -> Constant const
          | Symbol sym -> Symbol sym
          | _ -> Misc.fatal_error "Unexpected constant"
        in
        let new_var, constants =
          match Constant_or_symbol.Map.find const constants with
          | exception Not_found ->
          (* CR mshinwell: I've called everything "const" for the moment as
             otherwise it's confusing *)
            let var = Variable.create "const" in
            var, Constant_or_symbol.Map.add const var constants
          | var ->
            var, constants
        in
        constants, Variable.Map.add var new_var subst)
      (Constant_or_symbol.Map.empty, Variable.Map.empty)
      (State.constants state)
  in
  (* CR mshinwell: Do this substitution more efficiently *)
  let expr = Flambda.Expr.toplevel_substitution ~importer subst expr in
  Constant_or_symbol.Map.fold (fun (const : Constant_or_symbol.t) var expr ->
      let kind =
        match const with
        | Constant _ -> Flambda_kind.value Can_scan
        | Symbol _ -> Flambda_kind.value Must_scan
      in
      Flambda.Expr.create_let var kind (Constant_or_symbol.to_named const) expr)
    constants
    expr

let run ~importer program =
  Flambda_static.Program.Mappers.map_toplevel_exprs program
    ~f:(lift ~importer)
