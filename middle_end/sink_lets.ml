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

module W = Flambda.With_free_variables

module State = struct
  type t = {
    to_sink_by_continuation :
      (Variable.t * Flambda.named W.t) Continuation.Map.t;
    to_sink : Variable.Set.t;
    candidates_to_sink_by_continuation : Variable.t Continuation.Map.t;
    candidates_to_sink : Variable.Set.t;
    
  }
end

let rec sink_expr (expr : Flambda.expr) ~state =
  match expr with
  | Let ({ var; defining_expr; body; } as let_expr) ->
    let body, state = sink_expr body ~state in
    let defining_expr, state =
      match defining_expr with
      | Set_of_closures set_of_closures ->
        let set_of_closures = sink_set_of_closures set_of_closures in
        let defining_expr : Flambda.named = Set_of_closures set_of_closures in
        Flambda.With_free_variables.of_named defining_expr, state
      | _ ->
        Flambda.With_free_variables.of_defining_expr_of_let let_expr, state
    in
    let state =
      let was_candidate, state = State.remove_candidate_to_sink state var in
      if was_candidate
        && Effect_analysis.only_generative_effects_named defining_expr
      then
        State.sink_let state var
      else
        let fvs =
          Variable.Set.union (Flambda.free_variables_named defining_expr)
            (Variable.Set.remove var (Flambda.free_variables body))
        in
        State.remove_candidates_to_sink state fvs
    in
    W.create_let_reusing_defining_expr var defining_expr body, state
  | Let_mutable _ (*{ var; initial_value; contents_kind; body; } *)->
    assert false
  | Let_cont { name; body; handler = (Alias _) as handler; } ->
    let body, state = sink_expr body ~state in
    Let_cont { name; body; handler; }, state
  | Let_cont { name; body; handler =
      Handler { params; recursive; handler; } } ->
    let params_set = Variable.Set.of_list params in
    let body, state = sink_expr body ~state in
    let handler, handler_state = sink_expr handler ~state:(State.create ()) in
    let state =
      State.add_candidates_to_sink_from_state state
        ~from:handler_state
        ~except:params_set
    in
    let state = State.add_to_sink_from_state state ~from:handler_state in
    let fvs_handler =
      Variable.Set.diff (Flambda.free_variables handler) params_set
    in
    let candidates_to_sink =
      match recursive with
      | Nonrecursive ->
        Variable.Set.diff fvs_handler (Flambda.free_variables body)
      | Recursive ->
        (* We don't sink bindings into recursive continuation handlers. *)
        Variable.Set.empty
    in
    let state =
      State.add_candidates_to_sink state
        ~continuation_handler_for:name
        ~candidates_to_sink
    in
    Let_cont { name; body; handler =
      Handler { params; recursive; handler; } }, state
  | Apply _ | Apply_cont _ | Switch _ -> expr, state

and sink_set_of_closures (set_of_closures : Flambda.set_of_closures) =
  let funs =
    Variable.Map.map (fun
            (function_decl : Flambda.function_declaration) ->
        Flambda.create_function_declaration
          ~params:function_decl.params
          ~continuation_param:function_decl.continuation_param
          ~body:(sink function_decl.body)
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

and sink (expr : Flambda.t) =
  let expr, state = sink_expr expr ~state:(State.create ()) in
  let rec sink (expr : Flambda.t) : Flambda.t =
    match expr with
    | Let ({ var; defining_expr; body; } as let_expr) ->
      let body = sink body in
      if State.should_sink_let state var then
        body (* The let is to be moved into a handler. *)
      else
        W.create_let_reusing_defining_expr var defining_expr body
    | Let_mutable { var; initial_value; contents_kind; body; } ->
      let body = sink body in
      Let_mutable { var; initial_value; contents_kind; body; }
    | Let_cont { name; body; handler = (Alias _) as handler; } ->
      let body = sink body in
      Let_cont { name; body; handler; }
    | Let_cont { name; body; handler =
        Handler { params; recursive; handler; } } ->
      let body = sink body in
      let handler =
        let handler = sink handler in
        match State.sunken_lets_for_handler state name with
        | None -> handler
        | Some bindings_rev ->
          List.fold_left (fun handler (var, defining_expr) ->
              W.create_let_reusing_defining_expr var defining_expr handler)
            handler
            bindings_rev
      in
      Let_cont { name; body; handler =
        Handler { params; recursive; handler; } }
    | Apply _ | Apply_cont _ | Switch _ -> expr
  in
  sink expr

let run program =
  Flambda_iterators.map_exprs_at_toplevel_of_program program ~f:sink
