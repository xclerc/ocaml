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

module State : sig
  type t

  val create : unit -> t

  val should_sink_let : t -> Variable.t -> bool

  val sunken_lets_for_handler
     : t
    -> Continuation.t
    -> (Variable.t * Flambda.named W.t) list

  val add_candidates_to_sink
     : t
    -> continuation_handler_for:Continuation.t
    -> candidates_to_sink:Variable.Set.t
    -> t

  val add_candidates_to_sink_from_state
     : t
    -> from:t
    -> except:Variable.Set.t
    -> t

  val remove_candidate_to_sink : t -> Variable.t -> Continuation.t option * t
  val remove_candidates_to_sink : t -> Variable.Set.t -> t

  val sink_let
     : t
    -> Variable.t
    -> sink_into:Continuation.t
    -> defining_expr:Flambda.named W.t
    -> t

  val add_to_sink_from_state : t -> from:t -> t
end = struct
  type t = {
    to_sink :
      (Variable.t * Flambda.named W.t) list Continuation.Map.t;
    variables_to_sink : Variable.Set.t;
    candidates_to_sink : Continuation.t Variable.Map.t;
  }

  let create () =
    { to_sink = Continuation.Map.empty;
      variables_to_sink = Variable.Set.empty;
      candidates_to_sink = Variable.Map.empty;
    }

  let should_sink_let t var =
    Variable.Set.mem var t.variables_to_sink

  let sunken_lets_for_handler t cont =
    match Continuation.Map.find cont t.to_sink with
    | exception Not_found -> []
    | to_sink -> to_sink

  let add_candidates_to_sink t ~continuation_handler_for ~candidates_to_sink =
    let candidates_to_sink =
      Variable.Set.fold (fun candidate candidates_to_sink ->
          assert (not (Variable.Map.mem candidate candidates_to_sink));
          Variable.Map.add candidate continuation_handler_for
            candidates_to_sink)
        candidates_to_sink
        t.candidates_to_sink
    in
    { t with
      candidates_to_sink;
    }

  let add_candidates_to_sink_from_state t ~from ~except =
    let candidates_to_sink =
      Variable.Map.filter (fun var _ ->
          not (Variable.Set.mem var except))
        from.candidates_to_sink
    in
    let candidates_to_sink =
      Variable.Map.disjoint_union candidates_to_sink t.candidates_to_sink
    in
    { t with
      candidates_to_sink;
    }

  let remove_candidate_to_sink t var =
    let sink_to =
      match Variable.Map.find var t.candidates_to_sink with
      | exception Not_found -> None
      | sink_to -> Some sink_to
    in
    let candidates_to_sink =
      Variable.Map.remove var t.candidates_to_sink
    in
    let t =
      { t with
        candidates_to_sink;
      }
    in
    sink_to, t

  let remove_candidates_to_sink t vars =
    let candidates_to_sink =
      Variable.Set.fold (fun var candidates_to_sink ->
          Variable.Map.remove var candidates_to_sink)
        vars
        t.candidates_to_sink
    in
    { t with
      candidates_to_sink;
    }

  let sink_let t var ~sink_into ~defining_expr =
    let to_sink =
      let to_sink =
        match Continuation.Map.find sink_into t.to_sink with
        | exception Not_found -> []
        | to_sink -> to_sink
      in
      Continuation.Map.add sink_into ((var, defining_expr) :: to_sink)
        t.to_sink
    in
    let variables_to_sink = Variable.Set.add var t.variables_to_sink in
    { t with
      to_sink;
      variables_to_sink;
    }

  let add_to_sink_from_state t ~from =
    let to_sink = Continuation.Map.disjoint_union t.to_sink from.to_sink in
    let variables_to_sink =
      Variable.Set.union t.variables_to_sink from.variables_to_sink
    in
    { t with
      to_sink;
      variables_to_sink;
    }
end

let rec sink_expr (expr : Flambda.expr) ~state : Flambda.expr * State.t =
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
      match was_candidate with
      | Some sink_into
          when Effect_analysis.only_generative_effects_named
            (W.to_named defining_expr) ->
        State.sink_let state var ~sink_into ~defining_expr
      | Some _ | None ->
        let fvs =
          Variable.Set.union (W.free_variables defining_expr)
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
    | Let ({ var; body; } as let_expr) ->
      let body = sink body in
      if State.should_sink_let state var then
        body (* The let is to be moved into a handler. *)
      else
        let defining_expr = W.of_defining_expr_of_let let_expr in
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
        let bindings = State.sunken_lets_for_handler state name in
        List.fold_left (fun handler (var, defining_expr) ->
            W.create_let_reusing_defining_expr var defining_expr handler)
          handler
          (List.rev bindings)
      in
      Let_cont { name; body; handler =
        Handler { params; recursive; handler; } }
    | Apply _ | Apply_cont _ | Switch _ -> expr
  in
  sink expr

let run program =
  Flambda_iterators.map_exprs_at_toplevel_of_program program ~f:sink
