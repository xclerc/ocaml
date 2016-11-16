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

  when <named> has only generative effects and x is not free in <body>.
*)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

type thing_to_lift =
  | Let of Variable.t * Flambda.named
  | Let_mutable of Mutable_variable.t * Variable.t * Lambda.value_kind
  | Let_cont of Continuation.t * Flambda.let_cont_handler
  | Terminator of Flambda.expr

module Node = struct
  type t =
    | Root
    | Variable of Variable.t
    | Mutable_variable of Mutable_variable.t
    | Continuation of Continuation.t
    | Terminator of int

  include Identifiable.Make (struct
    type nonrec t = t

    let compare t1 t2 =
      match t1, t2 with
      | Root, Root -> 0
      | Variable v1, Variable v2 -> Variable.compare v1 v2
      | Continuation c1, Continuation c2 -> Continuation.compare c1 c2
      | Mutable_variable m1, Mutable_variable m2 ->
        Mutable_variable.compare m1 m2
      | Terminator id1, Terminator id2 -> Pervasives.compare id1 id2
      | Root, _ -> (-1)
      | _, Root -> 1
      | Variable _, _ -> (-1)
      | _, Variable _ -> 1
      | Continuation _, _ -> (-1)
      | _, Continuation _ -> 1
      | Terminator _, _ -> (-1)
      | _, Terminator _ -> 1

    let equal t1 t2 =
      compare t1 t2 = 0

    let hash t =
      match t with
      | Root -> 0
      | Variable v -> Hashtbl.hash (1, Variable.hash v)
      | Mutable_variable v -> Hashtbl.hash (2, Mutable_variable.hash v)
      | Continuation c -> Hashtbl.hash (3, Continuation.hash c)
      | Terminator id -> Hashtbl.hash (4, id)

    let output _chan _t = Misc.fatal_error "not implemented"
    let print _ppf _t = Misc.fatal_error "not implemented"
  end)

  let set_of_variable_set vs =
    Variable.Set.fold (fun var depends_on ->
        Set.add (Variable var) depends_on)
      vs
      Set.empty

  let set_of_continuation_set vs =
    Continuation.Set.fold (fun cont depends_on ->
        Set.add (Continuation cont) depends_on)
      vs
      Set.empty

  let next_terminator_id = ref 0

  let of_thing (thing : thing_to_lift) =
    match thing with
    | Let (var, _) -> Variable var
    | Let_mutable (var, _, _) -> Mutable_variable var
    | Let_cont (cont, _) -> Continuation cont
    | Terminator _ ->
      let id = !next_terminator_id in
      incr next_terminator_id;
      Terminator id
end

let add_to_graph (graph, definitions) (thing : thing_to_lift) ~depends_on =
  let target_node = Node.of_thing thing in
  let depends_on =
    if Node.Set.is_empty depends_on then Node.Set.singleton Root
    else depends_on
  in
  let graph =
    Node.Set.fold (fun source_node graph ->
        let target_nodes =
          match Node.Map.find source_node graph with
          | exception Not_found -> Node.Set.empty
          | target_nodes -> target_nodes
        in
        Node.Map.add source_node (Node.Set.add target_node target_nodes)
          graph)
      depends_on
      graph
  in
  let definitions = Node.Map.add target_node thing definitions in
  graph, definitions

let topological_sort (graph, definitions) =
  let rec traverse_node node =
    let children = Node.Map.find node graph in
    let results =
      Node.Set.fold (fun child results ->
          (traverse_node child) :: results)
        children
        []
    in
    node :: List.concat results
  in
  match Node.Map.find Root graph with
  | exception Not_found -> Misc.fatal_error "Graph has no root node"
  | _ ->
    let results = traverse_node Root in
    let rec find_definitions results output =
      match results with
      | [(Node.Terminator _) as result] ->
        begin match Node.Map.find result definitions with
        | exception Not_found ->
          Misc.fatal_error "Missing Terminator definition"
        | Terminator expr -> output, expr
        | _ -> assert false
        end
      | [] -> Misc.fatal_error "Missing Terminator"
      | result::results ->
        match Node.Map.find result definitions with
        | exception Not_found ->
          (* This is ok; the input expression to this pass may not be
             closed. *)
          (* CR mshinwell: maybe we should tighten this up *)
          find_definitions results output
        | thing_to_lift ->
          find_definitions results (thing_to_lift :: output)
    in
    find_definitions results []

let rec build_graph_and_extract_constants expr =
  let rec build (expr : Flambda.expr) ~graph ~constants
        ~most_recent_computational_let =
    match expr with
    | Let { var; defining_expr; body; } ->
      begin match defining_expr with
      | Const _ | Symbol _ ->
        let constants = Variable.Map.add var defining_expr constants in
        build body ~graph ~constants ~most_recent_computational_let
      | Var _ | Prim _ | Assign _ | Read_mutable _ | Read_symbol_field _
      | Allocated_const _ | Set_of_closures _ | Project_closure _
      | Move_within_set_of_closures _ | Project_var _ | Proved_unreachable ->
        let fvs_defining_expr = Flambda.free_variables_named defining_expr in
        (* There are no free continuations in the defining expression of
           a let. *)
        let graph =
          add_to_graph graph (Let (var, defining_expr))
            ~depends_on:(Node.set_of_variable_set fvs_defining_expr)
        in
        build body ~graph ~constants
          ~most_recent_computational_let:(Node.Set.singleton (Variable var))
      end
    | Let_mutable { var; initial_value; contents_kind; body; } ->
      let graph =
        add_to_graph graph (Let_mutable (var, initial_value, contents_kind))
          ~depends_on:(Node.Set.singleton (Variable initial_value))
      in
      (* [Let_mutable] doesn't count as a computation. *)
      build body ~graph ~constants ~most_recent_computational_let
    | Let_cont { name; body; handler = (Alias alias_of) as handler; } ->
      let graph =
        add_to_graph graph (Let_cont (name, handler))
          ~depends_on:(Node.Set.singleton (Continuation alias_of))
      in
      build body ~graph ~constants ~most_recent_computational_let
    | Let_cont { name; body; handler =
        (Handler { params; recursive = _; handler; }) as whole_handler } ->
      let params = Variable.Set.of_list params in
      let handler, constants' = lift_returning_constants handler in
      let constants =
        let eq (named1 : Flambda.named) (named2 : Flambda.named) =
          match named1, named2 with
          | Const const1, Const const2 ->
            Flambda.compare_const const1 const2 = 0
          | Symbol sym1, Symbol sym2 ->
            Symbol.equal sym1 sym2
          | Symbol _, Const _ | Const _, Symbol _ -> false
          | _, _ -> assert false  (* see above *)
        in
        Variable.Map.disjoint_union constants constants' ~eq
      in
      let add_let_cont_handler_to_graph ~graph ~name ~params ~handler
            ~whole_handler =
        let fcs_handler =
          Continuation.Set.remove name (Flambda.free_continuations handler)
        in
        let fvs_handler =
          Node.set_of_variable_set (
            Variable.Set.diff (Flambda.free_variables handler) params)
        in
        let fcs_handler = Node.set_of_continuation_set fcs_handler in
        let depends_on = Node.Set.union fvs_handler fcs_handler in
        add_to_graph graph (Let_cont (name, whole_handler)) ~depends_on
      in
      (* Any handler that might be eligible for lifting out of the [Let_cont]
        must now be at the top of [handler]. *)
      let rec peel_handlers (handler : Flambda.expr) ~graph =
        match handler with
        | Let_cont { name = name2; body = body2;
            handler = (Alias alias_of) as handler; } ->
          let graph =
            add_to_graph graph (Let_cont (name2, handler))
              ~depends_on:(Node.Set.singleton (Continuation alias_of))
          in
          peel_handlers body2 ~graph
        | Let_cont { name = name2; body = body2; handler =
            (Handler { params = params2; handler = handler2; _ })
              as whole_handler2 } ->
          (* This nested handler may be lifted so long as it doesn't use any
            of the outer handler's parameters. *)
          if Variable.Set.is_empty (Variable.Set.inter params
            (Flambda.free_variables handler2))
          then begin
            let graph =
              add_let_cont_handler_to_graph ~graph ~name:name2
                ~params:(Variable.Set.of_list params2) ~handler:handler2
                ~whole_handler:whole_handler2
            in
            peel_handlers body2 ~graph
          end else begin
            (* There's nothing else eligible for lifting in this nested
              handler. *)
            graph, handler
          end
        | Let _ | Let_mutable _ | Apply _ | Apply_cont _ | Switch _ ->
          graph, handler
      in
      let graph, handler = peel_handlers handler ~graph in
      let graph =
        add_let_cont_handler_to_graph ~graph ~name ~params ~handler
          ~whole_handler
      in
      build body ~graph ~constants ~most_recent_computational_let
    | Apply _ | Apply_cont _ | Switch _ ->
      let graph =
        add_to_graph graph (Terminator expr)
          ~depends_on:most_recent_computational_let
      in
      graph, constants
  in
  build expr ~constants:Variable.Map.empty
    ~most_recent_computational_let:Node.Set.empty
    ~graph:(Node.Map.empty, Node.Map.empty)

and lift_returning_constants (expr : Flambda.t) =
  let graph, constants = build_graph_and_extract_constants expr in
  let rev_bindings, terminator = topological_sort graph in
  let expr =
    List.fold_left (fun body (thing : thing_to_lift) : Flambda.expr ->
        match thing with
        | Let (var, defining_expr) ->
          Flambda.create_let var defining_expr body
        | Let_mutable (var, initial_value, contents_kind) ->
          Let_mutable { var; initial_value; contents_kind; body; }
        | Let_cont (name, handler) ->
          Let_cont { name; body; handler; }
        | Terminator _ -> assert false)
      terminator
      rev_bindings
  in
  expr, constants

let lift (expr : Flambda.t) =
  let expr, constants = lift_returning_constants expr in
  Variable.Map.fold (fun var const expr ->
      Flambda.create_let var const expr)
    constants
    expr

let run program =
  Flambda_iterators.map_exprs_at_toplevel_of_program program ~f:lift
