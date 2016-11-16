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
  type name =
    | Root
    | Variable of Variable.t
    | Mutable_variable of Mutable_variable.t
    | Continuation of Continuation.t
    | Terminator of int

  type t = {
    name : name;
    mutable marked : bool;
  }

  include Identifiable.Make (struct
    type nonrec t = t

    let compare t1 t2 =
      match t1.name, t2.name with
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
      match t.name with
      | Root -> 0
      | Variable v -> Hashtbl.hash (1, Variable.hash v)
      | Mutable_variable v -> Hashtbl.hash (2, Mutable_variable.hash v)
      | Continuation c -> Hashtbl.hash (3, Continuation.hash c)
      | Terminator id -> Hashtbl.hash (4, id)

    let output _chan _t = Misc.fatal_error "not implemented"

    let print ppf t =
      match t.name with
      | Root -> Format.fprintf ppf "Root"
      | Variable var -> Variable.print ppf var
      | Mutable_variable var -> Mutable_variable.print ppf var
      | Continuation cont -> Continuation.print ppf cont
      | Terminator id -> Format.fprintf ppf "Terminator-%d" id
  end)

  let create name =
    { name;
      marked = false;
    }

  let mark t =
    let already_marked = t.marked in
    t.marked <- true;
    already_marked

  let set_of_variable_set vs =
    Variable.Set.fold (fun var depends_on ->
        Set.add (create (Variable var)) depends_on)
      vs
      Set.empty

  let set_of_continuation_set vs =
    Continuation.Set.fold (fun cont depends_on ->
        Set.add (create (Continuation cont)) depends_on)
      vs
      Set.empty

  let next_terminator_id = ref 0

  let of_thing (thing : thing_to_lift) =
    let name =
      match thing with
      | Let (var, _) -> Variable var
      | Let_mutable (var, _, _) -> Mutable_variable var
      | Let_cont (cont, _) -> Continuation cont
      | Terminator _ ->
        let id = !next_terminator_id in
        incr next_terminator_id;
        Terminator id
    in
    create name
end

let add_to_graph (graph, definitions) (thing : thing_to_lift) ~depends_on =
  let target_node = Node.of_thing thing in
  let depends_on =
    if Node.Set.is_empty depends_on then Node.Set.singleton (Node.create Root)
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
  let definitions = Node.Map.add target_node (Some thing) definitions in
  graph, definitions

let add_free_things_to_graph graph target_nodes =
  Node.Set.fold (fun target_node (graph, definitions) ->
      let graph =
        let root = Node.create Root in
        let target_nodes =
          match Node.Map.find root graph with
          | exception Not_found -> Node.Set.empty
          | target_nodes -> target_nodes
        in
        Node.Map.add root (Node.Set.add target_node target_nodes) graph
      in
      let definitions = Node.Map.add target_node None definitions in
      graph, definitions)
    target_nodes
    graph

let print_graph graph =
  Format.eprintf "%a\n%!"
    (Node.Map.print Node.Set.print) graph

let topological_sort (graph, definitions) =
Format.eprintf "top sort:\n%!";
  print_graph graph;
  let rec traverse_node (node : Node.t) =
    let already_marked = Node.mark node in
    let children =
      if already_marked then
        Node.Set.empty
      else
        match node.name with
        | Terminator _ -> Node.Set.empty
        | _ ->
          match Node.Map.find node graph with
          | exception Not_found ->
            Misc.fatal_errorf "Node %a not found" Node.print node
          | children -> children
    in
    let results =
      Node.Set.fold (fun child results ->
          (traverse_node child) :: results)
        children
        []
    in
    node :: List.concat results
  in
  match Node.Map.find (Node.create Root) graph with
  | exception Not_found -> Misc.fatal_error "Graph has no root node"
  | _ ->
    let results = traverse_node (Node.create Root) in
    let rec find_definitions results output =
      match results with
      | [{ Node. name = Terminator _; _ } as result] ->
        begin match Node.Map.find result definitions with
        | exception Not_found ->
          Misc.fatal_error "Missing Terminator definition"
        | Some (Terminator expr) -> output, expr
        | _ -> assert false
        end
      | [] -> Misc.fatal_error "Missing Terminator"
      | result::results ->
        match Node.Map.find result definitions with
        | exception Not_found ->
          Misc.fatal_errorf "No definition for %a" Node.print result
        | None ->
          find_definitions results output
        | Some thing_to_lift ->
          find_definitions results (thing_to_lift :: output)
    in
    find_definitions results []

let rec build_graph_and_extract_constants expr ~free =
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
        let defining_expr : Flambda.named =
          match defining_expr with
          | Set_of_closures set_of_closures ->
            let set_of_closures = lift_set_of_closures set_of_closures in
            Set_of_closures set_of_closures
          | _ -> defining_expr
        in
        let fvs_defining_expr = Flambda.free_variables_named defining_expr in
        (* There are no free continuations in the defining expression of
           a let. *)
        let graph =
          add_to_graph graph (Let (var, defining_expr))
            ~depends_on:(Node.set_of_variable_set fvs_defining_expr)
        in
        build body ~graph ~constants
          ~most_recent_computational_let:
            (Node.Set.singleton (Node.create (Variable var)))
      end
    | Let_mutable { var; initial_value; contents_kind; body; } ->
      let graph =
        add_to_graph graph (Let_mutable (var, initial_value, contents_kind))
          ~depends_on:
            (Node.Set.singleton (Node.create (Variable initial_value)))
      in
      (* [Let_mutable] doesn't count as a computation. *)
      build body ~graph ~constants ~most_recent_computational_let
    | Let_cont { name; body; handler = (Alias alias_of) as handler; } ->
      let graph =
        add_to_graph graph (Let_cont (name, handler))
          ~depends_on:
            (Node.Set.singleton (Node.create (Continuation alias_of)))
      in
      build body ~graph ~constants ~most_recent_computational_let
    | Let_cont { name; body; handler =
        (Handler { params; recursive; handler; }) as whole_handler } ->
      let params = Variable.Set.of_list params in
      let handler, constants' =
        let fcs =
          match recursive with
          | Nonrecursive -> Node.Set.empty
          | Recursive -> Node.Set.singleton (Node.create (Continuation name))
        in
        let fvs = Node.set_of_variable_set params in
        let free = Node.Set.union fcs fvs in
        lift_returning_constants handler ~free
      in
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
Format.eprintf "Continuation %a being added\n%!" Continuation.print name;
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
              ~depends_on:
                (Node.Set.singleton (Node.create (Continuation alias_of)))
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
Format.eprintf "Continuation %a being peeled\n%!" Continuation.print name2;
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
      let fvs = Node.set_of_variable_set (Flambda.free_variables expr) in
      let fcs =
        Node.set_of_continuation_set (Flambda.free_continuations expr)
      in
      let depends_on =
        Node.Set.union most_recent_computational_let
          (Node.Set.union fvs fcs)
      in
      let graph = add_to_graph graph (Terminator expr) ~depends_on in
      graph, constants
  in
  let empty_graph =
    Node.Map.add (Node.create Root) Node.Set.empty Node.Map.empty,
      Node.Map.empty
  in
  let graph = add_free_things_to_graph empty_graph free in
Format.eprintf "Initial graph:\n%!";
print_graph (fst graph);
  build expr ~constants:Variable.Map.empty
    ~most_recent_computational_let:Node.Set.empty
    ~graph

and lift_returning_constants (expr : Flambda.t) ~free =
  let graph, constants = build_graph_and_extract_constants expr ~free in
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

and lift_set_of_closures (set_of_closures : Flambda.set_of_closures) =
  let funs =
    Variable.Map.map (fun
            (function_decl : Flambda.function_declaration) ->
        let continuation_param =
          Node.create (Continuation function_decl.continuation_param)
        in
        let params =
          Node.set_of_variable_set
            (Variable.Set.of_list function_decl.params)
        in
        let free_variables =
          Node.set_of_variable_set function_decl.free_variables
        in
        let free =
          Node.Set.union (Node.Set.singleton continuation_param)
            (Node.Set.union params free_variables)
        in
        let body = lift function_decl.body ~free in
        Flambda.create_function_declaration
          ~params:function_decl.params
          ~continuation_param:function_decl.continuation_param
          ~body
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

and lift (expr : Flambda.t) ~free =
  let expr, constants = lift_returning_constants expr ~free in
  Variable.Map.fold (fun var const expr ->
      Flambda.create_let var const expr)
    constants
    expr

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
    let fields =
      List.map (fun (expr, cont) ->
          let free = Node.Set.singleton (Node.create (Continuation cont)) in
          lift expr ~free, cont)
        fields
    in
    Initialize_symbol (sym, tag, fields, lift_program_body body)
  | Effect (expr, cont, body) ->
    let free = Node.Set.singleton (Node.create (Continuation cont)) in
    let expr = lift expr ~free in
    Effect (expr, cont, lift_program_body body)
  | End _ -> body

let run (program : Flambda.program) =
  { program with
    program_body = lift_program_body program.program_body;
  }
