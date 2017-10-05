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

module F0 = Flambda0

type apply = F0.apply
type apply_kind = F0.apply_kind
type assign = F0.assign

module Call_kind = F0.Call_kind
module Const = F0.Const
module Free_var = F0.Free_var
module Let = F0.Let
module Let_cont = F0.Let_cont
module Let_mutable = F0.Let_mutable
module Return_arity = F0.Return_arity
module Switch = F0.Switch
module Trap_action = F0.Trap_action
module Typed_parameter = F0.Typed_parameter
module With_free_variables = F0.With_free_variables

module Free_vars = struct
  include F0.Free_vars

  (* let clean_projections (t : Closure_id.t) = *)
  (*   Closure_id.Map.map (fun (free_var : Free_var.t) -> *)
  (*       match free_var.projection with *)
  (*       | None -> free_var *)
  (*       | Some projection -> *)
  (*         let from = Projection.projecting_from projection in *)
  (*         if Closure_id.Map.mem from t then free_var *)
  (*         else ({ free_var with projection = None; } : Free_var.t)) *)
  (*     t *)
end

module Reachable = struct
  type nonrec t =
    | Reachable of F0.Named.t
    | Non_terminating of F0.Named.t
    | Unreachable
end

module rec Expr : sig
  include module type of F0.Expr

  val equal : t -> t -> bool
  val make_closure_declaration
     : (id:Variable.t
    -> free_variable_kind:(Variable.t -> Flambda_kind.t)
    -> body:t
    -> params:Typed_parameter.t list
    -> continuation_param:Continuation.t
    (* CR mshinwell: update comment. *)
    -> stub:bool
    -> continuation:Continuation.t
    -> return_arity:Flambda0.Return_arity.t
    -> t) Flambda_type.with_importer
  val toplevel_substitution
     : (Variable.t Variable.Map.t
    -> t
    -> t) Flambda_type.with_importer
  val description_of_toplevel_node : t -> string
  val bind
     : bindings:(Variable.t * Flambda_kind.t * Named.t) list
    -> body:t
    -> t
  val all_defined_continuations_toplevel : t -> Continuation.Set.t
  val count_continuation_uses_toplevel : t -> int Continuation.Map.t
  type with_wrapper =
    | Unchanged of { handler : Continuation_handler.t; }
    | With_wrapper of {
        new_cont : Continuation.t;
        new_handler : Continuation_handler.t;
        wrapper_handler : Continuation_handler.t;
      }
  val build_let_cont_with_wrappers
     : body:t
    -> recursive:Asttypes.rec_flag
    -> with_wrappers:with_wrapper Continuation.Map.t
    -> t
  module Iterators : sig
    val iter : (t -> unit) -> (Named.t -> unit) -> t -> unit
    val iter_subexpressions : (t -> unit) -> (Named.t -> unit) -> t -> unit
    val iter_expr : (t -> unit) -> t -> unit
    val iter_named : (Named.t -> unit) -> t -> unit
    val iter_all_immutable_let_and_let_rec_bindings
       : t
      -> f:(Variable.t -> Named.t -> unit)
      -> unit
    val iter_sets_of_closures : (Set_of_closures.t -> unit) -> t -> unit
    val iter_lets
        : t
      -> for_defining_expr:(Variable.t -> Flambda_kind.t -> Named.t -> unit)
      -> for_last_body:(t -> unit)
      -> for_each_let:(t -> unit)
      -> unit
    module Toplevel_only : sig 
      val iter : (t -> unit) -> (Named.t -> unit) -> t -> unit
      val iter_all_immutable_let_and_let_rec_bindings
         : t
        -> f:(Variable.t -> Named.t -> unit)
        -> unit
    end
  end
  module Mappers : sig
    val map : (t -> t) -> (Named.t -> Named.t) -> t -> t
    val map_lets
       : t
      -> for_defining_expr:(Variable.t -> Flambda_kind.t -> Named.t -> Named.t)
      -> for_last_body:(t -> t)
      -> after_rebuild:(t -> t)
      -> t
    val map_subexpressions
       : (t -> t)
      -> (Variable.t -> Named.t -> Named.t)
      -> t
      -> t
    val map_expr : (t -> t) -> t -> t
    val map_named : (Named.t -> Named.t) -> t -> t
    val map_named_with_id : (Variable.t -> Named.t -> Named.t) -> t -> t
    val map_symbols : t -> f:(Symbol.t -> Symbol.t) -> t
    val map_sets_of_closures
       : t
      -> f:(Set_of_closures.t -> Set_of_closures.t)
      -> t
    val map_apply : t -> f:(apply -> apply) -> t
    val map_project_var_to_named_opt
       : t
      -> f:(Projection.Project_var.t -> Named.t option)
      -> t
    val map_all_immutable_let_and_let_rec_bindings
       : t
      -> f:(Variable.t -> Named.t -> Named.t)
      -> t
    module Toplevel_only : sig 
      val map : (t -> t) -> (Named.t -> Named.t) -> t -> t
      val map_expr : (t -> t) -> t -> t
      val map_named : (Named.t -> Named.t) -> t -> t
      val map_sets_of_closures
         : t
        -> f:(Set_of_closures.t -> Set_of_closures.t)
        -> t
    end
  end
  module Folders : sig
    val fold_lets_option
        : t
      -> init:'a
      -> for_defining_expr:(
          'a
        -> Variable.t
        -> Flambda_kind.t
        -> Named.t
        -> 'a
          * (Variable.t * Flambda_kind.t * Named.t) list
          * Variable.t
          * Flambda_kind.t
          * Reachable.t)
      -> for_last_body:('a -> t -> t * 'b)
      (* CR-someday mshinwell: consider making [filter_defining_expr]
        optional *)
      -> filter_defining_expr:(
          'b
        -> Variable.t
        -> Named.t
        -> Variable.Set.t
        -> 'b * Variable.t * (Named.t option))
      -> t * 'b
  end
end = struct
  include F0.Expr

  let rec equal t1 t2 =
    (* CR mshinwell: next comment may no longer be relevant? *)
    t1 == t2 || (* it is ok for the string case: if they are physically the same,
                   it is the same original branch *)
    match t1, t2 with
    | Apply a1 , Apply a2  ->
      a1.kind = a2.kind
        && Variable.equal a1.func a2.func
        && Misc.Stdlib.List.equal Variable.equal a1.args a2.args
    | Apply _, _ | _, Apply _ -> false
    | Let { var = var1; defining_expr = defining_expr1; body = body1; _ },
        Let { var = var2; defining_expr = defining_expr2; body = body2; _ } ->
      Variable.equal var1 var2 && Named.equal defining_expr1 defining_expr2
        && equal body1 body2
    | Let _, _ | _, Let _ -> false
    | Let_mutable {var = mv1; initial_value = v1; contents_kind = ck1; body = b1},
      Let_mutable {var = mv2; initial_value = v2; contents_kind = ck2; body = b2}
      ->
      Mutable_variable.equal mv1 mv2
        && Variable.equal v1 v2
        && ck1 = ck2
        && equal b1 b2
    | Let_mutable _, _ | _, Let_mutable _ -> false
    | Switch (a1, s1), Switch (a2, s2) ->
      Variable.equal a1 a2 && Switch.equal s1 s2
    | Switch _, _ | _, Switch _ -> false
    | Apply_cont (e1, trap1, a1), Apply_cont (e2, trap2, a2) ->
      Continuation.equal e1 e2 && Misc.Stdlib.List.equal Variable.equal a1 a2
        && Misc.Stdlib.Option.equal Trap_action.equal trap1 trap2
    | Apply_cont _, _ | _, Apply_cont _ -> false
    | Let_cont { body = body1; handlers = handlers1; },
        Let_cont { body = body2; handlers = handlers2; } ->
      equal body1 body2
        && Let_cont_handlers.equal handlers1 handlers2
    | Proved_unreachable, Proved_unreachable -> true
    | Proved_unreachable, _ | _, Proved_unreachable -> false

  let description_of_toplevel_node (expr : Expr.t) =
    match expr with
    | Let { var; _ } -> Format.asprintf "let %a" Variable.print var
    | Let_mutable _ -> "let_mutable"
    | Let_cont  _ -> "catch"
    | Apply _ -> "apply"
    | Apply_cont  _ -> "staticraise"
    | Switch _ -> "switch"
    | Proved_unreachable -> "unreachable"

  let bind ~bindings ~body =
    List.fold_left (fun expr (var, kind, var_def) ->
        Expr.create_let var kind var_def expr)
      body bindings

  type with_wrapper =
    | Unchanged of { handler : Continuation_handler.t; }
    | With_wrapper of {
        new_cont : Continuation.t;
        new_handler : Continuation_handler.t;
        wrapper_handler : Continuation_handler.t;
      }

  let build_let_cont_with_wrappers ~body ~(recursive : Asttypes.rec_flag)
        ~with_wrappers : Expr.t =
    match recursive with
    | Nonrecursive ->
      begin match Continuation.Map.bindings with_wrappers with
      | [cont, Unchanged { handler; }] ->
        Let_cont {
          body;
          handlers = Nonrecursive { name = cont; handler; };
        }
      | [cont, With_wrapper { new_cont; new_handler; wrapper_handler; }] ->
        Let_cont {
          body = Let_cont {
            body;
            handlers = Nonrecursive {
              name = cont;
              handler = wrapper_handler;
            };
          };
          handlers = Nonrecursive {
            name = new_cont;
            handler = new_handler;
          };
        }
      | _ -> assert false
      end
    | Recursive ->
      let handlers =
        Continuation.Map.fold
          (fun cont (with_wrapper : with_wrapper) handlers ->
            match with_wrapper with
            | Unchanged { handler; } ->
              Continuation.Map.add cont handler handlers
            | With_wrapper { new_cont; new_handler; wrapper_handler; } ->
              Continuation.Map.add new_cont new_handler
                (Continuation.Map.add cont wrapper_handler handlers))
          with_wrappers
          Continuation.Map.empty
      in
      Let_cont {
        body;
        handlers = Recursive handlers;
      }

  module Iterators = struct
    let iter_lets = F0.Expr.iter_lets

    let iter f f_named t = iter_general ~toplevel:false f f_named (Is_expr t)

    let iter_expr f t = iter f (fun _ -> ()) t

    let iter_named f_named t = iter (fun (_ : t) -> ()) f_named t

    let iter_subexpressions f f_named (t : t) =
      match t with
      | Apply _ | Apply_cont _ | Switch _ | Proved_unreachable -> ()
      | Let { defining_expr; body; _ } ->
        f_named defining_expr;
        f body
      | Let_mutable { body; _ } -> f body
      | Let_cont { body; handlers =
          Nonrecursive { handler = { handler; _ }; _ } } ->
        f body;
        f handler
      | Let_cont { body; handlers = Recursive handlers; } ->
        f body;
        Continuation.Map.iter
          (fun _cont ({ handler; _ } : Continuation_handler.t) -> f handler)
          handlers

    (* CR-soon mshinwell: Remove "let_rec" from this name (ditto for the
       toplevel-only variant) *)
    let iter_all_immutable_let_and_let_rec_bindings t ~f =
      iter_expr (function
          | Let { var; defining_expr; _ } -> f var defining_expr
          | _ -> ())
        t

    let iter_sets_of_closures f t =
      iter_named (function
          | Set_of_closures clos -> f clos
          | Var _ | Symbol _ | Const _ | Allocated_const _ | Read_mutable _
          | Assign _ | Read_symbol_field _ | Project_closure _
          | Move_within_set_of_closures _ | Project_var _ | Prim _ -> ())
        t

    module Toplevel_only = struct
      let iter f f_named t =
        iter_general ~toplevel:true f f_named (Is_expr t)

      let iter_all_immutable_let_and_let_rec_bindings t ~f =
        iter_general ~toplevel:true
          (function
            | Let { var; defining_expr; _ } -> f var defining_expr
            | _ -> ())
          (fun _ -> ())
          (Is_expr t)
    end
  end

  module Mappers = struct
    let map_lets = F0.Expr.map_lets

    let map_general ~toplevel f f_named tree =
      let rec aux (tree : t) =
        match tree with
        | Let _ ->
          map_lets tree ~for_defining_expr:aux_named ~for_last_body:aux
            ~after_rebuild:f
        | _ ->
          let exp : t =
            match tree with
            | Apply _ | Apply_cont _ | Switch _ | Proved_unreachable -> tree
            | Let _ -> assert false
            | Let_mutable mutable_let ->
              let new_body = aux mutable_let.body in
              if new_body == mutable_let.body then
                tree
              else
                Let_mutable { mutable_let with body = new_body }
            (* CR-soon mshinwell: There's too much code duplication here with
               [map_subexpressions]. *)
            | Let_cont { body; handlers; } ->
              let new_body = aux body in
              match handlers with
              | Nonrecursive { name; handler =
                  ({ handler = handler_expr; _ } as handler); } ->
                let new_handler_expr = aux handler_expr in
                if new_body == body && new_handler_expr == handler_expr then
                  tree
                else
                  Let_cont {
                    body = new_body;
                    handlers = Nonrecursive {
                      name;
                      handler = { handler with handler = new_handler_expr; }
                    };
                  }
              | Recursive handlers ->
                let something_changed = ref false in
                let candidate_handlers =
                  Continuation.Map.map
                    (fun (handler : Continuation_handler.t) ->
                      let new_handler = aux handler.handler in
                      if not (new_handler == handler.handler) then begin
                        something_changed := true
                      end;
                      { handler with handler = new_handler; })
                    handlers
                in
                if !something_changed || not (new_body == body) then
                  Let_cont {
                    body = new_body;
                    handlers = Recursive candidate_handlers;
                  }
                else
                  tree
          in
          f exp
      and aux_named (id : Variable.t) _kind (named : Named.t) =
        let named : Named.t =
          match named with
          | Var _ | Symbol _ | Const _ | Allocated_const _ | Read_mutable _
          | Assign _ | Project_closure _ | Move_within_set_of_closures _
          | Project_var _ | Prim _ | Read_symbol_field _ -> named
          | Set_of_closures ({ function_decls; free_vars;
              direct_call_surrogates }) ->
            if toplevel then named
            else begin
              let done_something = ref false in
              let funs =
                Closure_id.Map.map (fun (func_decl : Function_declaration.t) ->
                    let new_body = aux func_decl.body in
                    if new_body == func_decl.body then begin
                      func_decl
                    end else begin
                      done_something := true;
                      Function_declaration.update_body func_decl
                        ~body:new_body
                    end)
                  function_decls.funs
              in
              if not !done_something then
                named
              else
                let function_decls =
                  Function_declarations.update function_decls ~funs
                in
                let set_of_closures =
                  Set_of_closures.create ~function_decls ~free_vars
                    ~direct_call_surrogates
                in
                Set_of_closures set_of_closures
            end
        in
        f_named id named
      in
      aux tree

    let map f f_named t =
      map_general ~toplevel:false f (fun _ n -> f_named n) t

    let map_expr f t = map f (fun named -> named) t
    let map_named f_named t = map (fun t -> t) f_named t

    let map_named_with_id f_named t =
      map_general ~toplevel:false (fun t -> t) f_named t

    let map_subexpressions f f_named (tree : t) : t =
      match tree with
      | Apply _ | Apply_cont _ | Switch _ | Proved_unreachable -> tree
      | Let { var; kind; defining_expr; body; _ } ->
        let new_named = f_named var defining_expr in
        let new_body = f body in
        if new_named == defining_expr && new_body == body then
          tree
        else
          create_let var kind new_named new_body
      | Let_mutable mutable_let ->
        let new_body = f mutable_let.body in
        if new_body == mutable_let.body then
          tree
        else
          Let_mutable { mutable_let with body = new_body }
      | Let_cont { body; handlers; } ->
        let new_body = f body in
        match handlers with
        | Nonrecursive { name; handler =
            ({ handler = handler_expr; _ } as handler); } ->
          let new_handler_expr = f handler_expr in
          if new_body == body && new_handler_expr == handler_expr then
            tree
          else
            Let_cont {
              body = new_body;
              handlers = Nonrecursive {
                name;
                handler = { handler with handler = new_handler_expr; }
              };
            }
        | Recursive handlers ->
          let something_changed = ref false in
          let candidate_handlers =
            Continuation.Map.map
              (fun (handler : Continuation_handler.t) ->
                let new_handler = f handler.handler in
                if not (new_handler == handler.handler) then begin
                  something_changed := true
                end;
                { handler with handler = new_handler; })
              handlers
          in
          if !something_changed || not (new_body == body) then
            Let_cont {
              body = new_body;
              handlers = Recursive candidate_handlers;
            }
          else
            tree

    let map_symbols tree ~f =
      map_named (function
          | (Symbol sym) as named ->
            let new_sym = f sym in
            if new_sym == sym then
              named
            else
              Symbol new_sym
          | ((Read_symbol_field (sym, field)) as named) ->
            let new_sym = f sym in
            if new_sym == sym then
              named
            else
              Read_symbol_field (new_sym, field)
          | (Var _ | Const _ | Allocated_const _ | Set_of_closures _
             | Read_mutable _ | Project_closure _
             | Move_within_set_of_closures _ | Project_var _ | Prim _
             | Assign _) as named -> named)
        tree

    let map_apply tree ~f =
      map (function
          | (Apply apply) as expr ->
            let new_apply = f apply in
            if new_apply == apply then
              expr
            else
              Apply new_apply
          | expr -> expr)
        (fun named -> named)
        tree

    let map_sets_of_closures tree ~f =
      map_named (function
          | (Set_of_closures set_of_closures) as named ->
            let new_set_of_closures = f set_of_closures in
            if new_set_of_closures == set_of_closures then named
            else Set_of_closures new_set_of_closures
          | (Var _ | Symbol _ | Const _ | Allocated_const _ | Project_closure _
          | Move_within_set_of_closures _ | Project_var _ | Assign _
          | Prim _ | Read_mutable _ | Read_symbol_field _) as named -> named)
        tree

    let map_project_var_to_named_opt tree ~f =
      map_named (function
          | (Project_var project_var) as named ->
            begin match f project_var with
            | None -> named
            | Some named -> named
            end
          | (Var _ | Symbol _ | Const _ | Allocated_const _ | Set_of_closures _
          | Project_closure _ | Move_within_set_of_closures _ | Prim _
          | Read_mutable _ | Read_symbol_field _ | Assign _) as named -> named)
        tree

    (* CR mshinwell: duplicate function *)
    let map_all_immutable_let_and_let_rec_bindings (expr : t)
          ~(f : Variable.t -> Named.t -> Named.t) : t =
      map_named_with_id f expr

    module Toplevel_only = struct
      let map f f_named t =
        map_general ~toplevel:true f (fun _ n -> f_named n) t

      let map_expr f_expr t = map f_expr (fun named -> named) t
      let map_named f_named t = map (fun t -> t) f_named t

      let map_sets_of_closures tree ~f =
        map_named (function
            | (Set_of_closures set_of_closures) as named ->
              let new_set_of_closures = f set_of_closures in
              if new_set_of_closures == set_of_closures then named
              else Set_of_closures new_set_of_closures
            | (Var _ | Symbol _ | Const _ | Allocated_const _ | Read_mutable _
            | Read_symbol_field _ | Project_closure _
            | Move_within_set_of_closures _ | Project_var _ | Prim _
            | Assign _) as named -> named)
          tree
      end
  end

  module Folders = struct
    let fold_lets_option (t : t) ~init ~for_defining_expr
          ~for_last_body ~filter_defining_expr =
      let finish ~last_body ~acc ~rev_lets =
        let module W = With_free_variables in
        let acc, t =
          List.fold_left (fun (acc, t) (var, kind, defining_expr) ->
              let free_vars_of_body = W.free_variables t in
              let acc, var, defining_expr =
                filter_defining_expr acc var defining_expr free_vars_of_body
              in
              match defining_expr with
              | None ->
                acc, t
              | Some defining_expr ->
                let let_expr =
                  W.create_let_reusing_body var kind defining_expr t
                in
                acc, W.of_expr let_expr)
            (acc, W.of_expr last_body)
            rev_lets
        in
        W.contents t, acc
      in
      let rec loop (t : t) ~acc ~rev_lets =
        match t with
        | Let { var; kind; defining_expr; body; _ } ->
          let acc, bindings, var, kind, (defining_expr : Reachable.t) =
            for_defining_expr acc var kind defining_expr
          in
          begin match defining_expr with
          | Reachable defining_expr ->
            let rev_lets =
              (var, kind, defining_expr) :: (List.rev bindings) @ rev_lets
            in
            loop body ~acc ~rev_lets
          | Non_terminating defining_expr ->
            let rev_lets =
              (var, kind, defining_expr) :: (List.rev bindings) @ rev_lets
            in
            let last_body, acc = for_last_body acc Proved_unreachable in
            finish ~last_body ~acc ~rev_lets
          | Unreachable ->
            let rev_lets = (List.rev bindings) @ rev_lets in
            let last_body, acc = for_last_body acc Proved_unreachable in
            finish ~last_body ~acc ~rev_lets
          end
        | t ->
          let last_body, acc = for_last_body acc t in
          finish ~last_body ~acc ~rev_lets
      in
      loop t ~acc:init ~rev_lets:[]
  end

  (* CR-soon mshinwell: this should use the explicit ignore functions *)
  let toplevel_substitution ~importer sb tree =
    let sb' = sb in
    let sb v = try Variable.Map.find v sb with Not_found -> v in
    let substitute_type ty =
      Flambda_type.rename_variables ~importer ty ~f:(fun var -> sb var)
    in
    let substitute_params_list params =
      List.map (fun param ->
          Typed_parameter.map_type param ~f:(fun ty ->
            substitute_type ty))
        params
    in
    let substitute_args_list args =
      List.map (fun arg -> sb arg) args
    in
    let aux (expr : t) : t =
      (* Note that this does not have to traverse subexpressions; the call to
         [map_toplevel] below will deal with that. *)
      match expr with
      | Let_mutable mutable_let ->
        let initial_value = sb mutable_let.initial_value in
        Let_mutable { mutable_let with initial_value }
      | Apply { kind; func; args; continuation; call_kind; dbg; inline;
          specialise; } ->
        let kind : apply_kind =
          match kind with
          | Function -> Function
          | Method { kind; obj; } -> Method { kind; obj = sb obj; }
        in
        let func = sb func in
        let args = substitute_args_list args in
        Apply { kind; func; args; continuation; call_kind; dbg; inline;
          specialise; }
      | Switch (cond, sw) ->
        let cond = sb cond in
        Switch (cond, sw)
      | Apply_cont (cont, trap_action, args) ->
        let args = substitute_args_list args in
        Apply_cont (cont, trap_action, args)
      | Let _ | Proved_unreachable -> expr
      | Let_cont { body; handlers; } ->
        let f handlers =
          Continuation.Map.map (fun (handler : Continuation_handler.t)
                  : Continuation_handler.t ->
              { handler with
                params = substitute_params_list handler.params;
              })
            handlers
        in
        Let_cont {
          body;
          handlers = Let_cont_handlers.map handlers ~f;
        }
    in
    let aux_named (named : Named.t) : Named.t =
      match named with
      | Var var ->
        let var' = sb var in
        if var == var' then named
        else Var var'
      | Symbol _ | Const _ -> named
      | Allocated_const _ | Read_mutable _ -> named
      | Assign { being_assigned; new_value; } ->
        let new_value = sb new_value in
        Assign { being_assigned; new_value; }
      | Read_symbol_field _ -> named
      | Set_of_closures set_of_closures ->
        let function_decls =
          Function_declarations.map_parameter_types
            set_of_closures.function_decls
            ~f:(fun ty -> substitute_type ty)
        in
        let set_of_closures =
          Set_of_closures.create
            ~function_decls
            ~free_vars:
              (Var_within_closure.Map.map (fun (free_var : Free_var.t) ->
                  { free_var with var = sb free_var.var; })
                set_of_closures.free_vars)
            ~direct_call_surrogates:set_of_closures.direct_call_surrogates
        in
        Set_of_closures set_of_closures
      | Project_closure project_closure ->
        Project_closure {
          project_closure with
          set_of_closures = sb project_closure.set_of_closures;
        }
      | Move_within_set_of_closures move_within_set_of_closures ->
        Move_within_set_of_closures {
          move_within_set_of_closures with
          closure = sb move_within_set_of_closures.closure;
        }
      | Project_var project_var ->
        Project_var {
          project_var with
          closure = sb project_var.closure;
        }
      | Prim (prim, args, dbg) ->
        Prim (prim, List.map sb args, dbg)
    in
    if Variable.Map.is_empty sb' then tree
    else Mappers.Toplevel_only.map aux aux_named tree

  let make_closure_declaration ~importer ~id
        ~free_variable_kind ~body ~params ~continuation_param
        ~stub ~continuation ~return_arity : Expr.t =
    let my_closure = Variable.rename id in
    let closure_id = Closure_id.wrap id in
    let free_variables = Expr.free_variables body in
    let param_set = Typed_parameter.List.var_set params in
    if not (Variable.Set.subset param_set free_variables) then begin
      Misc.fatal_error "Expr.make_closure_declaration"
    end;
    let sb =
      Variable.Set.fold
        (fun id sb -> Variable.Map.add id (Variable.rename id) sb)
        free_variables Variable.Map.empty
    in
    (* CR-soon mshinwell: try to eliminate this [toplevel_substitution].  This
       function is only called from [Simplify], so we should be able
       to do something similar to what happens in [Inlining_transforms] now. *)
    let body = toplevel_substitution ~importer sb body in
    let vars_within_closure =
      Variable.Map.of_set Var_within_closure.wrap
        (Variable.Set.diff free_variables param_set)
    in
    let body =
      Variable.Map.fold (fun var var_within_closure body ->
        let new_var = Variable.Map.find var sb in
        let kind : Flambda_kind.t = free_variable_kind var in
        let projection : Named.t =
          Project_var {
            closure = my_closure;
            var = Closure_id.Map.singleton closure_id var_within_closure }
        in
        match kind with
        | Value _ ->
          Expr.create_let new_var kind projection body
        | _ ->
          let boxed_var = Variable.rename new_var in
          let unbox, boxed_kind = Flambda0.Named.unbox_value boxed_var kind in
          Expr.create_let boxed_var boxed_kind projection
            (Expr.create_let new_var kind unbox
               body))
        vars_within_closure body
    in
    let subst var = Variable.Map.find var sb in
    let subst_param param = Typed_parameter.map_var param ~f:subst in
    let function_declaration : Function_declaration.t =
      Function_declaration.create
        ~params:(List.map subst_param params)
        ~continuation_param ~return_arity ~body ~stub ~dbg:Debuginfo.none
        ~inline:Default_inline ~specialise:Default_specialise
        ~is_a_functor:false
        ~closure_origin:(Closure_origin.create closure_id)
        ~my_closure
    in
    (* Should be checked differently *)
    (* assert (Variable.Set.equal (Variable.Set.map subst free_variables) *)
    (*   function_declaration.free_variables); *)
    let free_vars, boxed_var =
      Variable.Map.fold (fun id var_within_closure (fv', boxed_vars) ->
        let var, boxed_vars =
          match (free_variable_kind id : Flambda_kind.t) with
          | Value _ ->
            id, boxed_vars
          | kind ->
            let boxed_var = Variable.rename id in
            let box, boxed_kind = Flambda0.Named.box_value id kind in
            boxed_var,
            (boxed_var, box, boxed_kind) :: boxed_vars
        in
        let free_var : Free_var.t =
          { var;
            projection = None;
          }
        in
        Var_within_closure.Map.add var_within_closure free_var fv',
        boxed_vars)
        vars_within_closure
        (Var_within_closure.Map.empty, [])
    in
    let compilation_unit = Compilation_unit.get_current_exn () in
    let set_of_closures_var =
      Variable.create "set_of_closures"
        ~current_compilation_unit:compilation_unit
    in
    let set_of_closures =
      let function_decls =
        Function_declarations.create
          ~funs:(Closure_id.Map.singleton closure_id function_declaration)
      in
      Set_of_closures.create ~function_decls ~free_vars
        ~direct_call_surrogates:Closure_id.Map.empty
    in
    let project_closure : Named.t =
      Project_closure {
          set_of_closures = set_of_closures_var;
          closure_id = Closure_id.Set.singleton closure_id;
        }
    in
    let project_closure_var =
      Variable.create "project_closure"
        ~current_compilation_unit:compilation_unit
    in
    let body =
      Expr.create_let set_of_closures_var
        (Flambda_kind.value Must_scan)
        (Set_of_closures set_of_closures)
        (Expr.create_let project_closure_var (Flambda_kind.value Must_scan)
           project_closure
           (Apply_cont (continuation, None, [project_closure_var])))
    in
    List.fold_left (fun body (boxed_var, box, boxed_kind) ->
      Expr.create_let boxed_var boxed_kind box body)
      body boxed_var

  let all_defined_continuations_toplevel expr =
    let defined_continuations = ref Continuation.Set.empty in
    Iterators.Toplevel_only.iter (fun (expr : t) ->
        match expr with
        | Let_cont { handlers; _ } ->
          let conts = Let_cont_handlers.bound_continuations handlers in
          defined_continuations :=
            Continuation.Set.union conts
              !defined_continuations
        | _ -> ())
      (fun _named -> ())
      expr;
    !defined_continuations

  let count_continuation_uses_toplevel (expr : t) =
    let counts = Continuation.Tbl.create 42 in
    let use cont =
      match Continuation.Tbl.find counts cont with
      | exception Not_found -> Continuation.Tbl.add counts cont 1
      | count -> Continuation.Tbl.replace counts cont (count + 1)
    in
    Iterators.Toplevel_only.iter (fun (expr : t) ->
        match expr with
        | Apply { continuation; _ } -> use continuation
        | Apply_cont (cont, None, _) -> use cont
        | Apply_cont (cont, Some (Push { exn_handler; _ }), _)
        | Apply_cont (cont, Some (Pop { exn_handler; _ }), _) ->
          use cont;
          use exn_handler
        | Switch (_, switch) ->
          List.iter (fun (_const, cont) -> use cont) switch.consts;
          begin match switch.failaction with
          | None -> ()
          | Some cont -> use cont
          end
        | Let _ | Let_mutable _ | Let_cont _ | Proved_unreachable -> ())
      (fun _named -> ())
      expr;
    Continuation.Tbl.to_map counts
end and Named : sig
  include module type of F0.Named

  val equal : t -> t -> bool
  val toplevel_substitution
     : (Variable.t Variable.Map.t
    -> t
    -> t) Flambda_type.with_importer
  val of_projection : Projection.t -> Debuginfo.t -> t
  module Iterators : sig
    val iter : (Expr.t -> unit) -> (t -> unit) -> t -> unit
    val iter_named : (t -> unit) -> t -> unit
    module Toplevel_only : sig
      val iter : (Expr.t -> unit) -> (t -> unit) -> t -> unit
    end
  end
end = struct
  include F0.Named

  (* CR mshinwell: Implement this properly. *)
  let toplevel_substitution ~importer sb (t : t) =
    let var = Variable.create "subst" in
    let cont = Continuation.create () in
    let expr : Expr.t =
      Expr.create_let var
        (Flambda_kind.value Must_scan (* arbitrary *)) t
        (Apply_cont (cont, None, []))
    in
    match Expr.toplevel_substitution ~importer sb expr with
    | Let let_expr -> let_expr.defining_expr
    | _ -> assert false

  let of_projection (projection : Projection.t) dbg : t =
    match projection with
    | Project_var project_var -> Project_var project_var
    | Project_closure project_closure -> Project_closure project_closure
    | Move_within_set_of_closures move -> Move_within_set_of_closures move
    | Prim (prim, vars) -> Prim (prim, vars, dbg)
    | Switch _ ->
      (* CR mshinwell: This is dubious -- check usage *)
      Misc.fatal_error "Unsupported"

  let equal _t1 _t2 = false
    (* CR mshinwell: Sort this out.  The latest problem is lack of
       equality on [Const.t] due to the [print_as_char] field. *)
(*
    match t1, t2 with
    | Var var1, Var var2 -> Variable.equal var1 var2
    | Var _, _ | _, Var _ -> false
    | Symbol s1 , Symbol s2  -> Symbol.equal s1 s2
    | Symbol _, _ | _, Symbol _ -> false
    | Const c1, Const c2 -> Const.equal c1 c2
    | Const _, _ | _, Const _ -> false
    | Allocated_const c1, Allocated_const c2 ->
      Allocated_const.compare c1 c2 = 0
    | Allocated_const _, _ | _, Allocated_const _ -> false
    | Read_mutable mv1, Read_mutable mv2 -> Mutable_variable.equal mv1 mv2
    | Read_mutable _, _ | _, Read_mutable _ -> false
    | Assign { being_assigned = being_assigned1; new_value = new_value1; },
      Assign { being_assigned = being_assigned2; new_value = new_value2; } ->
      Mutable_variable.equal being_assigned1 being_assigned2
        && Variable.equal new_value1 new_value2
    | Assign _, _ | _, Assign _ -> false
    | Read_symbol_field (s1, i1), Read_symbol_field (s2, i2) ->
      Symbol.equal s1 s2 && i1 = i2
    | Read_symbol_field _, _ | _, Read_symbol_field _ -> false
    | Set_of_closures s1, Set_of_closures s2 ->
      Set_of_closures.equal s1 s2
    | Set_of_closures _, _ | _, Set_of_closures _ -> false
    | Project_closure f1, Project_closure f2 ->
      Projection.Project_closure.equal f1 f2
    | Project_closure _, _ | _, Project_closure _ -> false
    | Project_var v1, Project_var v2 ->
      Variable.equal v1.closure v2.closure
        && Closure_id.Map.equal Var_within_closure.equal v1.var v2.var
    | Project_var _, _ | _, Project_var _ -> false
    | Move_within_set_of_closures m1, Move_within_set_of_closures m2 ->
      Projection.Move_within_set_of_closures.equal m1 m2
    | Move_within_set_of_closures _, _ | _, Move_within_set_of_closures _ ->
      false
    | Prim (p1, al1, _), Prim (p2, al2, _) ->
      p1 = p2 && Misc.Stdlib.List.equal Variable.equal al1 al2
*)

  module Iterators = struct
    let iter f f_named t =
      Expr.iter_general ~toplevel:false f f_named (Is_named t)

    let iter_named f_named t =
      Expr.iter_general ~toplevel:false (fun (_ : Expr.t) -> ()) f_named
        (Is_named t)

    module Toplevel_only = struct
      let iter f f_named t =
        Expr.iter_general ~toplevel:true f f_named (Is_named t)
    end
  end
end and Let_cont_handlers : sig
  include module type of F0.Let_cont_handlers

  val equal : t -> t -> bool
end = struct
  include Let_cont_handlers

  let equal t1 t2 =
    match t1, t2 with
    | Nonrecursive { name = name1; handler = handler1; },
        Nonrecursive { name = name2; handler = handler2; } ->
      Continuation.equal name1 name2
        && Continuation_handler.equal handler1 handler2
    | Recursive handlers1, Recursive handlers2 ->
      Continuation_handlers.equal handlers1 handlers2
    | _, _ -> false
end and Continuation_handler : sig
  include module type of F0.Continuation_handler

  val equal : t -> t -> bool
end = struct
  include Continuation_handler

  let equal _ _ = false
(* CR mshinwell: Can we remove this?  We don't have equality on types at
   the moment.  Maybe we need to write that.
        ({ params = params1; stub = stub1; handler = handler1; } : t)
        ({ params = params2; stub = stub2; handler = handler2; } : t) =
    Misc.Stdlib.List.compare Typed_parameter.compare params1 params2 = 0
      && (stub1 : bool) = stub2
      && Expr.equal handler1 handler2
*)
end and Continuation_handlers : sig
  include module type of F0.Continuation_handlers

  val equal : t -> t -> bool
end = struct
  include Continuation_handlers

  let equal t1 t2 =
    Continuation.Map.equal Continuation_handler.equal t1 t2
end and Set_of_closures : sig
  include module type of F0.Set_of_closures

  (* CR mshinwell: swap parameters and add "_exn" suffix or similar *)
  val find_free_variable : Var_within_closure.t -> t -> Variable.t

(*  val equal : t -> t -> bool *)

  module Mappers : sig
    val map_symbols : t -> f:(Symbol.t -> Symbol.t) -> t
    val map_function_bodies
       : ?ignore_stubs:unit
      -> t
      -> f:(Expr.t -> Expr.t)
      -> t
  end
  module Folders : sig
    val fold_function_decls_ignoring_stubs
       : t
      -> init:'a
      -> f:(closure_id:Closure_id.t
        -> function_decl:Function_declaration.t
        -> 'a
        -> 'a)
      -> 'a
  end
end = struct
  include F0.Set_of_closures

  let find_free_variable cv ({ free_vars } : t) =
    let free_var : Free_var.t =
      Var_within_closure.Map.find cv free_vars
    in
    free_var.var

(*
  let equal (t1 : t) (t2 : t) =
    Variable.Map.equal Function_declaration.equal
        t1.function_decls.funs t2.function_decls.funs
      && Variable.Map.equal Free_var.equal t1.free_vars t2.free_vars
*)

  module Mappers = struct
    let map_symbols ({ function_decls; free_vars; direct_call_surrogates; }
          as set_of_closures) ~f =
      let done_something = ref false in
      let funs =
        Closure_id.Map.map (fun (func_decl : Function_declaration.t) ->
            let body = Expr.Mappers.map_symbols func_decl.body ~f in
            if not (body == func_decl.body) then begin
              done_something := true;
            end;
            Function_declaration.update_body func_decl ~body)
          function_decls.funs
      in
      if not !done_something then
        set_of_closures
      else
        let function_decls =
          Function_declarations.update function_decls ~funs
        in
        create ~function_decls ~free_vars ~direct_call_surrogates

    let map_function_bodies ?ignore_stubs (set_of_closures : t) ~f =
      let done_something = ref false in
      let funs =
        Closure_id.Map.map (fun (function_decl : Function_declaration.t) ->
            let new_body =
              match ignore_stubs, function_decl.stub with
              | Some (), true -> function_decl.body
              | _, _ -> f function_decl.body
            in
            if new_body == function_decl.body then
              function_decl
            else begin
              done_something := true;
              Function_declaration.update_body function_decl
                ~body:new_body
            end)
          set_of_closures.function_decls.funs
      in
      if not !done_something then
        set_of_closures
      else
        let function_decls =
          Function_declarations.update set_of_closures.function_decls ~funs
        in
        create ~function_decls ~free_vars:set_of_closures.free_vars
          ~direct_call_surrogates:set_of_closures.direct_call_surrogates
  end

  module Folders = struct
    let fold_function_decls_ignoring_stubs (t : t) ~init ~f =
      Closure_id.Map.fold (fun closure_id function_decl acc ->
          f ~closure_id ~function_decl acc)
        t.function_decls.funs
        init
  end
end and Function_declarations : sig
  include module type of F0.Function_declarations

  val find_declaration_variable : Closure_id.t -> t -> Variable.t
  val variables_bound_by_the_closure : Closure_id.t -> t -> Variable.Set.t
  val fun_vars_referenced_in_decls
     : t
    -> backend:(module Backend_intf.S)
    -> Closure_id.Set.t Closure_id.Map.t
  val closures_required_by_entry_point
     : entry_point:Closure_id.t
    -> backend:(module Backend_intf.S)
    -> t
    -> Closure_id.Set.t
  val all_functions_parameters : t -> Variable.Set.t
  val all_free_symbols : t -> Symbol.Set.t
  val contains_stub : t -> bool
  val map_parameter_types : t -> f:(Flambda_type.t -> Flambda_type.t) -> t
end = struct
  include Function_declarations

  let fun_vars_referenced_in_decls (_function_decls : t) ~backend:_ =
(*
    let fun_vars = Variable.Map.keys function_decls.funs in
    let symbols_to_fun_vars =
      let module Backend = (val backend : Backend_intf.S) in
      Variable.Set.fold (fun fun_var symbols_to_fun_vars ->
          let closure_id = Closure_id.wrap fun_var in
          let symbol = Backend.closure_symbol closure_id in
          Symbol.Map.add symbol fun_var symbols_to_fun_vars)
        fun_vars
        Symbol.Map.empty
    in
    Variable.Map.map (fun (func_decl : Function_declaration.t) ->
        let from_symbols =
          Symbol.Set.fold (fun symbol fun_vars' ->
              match Symbol.Map.find symbol symbols_to_fun_vars with
              | exception Not_found -> fun_vars'
              | fun_var ->
                assert (Variable.Set.mem fun_var fun_vars);
                Variable.Set.add fun_var fun_vars')
            func_decl.free_symbols
            Variable.Set.empty
        in
        let from_variables =
          Variable.Set.inter func_decl.free_variables fun_vars
        in
        Variable.Set.union from_symbols from_variables)
      function_decls.funs
*)
    (* CR pchambart: this needs another way to do it *)
    assert false

  let closures_required_by_entry_point ~(entry_point : Closure_id.t) ~backend
      (function_decls : t) =
    let dependencies =
      fun_vars_referenced_in_decls function_decls ~backend
    in
    let set = ref Closure_id.Set.empty in
    let queue = Queue.create () in
    let add v =
      if not (Closure_id.Set.mem v !set) then begin
        set := Closure_id.Set.add v !set;
        Queue.push v queue
      end
    in
    add entry_point;
    while not (Queue.is_empty queue) do
      let closure_id = Queue.pop queue in
      match Closure_id.Map.find closure_id dependencies with
      | exception Not_found -> ()
      | fun_dependencies ->
        Closure_id.Set.iter (fun dep ->
            if Closure_id.Map.mem dep function_decls.funs then
              add dep)
          fun_dependencies
    done;
    !set

  let all_functions_parameters (function_decls : t) =
    Closure_id.Map.fold
      (fun _ ({ params } : Function_declaration.t) set ->
        Variable.Set.union set (Typed_parameter.List.var_set params))
      function_decls.funs Variable.Set.empty

  let all_free_symbols (function_decls : t) =
    Closure_id.Map.fold (fun _ (function_decl : Function_declaration.t) syms ->
        Symbol.Set.union syms function_decl.free_symbols)
      function_decls.funs Symbol.Set.empty

  let contains_stub (fun_decls : t) =
    let number_of_stub_functions =
      Closure_id.Map.cardinal
        (Closure_id.Map.filter (fun _ ({ stub } : Function_declaration.t) -> stub)
          fun_decls.funs)
    in
    number_of_stub_functions > 0

  let map_parameter_types t ~f =
    let funs =
      Closure_id.Map.map (fun (decl : Function_declaration.t) ->
          Function_declaration.map_parameter_types decl ~f)
        t.funs
    in
    update t ~funs
end and Function_declaration : sig
  include module type of F0.Function_declaration

  val function_arity : t -> int
  (* val num_variables_in_closure *)
  (*    : t *)
  (*   -> function_decls:Function_declarations.t *)
  (*   -> int *)
  val equal : t -> t -> bool
  val map_parameter_types : t -> f:(Flambda_type.t -> Flambda_type.t) -> t
end = struct
  include Function_declaration

  let function_arity t = List.length t.params

  (* Removed because useless now.
     This was used to evaluate the size increase of inlining the closure.
     As there is no additionnal projections inserted at the inlining point
     since this is now already part of the body of the function. *)
  (*
  let num_variables_in_closure t ~(function_decls : Function_declarations.t) =
    let functions = Closure_id.Map.keys function_decls.funs in
    let params = Typed_parameter.List.var_set t.params in
    let vars_in_closure =
      Variable.Set.diff (Variable.Set.diff t.free_variables params) functions
    in
    Variable.Set.cardinal vars_in_closure
  *)

  let equal _t1 _t2 =
    false  (* CR mshinwell: see above *)
(*
    (* CR mshinwell: Is this right? *)
    Misc.Stdlib.List.equal Typed_parameter.equal t1.params t2.params
      && Expr.equal t1.body t2.body
*)

  let map_parameter_types t ~f =
    let params =
      List.map (fun param -> Typed_parameter.map_type param ~f) t.params
    in
    Function_declaration.update_params t ~params
end
