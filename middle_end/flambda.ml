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

module Free_var = F0.Free_var

module Free_vars = struct
  include Identifiable.Alias (F0.Free_var)

  let clean_projections t =
    Variable.Map.map (fun (free_var : F0.Free_var.t) ->
        match free_var.projection with
        | None -> free_var
        | Some projection ->
          let from = Projection.projecting_from projection in
          if Variable.Map.mem from free_vars then
            free_var
          else
            ({ free_var with projection = None; } : F0.Free_var.t))
      t
end

module rec Expr : sig
  include module type of F0.Expr

  val equal : t -> t -> bool
  val make_closure_declaration
     : id:Variable.t
    -> body:t
    -> params:Parameter.t list
    -> continuation_param:Continuation.t
    -> stub:bool
    -> continuation:Continuation.t
    -> t
  val toplevel_substitution
     : Variable.t Variable.Map.t
    -> t
    -> t
  val substitute_read_symbol_field_for_variables
     : (Symbol.t * int option) Variable.Map.t
    -> t
    -> t
  val description_of_toplevel_node : t -> string
  val bind
     : bindings:(Variable.t * Flambda.Named.t) list
    -> body:t
    -> t
  module Reachable : sig
    type nonrec t =
      | Reachable of Flambda.Named.t
      | Non_terminating of Flambda.Named.t
      | Unreachable
  end
  val fold_lets_option
      : t
    -> init:'a
    -> for_defining_expr:(
        'a
      -> Variable.t
      -> Flambda.Named.t
      -> 'a
        * (Variable.t * Flambda.Function_declarations.t Flambda_type0.T.t
            * Flambda.Named.t) list
        * Variable.t
        * Flambda.Function_declarations.t Flambda_type0.T.t
        * Reachable.t)
    -> for_last_body:('a -> Flambda.t -> Flambda.t * 'b)
    -> filter_defining_expr:(
        'b
      -> Variable.t
      -> Flambda.Named.t
      -> Variable.Set.t
      -> 'b * Variable.t * (Flambda.Named.t option))
    -> t * 'b
  val map_lets
     : Flambda.Expr.t
    -> for_defining_expr:(Variable.t -> Flambda.Named.t -> Flambda.Named.t)
    -> after_rebuild:(Flambda.Expr.t -> Flambda.Expr.t)
    -> for_last_body:(Flambda.Expr.t -> Flambda.Expr.t)
    -> Flambda.Expr.t
  val all_defined_continuations_toplevel : t -> Continuation.Set.t
  val count_continuation_uses_toplevel : t -> int Continuation.Map.t
  type with_wrapper =
    | Unchanged of { handler : Flambda.Continuation_handler.t; }
    | With_wrapper of {
        new_cont : Continuation.t;
        new_handler : Flambda.Continuation_handler.t;
        wrapper_handler : Flambda.Continuation_handler.t;
      }
  val build_let_cont_with_wrappers
     : body:t
    -> recursive:Asttypes.rec_flag
    -> with_wrappers:with_wrapper Continuation.Map.t
    -> t
end = struct
  include F0.Expr

  (* CR-soon mshinwell: this should use the explicit ignore functions *)
  let toplevel_substitution sb tree =
    let sb' = sb in
    let sb v = try Variable.Map.find v sb with Not_found -> v in
    let sb_opt = function
      | None -> None
      | Some v -> Some (sb v)
    in
    let aux (flam : F0.Expr.t) : F0.Expr.t =
      match flam with
      | Let_mutable mutable_let ->
        let initial_value = sb mutable_let.initial_value in
        Let_mutable { mutable_let with initial_value }
      | Apply { kind; func; args; continuation; call_kind; dbg; inline;
          specialise; } ->
        let kind : F0.apply_kind =
          match kind with
          | Function -> Function
          | Method { kind; obj; } -> Method { kind; obj = sb obj; }
        in
        let func = sb func in
        let args = List.map sb args in
        Apply { kind; func; args; continuation; call_kind; dbg; inline;
          specialise; }
      | Switch (cond, sw) ->
        let cond = sb cond in
        Switch (cond, sw)
      | Apply_cont (static_exn, trap_action, args) ->
        let args = List.map sb args in
        Apply_cont (static_exn, trap_action, args)
      | Let _ | Proved_unreachable -> flam
      | Let_cont { body; handlers; } ->
        let f handlers =
          Continuation.Map.map (fun (handler : F0.Continuation_handler.t)
                  : F0.Continuation_handler.t ->
              { handler with
                specialised_args =
                  (Variable.Map.map (fun (spec_to : F0.specialised_to) ->
                      { spec_to with var = sb_opt spec_to.var; })
                    handler.specialised_args);
              })
            handlers
        in
        Let_cont {
          body;
          handlers = F0.map_let_cont_handlers ~handlers ~f;
        }
    in
    let aux_named (named : F0.Named.t) : F0.Named.t =
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
        let set_of_closures =
          F0.Set_of_closures.create
            ~function_decls:set_of_closures.function_decls
            ~free_vars:
              (Variable.Map.map (fun (free_var : F0.Free_var.t) ->
                  { free_var with var = sb free_var.var; })
                set_of_closures.free_vars)
            ~specialised_args:
              (Variable.Map.map (fun (spec_to : F0.specialised_to) ->
                  { spec_to with var = sb_opt spec_to.var; })
                set_of_closures.specialised_args)
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
    else Flambda_iterators.map_toplevel aux aux_named tree

  (* CR-soon mshinwell: This function should be tidied up. *)
  let substitute_read_symbol_field_for_variables
      (substitution : (Symbol.t * int option) Variable.Map.t)
      (expr : F0.Expr.t) =
    let bind var fresh_var (expr : F0.Expr.t) : F0.Expr.t =
      let symbol, path = Variable.Map.find var substitution in
      let make_named (path : int option) : F0.Named.t =
        match path with
        | None -> Symbol symbol
        | Some i -> Read_symbol_field (symbol, i)
      in
      F0.Expr.create_let fresh_var (make_named path) expr
    in
    let substitute_named bindings (named : F0.Named.t) : F0.Named.t =
      let sb to_substitute =
        try Variable.Map.find to_substitute bindings
        with Not_found -> to_substitute
      in
      let sb_opt = function
        | None -> None
        | Some v -> Some (sb v)
      in
      match named with
      | Var v when Variable.Map.mem v substitution -> Var (sb v)
  (*
        let fresh = Variable.rename v in
        Expr (bind v fresh (Var fresh))
  *)
      | Var _ -> named
      | Symbol _ | Const _ -> named
      | Allocated_const _ | Read_mutable _ -> named
      | Assign { being_assigned; new_value }
          when Variable.Map.mem new_value substitution ->
        Assign { being_assigned; new_value = sb new_value; }
  (*
        let fresh = Variable.rename new_value in
        bind new_value fresh (Assign { being_assigned; new_value = fresh })
  *)
      | Assign _ -> named
      | Read_symbol_field _ -> named
      | Set_of_closures set_of_closures ->
        let set_of_closures =
          F0.Set_of_closures.create
            ~function_decls:set_of_closures.function_decls
            ~free_vars:
              (Variable.Map.map (fun (free_var : F0.Free_var.t) ->
                  { free_var with var = sb free_var.var; })
                set_of_closures.free_vars)
            ~specialised_args:
              (Variable.Map.map (fun (spec_to : F0.specialised_to) ->
                  { spec_to with var = sb_opt spec_to.var; })
                set_of_closures.specialised_args)
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
    let make_var_subst var =
      if Variable.Map.mem var substitution then
        let fresh = Variable.rename var in
        fresh, (fun expr -> bind var fresh expr)
      else
        var, (fun x -> x)
    in
    let make_apply_kind_subst (func : F0.apply_kind) =
      match func with
      | Function -> F0.Function, (fun x -> x)
      | Method { kind; obj; } ->
        if Variable.Map.mem obj substitution then
          let fresh = Variable.rename obj in
          F0.Method { kind; obj = fresh; },
            (fun expr -> bind obj fresh expr)
        else
          F0.Method { kind; obj; }, (fun x -> x)
    in
    let f (expr:F0.Expr.t) : F0.Expr.t =
      match expr with
      | Let ({ var = v; defining_expr = named; _ } as let_expr) ->
        let to_substitute =
          Variable.Set.filter
            (fun v -> Variable.Map.mem v substitution)
            (F0.Named.free_variables named)
        in
        if Variable.Set.is_empty to_substitute then
          expr
        else
          let bindings =
            Variable.Map.of_set (fun var -> Variable.rename var) to_substitute
          in
          let named =
            substitute_named bindings named
          in
          let expr =
            let module W = F0.With_free_variables in
            W.create_let_reusing_body v named (W.of_body_of_let let_expr)
          in
          Variable.Map.fold (fun to_substitute fresh expr ->
              bind to_substitute fresh expr)
            bindings expr
      | Let_mutable let_mutable when
          Variable.Map.mem let_mutable.initial_value substitution ->
        let fresh = Variable.rename let_mutable.initial_value in
        bind let_mutable.initial_value fresh
          (Let_mutable { let_mutable with initial_value = fresh })
      | Let_mutable _ ->
        expr
      | Switch (cond, sw) when Variable.Map.mem cond substitution ->
        let fresh = Variable.rename cond in
        bind cond fresh (Switch (fresh, sw))
      | Switch _ ->
        expr
      | Apply_cont (exn, trap_action, args) ->
        let args, bind_args =
          List.split (List.map make_var_subst args)
        in
        List.fold_right (fun f expr -> f expr) bind_args @@
          F0.Apply_cont (exn, trap_action, args)
      | Apply { kind; func; args; continuation; call_kind; dbg; inline;
          specialise } ->
        let kind, bind_kind = make_apply_kind_subst kind in
        let func, bind_func = make_var_subst func in
        let args, bind_args =
          List.split (List.map make_var_subst args)
        in
        bind_kind @@
          bind_func @@
            List.fold_right (fun f expr -> f expr) bind_args @@
            F0.Apply
              { kind; func; args; continuation; call_kind; dbg; inline;
                specialise;
              }
      | Let_cont _ | Proved_unreachable ->
        (* No variables directly used in those expressions *)
        expr
    in
    Flambda_iterators.map_toplevel_expr f expr

  let equal t1 t2 =
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
      Variable.equal var1 var2 && same_named defining_expr1 defining_expr2
        && same body1 body2
    | Let _, _ | _, Let _ -> false
    | Let_mutable {var = mv1; initial_value = v1; contents_kind = ck1; body = b1},
      Let_mutable {var = mv2; initial_value = v2; contents_kind = ck2; body = b2}
      ->
      Mutable_variable.equal mv1 mv2
        && Variable.equal v1 v2
        && ck1 = ck2
        && same b1 b2
    | Let_mutable _, _ | _, Let_mutable _ -> false
    | Switch (a1, s1), Switch (a2, s2) ->
      Variable.equal a1 a2 && F0.Switch.equal s1 s2
    | Switch _, _ | _, Switch _ -> false
    | Apply_cont (e1, trap1, a1), Apply_cont (e2, trap2, a2) ->
      Continuation.equal e1 e2 && Misc.Stdlib.List.equal Variable.equal a1 a2
        && trap_action_equal trap1 trap2
    | Apply_cont _, _ | _, Apply_cont _ -> false
    | Let_cont { body = body1; handlers = handlers1; },
        Let_cont { body = body2; handlers = handlers2; } ->
      same body1 body2
        && same_let_cont_handlers handlers1 handlers2
    | Proved_unreachable, Proved_unreachable -> true
    | Proved_unreachable, _ | _, Proved_unreachable -> false

  let make_closure_declaration ~id ~body ~params ~continuation_param
        ~stub ~continuation : F0.Expr.t =
    let free_variables = F0.Expr.free_variables body in
    let param_set = Parameter.Set.vars params in
    if not (Variable.Set.subset param_set free_variables) then begin
      Misc.fatal_error "Flambda_utils.make_closure_declaration"
    end;
    let sb =
      Variable.Set.fold
        (fun id sb -> Variable.Map.add id (Variable.rename id) sb)
        free_variables Variable.Map.empty
    in
    (* CR-soon mshinwell: try to eliminate this [toplevel_substitution].  This
      function is only called from [Simplify], so we should be able
      to do something similar to what happens in [Inlining_transforms] now. *)
    let body = toplevel_substitution sb body in
    let subst id = Variable.Map.find id sb in
    let subst_param param = Parameter.map_var subst param in
    let function_declaration =
      F0.Function_declaration.create ~params:(List.map subst_param params)
        ~continuation_param ~return_arity:1 ~body ~stub ~dbg:Debuginfo.none
        ~inline:Default_inline ~specialise:Default_specialise ~is_a_functor:false
        ~closure_origin:(Closure_origin.create (Closure_id.wrap id))
    in
    assert (Variable.Set.equal (Variable.Set.map subst free_variables)
      function_declaration.free_variables);
    let free_vars =
      Variable.Map.fold (fun id id' fv' ->
          let free_var : F0.Free_var.t =
            { var = id;
              projection = None;
            }
          in
          Variable.Map.add id' free_var fv')
        (Variable.Map.filter
          (fun id _ -> not (Variable.Set.mem id param_set))
          sb)
        Variable.Map.empty
    in
    let compilation_unit = Compilation_unit.get_current_exn () in
    let set_of_closures_var =
      Variable.create "set_of_closures"
        ~current_compilation_unit:compilation_unit
    in
    let set_of_closures =
      let function_decls =
        F0.Function_declarations.create
          ~funs:(Variable.Map.singleton id function_declaration)
      in
      F0.Set_of_closures.create ~function_decls ~free_vars
        ~specialised_args:Variable.Map.empty
        ~direct_call_surrogates:Variable.Map.empty
    in
    let project_closure : F0.Named.t =
      Project_closure {
          set_of_closures = set_of_closures_var;
          closure_id = Closure_id.Set.singleton (Closure_id.wrap id);
        }
    in
    let project_closure_var =
      Variable.create "project_closure"
        ~current_compilation_unit:compilation_unit
    in
    F0.Expr.create_let set_of_closures_var (Set_of_closures set_of_closures)
      (F0.Expr.create_let project_closure_var project_closure
        (Apply_cont (continuation, None, [project_closure_var])))

  module Reachable = struct
    type t =
      | Reachable of Named.t
      | Non_terminating of Named.t
      | Unreachable
  end

  let map_lets t ~for_defining_expr ~for_last_body ~after_rebuild =
    let rec loop (t : t) ~rev_lets =
      match t with
      | Let { var; defining_expr; body; _ } ->
        let new_defining_expr =
          for_defining_expr var defining_expr
        in
        let original =
          if new_defining_expr == defining_expr then
            Some t
          else
            None
        in
        let rev_lets = (var, new_defining_expr, original) :: rev_lets in
        loop body ~rev_lets
      | t ->
        let last_body = for_last_body t in
        (* As soon as we see a change, we have to rebuild that [Let] and every
          outer one. *)
        let seen_change = ref (not (last_body == t)) in
        List.fold_left (fun t (var, defining_expr, original) ->
            let let_expr =
              match original with
              | Some original when not !seen_change -> original
              | Some _ | None ->
                seen_change := true;
                create_let var defining_expr t
            in
            let new_let = after_rebuild let_expr in
            if not (new_let == let_expr) then begin
              seen_change := true
            end;
            new_let)
          last_body
          rev_lets
    in
    loop t ~rev_lets:[]

  let fold_lets_option (t : F0.Expr.t) ~init ~for_defining_expr
        ~for_last_body ~filter_defining_expr =
    let finish ~last_body ~acc ~rev_lets =
      let module W = With_free_variables in
      let acc, t =
        List.fold_left (fun (acc, t) (var, ty, defining_expr) ->
            let free_vars_of_body = W.free_variables t in
            let acc, var, defining_expr =
              filter_defining_expr acc var defining_expr free_vars_of_body
            in
            match defining_expr with
            | None ->
              acc, t
            | Some defining_expr ->
              let let_expr =
                W.create_let_reusing_body var ty defining_expr t
              in
              acc, W.of_expr let_expr)
          (acc, W.of_expr last_body)
          rev_lets
      in
      W.contents t, acc
    in
    let rec loop (t : t) ~acc ~rev_lets =
      match t with
      | Let { var; defining_expr; body; _ } ->
        let acc, bindings, var, ty, (defining_expr : named_reachable) =
          for_defining_expr acc var ty defining_expr
        in
        begin match defining_expr with
        | Reachable defining_expr ->
          let rev_lets =
            (var, ty, defining_expr) :: (List.rev bindings) @ rev_lets
          in
          loop body ~acc ~rev_lets
        | Non_terminating defining_expr ->
          let rev_lets =
            (var, ty, defining_expr) :: (List.rev bindings) @ rev_lets
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

  let description_of_toplevel_node (expr : F0.Expr.t) =
    match expr with
    | Let { var; _ } -> Format.asprintf "let %a" Variable.print var
    | Let_mutable _ -> "let_mutable"
    | Let_cont  _ -> "catch"
    | Apply _ -> "apply"
    | Apply_cont  _ -> "staticraise"
    | Switch _ -> "switch"
    | Proved_unreachable -> "unreachable"

  let bind ~bindings ~body =
    List.fold_left (fun expr (var, var_def) ->
        F0.Expr.create_let var var_def expr)
      body bindings

  let all_defined_continuations_toplevel expr =
    let defined_continuations = ref Continuation.Set.empty in
    Flambda_iterators.iter_toplevel (fun (expr : F0.Expr.t) ->
        match expr with
        | Let_cont { handlers; _ } ->
          let conts = F0.bound_continuations_of_let_handlers ~handlers in
          defined_continuations :=
            Continuation.Set.union conts
              !defined_continuations
        | _ -> ())
      (fun _named -> ())
      expr;
    !defined_continuations

  let count_continuation_uses_toplevel (expr : F0.Expr.t) =
    let counts = Continuation.Tbl.create 42 in
    let use cont =
      match Continuation.Tbl.find counts cont with
      | exception Not_found -> Continuation.Tbl.add counts cont 1
      | count -> Continuation.Tbl.replace counts cont (count + 1)
    in
    Flambda_iterators.iter_toplevel (fun (expr : F0.Expr.t) ->
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

  type with_wrapper =
    | Unchanged of { handler : Flambda.Continuation_handler.t; }
    | With_wrapper of {
        new_cont : Continuation.t;
        new_handler : Flambda.Continuation_handler.t;
        wrapper_handler : Flambda.Continuation_handler.t;
      }

  let build_let_cont_with_wrappers ~body ~(recursive : Asttypes.rec_flag)
        ~with_wrappers : Flambda.Expr.t =
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
end and Named : sig
  include module type of F0.Named

  val toplevel_substitution
     : Variable.t Variable.Map.t
    -> t
    -> t

  val of_projection : Projection.t -> t
end = struct
  include F0.Named

  (* CR-someday mshinwell: Fix [Flambda_iterators] so this can be implemented
     properly. *)
  let toplevel_substitution sb t =
    let var = Variable.create "subst" in
    let cont = Continuation.create () in
    let expr : F0.Expr.t =
      F0.Expr.create_let var t (Apply_cont (cont, None, []))
    in
    match Expr.toplevel_substitution sb expr with
    | Let let_expr -> let_expr.defining_expr
    | _ -> assert false

  let of_projection (projection : Projection.t) : t =
    match projection with
    | Project_var project_var -> Project_var project_var
    | Project_closure project_closure -> Project_closure project_closure
    | Move_within_set_of_closures move -> Move_within_set_of_closures move
    | Field (field_index, var) ->
      (* CR mshinwell: this should not say Debuginfo.none *)
      Prim (Pfield field_index, [var], Debuginfo.none)
    | Prim _ | Switch _ -> Misc.fatal_error "Unsupported"

  let equal t1 t2 =
    match t1, t2 with
    | Var var1, Var var2 -> Variable.equal var1 var2
    | Var _, _ | _, Var _ -> false
    | Symbol s1 , Symbol s2  -> Symbol.equal s1 s2
    | Symbol _, _ | _, Symbol _ -> false
    | Const c1, Const c2 -> compare_const c1 c2 = 0
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
    | Set_of_closures s1, Set_of_closures s2 -> same_set_of_closures s1 s2
    | Set_of_closures _, _ | _, Set_of_closures _ -> false
    | Project_closure f1, Project_closure f2 -> same_project_closure f1 f2
    | Project_closure _, _ | _, Project_closure _ -> false
    | Project_var v1, Project_var v2 ->
      Variable.equal v1.closure v2.closure
        && Closure_id.Map.equal Var_within_closure.equal v1.var v2.var
    | Project_var _, _ | _, Project_var _ -> false
    | Move_within_set_of_closures m1, Move_within_set_of_closures m2 ->
      same_move_within_set_of_closures m1 m2
    | Move_within_set_of_closures _, _ | _, Move_within_set_of_closures _ ->
      false
    | Prim (p1, al1, _), Prim (p2, al2, _) ->
      p1 = p2 && Misc.Stdlib.List.equal Variable.equal al1 al2
end and Let_cont_handlers : sig
  include module type of F0.Let_cont_handlers
end = struct
  include F0.Let_cont_handlers

  let equal t1 t2 =
    match t1, t2 with
    | Nonrecursive { name = name1; handler = handler1; },
        Nonrecursive { name = name2; handler = handler2; } ->
      Continuation.equal name1 name2
        && same_continuation_handler handler1 handler2
    | Recursive handlers1, Recursive handlers2 ->
      same_continuation_handlers handlers1 handlers2
    | _, _ -> false
end and Continuation_handler : sig
  include module type of F0.Continuation_handler
end = struct
  include F0.Continuation_handler

  let equal
        ({ params = params1; stub = stub1; handler = handler1; } : t)
        ({ params = params2; stub = stub2; handler = handler2; } : t) =
    F0.Typed_parameter.List.compare params1 params2 = 0
      && stub1 = stub2
      && Expr.equal handler1 handler2
end and Continuation_handlers : sig
  include module type of F0.Continuation_handlers
end = struct
  include F0.Continuation_handlers

  let equal t1 t2 =
    Continuation.Map.equal Continuation_handler.equal t1 t2
end and Set_of_closures : sig
  include module type of F0.Set_of_closures
end = struct
  include F0.Set_of_closures

  let find_free_variable cv ({ free_vars } : F0.Set_of_closures.t) =
    let free_var : F0.Free_var.t =
      Variable.Map.find (Var_within_closure.unwrap cv) free_vars
    in
    free_var.var

  and same_set_of_closures (c1 : F0.Set_of_closures.t)
        (c2 : F0.Set_of_closures.t) =
    Variable.Map.equal sameclosure c1.function_decls.funs c2.function_decls.funs
      && Variable.Map.equal F0.equal_free_var
          c1.free_vars c2.free_vars
      && Variable.Map.equal F0.equal_specialised_to c1.specialised_args
          c2.specialised_args
end and Function_declarations : sig
  include module type of F0.Function_declarations

  val find
     : Closure_id.t
    -> t
    -> Flambda0.Function_declaration.t
  val find_declaration_variable
     : Closure_id.t
    -> t
    -> Variable.t
  val variables_bound_by_the_closure
     : Closure_id.t
    -> t
    -> Variable.Set.t
  val fun_vars_referenced_in_decls
     : t
    -> backend:(module Backend_intf.S)
    -> Variable.Set.t Variable.Map.t
  val closures_required_by_entry_point
     : entry_point:Closure_id.t
    -> backend:(module Backend_intf.S)
    -> t
    -> Variable.Set.t
  val all_functions_parameters : t -> Variable.Set.t
  val all_free_symbols : t -> Symbol.Set.t
  val contains_stub : t -> bool
end = struct
  include F0.Function_declarations

  let find cf ({ funs } : t) =
    Variable.Map.find (Closure_id.unwrap cf) funs

  let find_declaration_variable cf ({ funs } : t) =
    let var = Closure_id.unwrap cf in
    if not (Variable.Map.mem var funs)
    then raise Not_found  (* CR mshinwell: think about this *)
    else var

  let variables_bound_by_the_closure cf
        (decls : F0.Function_declarations.t) =
    let func = find_declaration cf decls in
    let params = Parameter.Set.vars func.params in
    let functions = Variable.Map.keys decls.funs in
    Variable.Set.diff
      (Variable.Set.diff func.free_variables params)
      functions

  let fun_vars_referenced_in_decls (function_decls : t) ~backend =
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

  let closures_required_by_entry_point ~(entry_point : Closure_id.t) ~backend
      (function_decls : t) =
    let dependencies =
      fun_vars_referenced_in_decls function_decls ~backend
    in
    let set = ref Variable.Set.empty in
    let queue = Queue.create () in
    let add v =
      if not (Variable.Set.mem v !set) then begin
        set := Variable.Set.add v !set;
        Queue.push v queue
      end
    in
    add (Closure_id.unwrap entry_point);
    while not (Queue.is_empty queue) do
      let fun_var = Queue.pop queue in
      match Variable.Map.find fun_var dependencies with
      | exception Not_found -> ()
      | fun_dependencies ->
        Variable.Set.iter (fun dep ->
            if Variable.Map.mem dep function_decls.funs then
              add dep)
          fun_dependencies
    done;
    !set

  let all_functions_parameters (function_decls : t) =
    Variable.Map.fold
      (fun _ ({ params } : Function_declaration.t) set ->
        Variable.Set.union set (Parameter.Set.vars params))
      function_decls.funs Variable.Set.empty

  let all_free_symbols (function_decls : t) =
    Variable.Map.fold (fun _ (function_decl : Function_declaration.t) syms ->
        Symbol.Set.union syms function_decl.free_symbols)
      function_decls.funs Symbol.Set.empty

  let contains_stub (fun_decls : t) =
    let number_of_stub_functions =
      Variable.Map.cardinal
        (Variable.Map.filter (fun _ { F0.stub } -> stub)
          fun_decls.funs)
    in
    number_of_stub_functions > 0
end and Function_declaration : sig
  include module type of F0.Function_declaration

  val function_arity : t -> int
end = struct
  include F0.Function_declaration

  let function_arity t = List.length t.params

  let equal t1 t2 =
    Misc.Stdlib.List.equal Parameter.equal t1.params t2.params
      && Expr.equal t1.body t2.body
end
