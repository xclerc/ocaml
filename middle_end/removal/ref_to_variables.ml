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

let rename_var var =
  Mutable_variable.create
    (Variable.unique_name var)
  (* Variable.rename var *)
  (*   ~current_compilation_unit:(Compilation_unit.get_current_exn ()) *)

let variables_not_used_as_local_reference (tree:Flambda.Expr.t) =
  let set = ref Variable.Set.empty in
  let rec loop_named (flam : Flambda.Named.t) =
    match flam with
    | Var var ->
      set := Variable.Set.add var !set
    (* Directly used block: does not prevent use as a variable *)
    | Prim(Pfield _, [_], _)
    | Prim(Poffsetref _, [_], _) -> ()
    | Prim(Psetfield _, [_block; v], _) ->
      (* block is not prevented to be used as a local reference, but v is *)
      set := Variable.Set.add v !set
    | Prim(_, _, _)
    | Symbol _ |Const _ | Allocated_const _ | Read_mutable _
    | Field_of_symbol _ | Project_closure _
    | Move_within_set_of_closures _ | Project_var _ ->
      set := Variable.Set.union !set (Flambda.Named.free_variables flam)
    | Set_of_closures set_of_closures ->
      set := Variable.Set.union !set (Flambda.Named.free_variables flam);
      Closure_id.Map.iter
        (fun _ (function_decl : Flambda.Function_declaration.t) ->
          loop function_decl.body)
        set_of_closures.function_decls.funs
    | Assign _ ->
      set := Variable.Set.union !set (Flambda.Named.free_variables flam)
  and loop (flam : Flambda.Expr.t) =
    match flam with
    | Let { defining_expr; body; _ } ->
      loop_named defining_expr;
      loop body
    | Let_mutable { initial_value = v; body } ->
      set := Variable.Set.add v !set;
      loop body
    | Let_cont { body; handlers =
        Nonrecursive { name = _; handler = { handler; _ }; }; } ->
      loop body;
      loop handler
    | Let_cont { body; handlers = Recursive handlers; } ->
      loop body;
      Continuation.Map.iter (fun _cont
            (handler : Flambda.Continuation_handler.t) ->
          loop handler.handler)
        handlers
    | Apply _ | Apply_cont _ | Switch _ ->
      set := Variable.Set.union !set (Flambda.Expr.free_variables flam)
    | Invalid _ -> ()
  in
  loop tree;
  !set

let variables_containing_ref (flam:Flambda.Expr.t) =
  let map = ref Variable.Map.empty in
  let aux (flam : Flambda.Expr.t) =
    match flam with
    | Let { var;
            kind;
            defining_expr =
              Prim (Pmakeblock (0, Asttypes.Mutable, shape), l, _);
          } ->
      if not (Flambda_kind.is_value kind) then begin
        Misc.fatal_errorf "Variable %a bound to [Pmakeblock] but has kind \
            %a"
          Variable.print var
          Flambda_kind.print kind
      end;
      let arity =
        Flambda_arity.of_block_shape shape ~num_fields:(List.length l)
      in
      map := Variable.Map.add var arity !map
    | _ -> ()
  in
  Flambda.Expr.Iterators.iter aux (fun _ -> ()) flam;
  !map

let eliminate_ref_of_expr flam =
  let variables_not_used_as_local_reference =
    variables_not_used_as_local_reference flam
  in
  let convertible_variables =
    Variable.Map.filter (fun v _arity ->
        not (Variable.Set.mem v variables_not_used_as_local_reference))
      (variables_containing_ref flam)
  in
  if Variable.Map.cardinal convertible_variables = 0 then flam
  else
    let convertible_variables =
      Variable.Map.mapi (fun v arity ->
          Array.of_list (List.map (fun kind -> rename_var v, kind) arity))
        convertible_variables
    in
    let convertible_variable v = Variable.Map.mem v convertible_variables in
    let get_variable v field =
      let arr =
        try Variable.Map.find v convertible_variables
        with Not_found -> assert false
      in
      if Array.length arr <= field
      then None (* This case could apply when inlining code containing GADTs *)
      else Some (fst arr.(field), snd arr.(field), Array.length arr)
    in
    let aux_named var kind (named : Flambda.Named.t) =
      let module R = Flambda.Reachable in
      match named with
      | Prim (Pfield field, [v], _)
          when convertible_variable v ->
        begin match get_variable v field with
        | None -> (), [], var, kind, R.invalid ()
        | Some (var', kind', _size) ->
          assert (Flambda_kind.equal kind kind');
          (), [], var, kind, R.reachable (Read_mutable var')
        end
      | Prim (Poffsetref delta, [v], dbg)
          when convertible_variable v ->
        assert (Flambda_kind.is_value kind);
        begin match get_variable v 0 with
        | None -> (), [], var, kind, R.invalid ()
        | Some (var', kind', size) ->
          if size = 1
          then begin
            let mut = Variable.create "read_mutable" in
            let new_value = Variable.create "offseted" in
            let new_bindings = [
              mut, kind',
                Flambda.Named.Read_mutable var';
              new_value, kind',
                Flambda.Named.Prim (Poffsetint delta, [mut], dbg);
            ] in
            (), new_bindings, var, kind,
              R.reachable (Assign { being_assigned = var'; new_value; })
          end
          else
            (), [], var, kind, R.invalid ()
        end
      | Prim (Psetfield (field, _, _), [v; new_value], _)
          when convertible_variable v ->
        assert (Flambda_kind.is_value kind);
        begin match get_variable v field with
        | None -> (), [], var, kind, R.invalid ()
        | Some (being_assigned, _kind, _size) ->
          (), [], var, kind,
            R.reachable (Assign { being_assigned; new_value })
        end
      | Prim _ | Var _ | Symbol _ | Const _ | Allocated_const _ | Read_mutable _
      | Field_of_symbol _ | Set_of_closures _ | Project_closure _
      | Move_within_set_of_closures _ | Project_var _ | Assign _ ->
        (), [], var, kind, R.reachable named
    in
    let aux (flam : Flambda.Expr.t) : Flambda.Expr.t =
      match flam with
      | Let {
          var;
          kind;
          defining_expr = Prim (Pmakeblock (0, Asttypes.Mutable, shape), l, _);
          body;
        }
          when convertible_variable var ->
        if not (Flambda_kind.is_value kind) then begin
          Misc.fatal_errorf "Variable %a bound to [Pmakeblock] but has kind \
              %a"
            Variable.print var
            Flambda_kind.print kind
        end;
        let arity =
          Flambda_arity.of_block_shape shape ~num_fields:(List.length l)
        in
        let _, expr =
          List.fold_left2 (fun (field, body) initial_value kind ->
              match get_variable var field with
              | None -> assert false
              | Some (field_var, _kind, _size) ->
                field + 1,
                  (Let_mutable {
                    var = field_var;
                    initial_value;
                    body;
                    contents_type = Flambda_type.unknown kind Other;
                  } : Flambda.Expr.t))
            (0, body) l arity in
        expr
      | Let _ ->
        let flam, () =
          Flambda.Expr.Folders.fold_lets_option flam
            ~init:()
            ~for_defining_expr:(fun () var kind named ->
              aux_named var kind named)
            ~for_last_body:(fun () expr -> expr, ())
            ~filter_defining_expr:(fun () var named _ ->
              (), var, Some named)
        in
        flam
      | Let_mutable _ | Apply _ | Switch _
      | Apply_cont _ | Let_cont _ | Invalid _ -> flam
    in
    Flambda.Expr.Mappers.map_expr aux flam

let eliminate_ref (program:Flambda_static.Program.t) =
  Flambda_static.Program.Mappers.map_toplevel_exprs program
    ~f:eliminate_ref_of_expr
