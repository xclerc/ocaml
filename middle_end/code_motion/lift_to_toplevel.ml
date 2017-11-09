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

module K = Flambda_kind
module Program_body = Flambda_static.Program_body

let static_structure name ~params : Program_body.static_structure =
  let dbg = Debuginfo.none in
  let make_symbol index =
    let index =
      match index with
      | None -> ""
      | Some index -> Printf.sprintf " %d" index
    in
    let linkage_name =
      Linkage_name.create
        (Format.asprintf "lifted_%a%a%s" Continuation.print name index)
    in
    Symbol.create (Compilation_unit.get_current_exn ()) linkage_name
  in
  let arity = Flambda.Typed_parameter.List.arity ~importer params in
  let rec assign_symbols index params_with_kinds
        resulting_static_part resulting_bindings =
    (* Even when it looks like we could produce a single symbol with multiple
       fields (say when all of the parameters are of kind [Value] or
       [Naked_float]), we still produce multiple symbols, since unused
       definitions (e.g. arising as a result of unboxing) will then be cleared
       away by the straightforward "unused symbol" analysis rather than
       requiring something more complicated. *)
    match params with
    | [] -> (List.rev resulting_static_part), (List.rev resulting_bindings)
    | (param, (kind : K.t))::params_with_kinds ->
      let symbol = make_symbol (Some index) in
      let var = Flambda.Typed_parameter.var param in
      let static_part : Flambda_static.Static_part.t =
        match kind with
        | Value _ -> Block (Tag.Scannable.zero, Immutable, [var])
        | Naked_float -> Boxed_float (Var var)
        | Naked_int32 -> Boxed_int32 (Var var)
        | Naked_int64 -> Boxed_int64 (Var var)
        | Naked_nativeint -> Boxed_nativeint (Var var)
        | Naked_immediate -> Misc.fatal_errorf "Not yet implemented"
      in
      let prim : Flambda_primitive.t =
        let var = Simple.var var in
        match kind with
        | Value _ -> Unary (Block_load (0, Not_a_float, Immutable), var)
        | Naked_float -> Unary (Unbox_number Naked_float, var)
        | Naked_int32 -> Unary (Unbox_number Naked_int32, var)
        | Naked_int64 -> Unary (Unbox_number Naked_int64, var)
        | Naked_nativeint -> Unary (Unbox_number Naked_nativeint, var)
        | Naked_immediate -> Misc.fatal_errorf "Not yet implemented"
      in
      let binding : Flambda.Named.t = Prim (prim, dbg) in
      assign_symbols (index + 1) params_with_kinds
        ((symbol, static_part) :: resulting_static_part)
        ((var, kind, binding) :: resulting_bindings)
  in
  let params_with_kinds = List.combine params arity in
  let static_part, bindings = assign_symbols 0 params_with_kinds [] [] in
  params_with_kinds, static_part, bindings

type or_do_not_lift =
  | Lift of Flambda_static.Static_part.t
  | Do_not_lift

let rec lift ~importer (expr : Flambda.Expr.t) ~to_copy =
  match expr with
  | Let_cont ({ body; handlers = Nonrecursive { name; handler = ({
      params; handler; is_exn_handler; _ } as handler_record); }; })
      when (not is_exn_handler) ->
    let free_conts_body, lifted, body = lift ~importer body ~to_copy in
    let our_cont = Continuation.Set.singleton name in
    if Continuation.Set.is_empty free_conts_body then begin
      (* The continuation is unused; delete it. *)
      free_conts_body, lifted, body
    end else if Continuation.Set.equal free_conts_body our_cont then begin
      (* The body of this [Let_cont] can only return through [name], which
         means that [handler] postdominates [body].  As such we can cut off
         [body] and put it inside a [computation] whose continuation
         is [handler].
         We augment [to_copy] to ensure that the bindings of the variables
         currently serving as parameters to [handler] is/are restated at the
         top of each subsequent lifted expression. *)
      let arity = Flambda.Typed_parameter.List.arity ~importer params in
      let computed_values, static_structure, to_copy' =
        static_structure name ~params
      in
      let to_copy = to_copy' @ to_copy in
      let free_conts_handler, lifted', handler =
        lift ~importer handler ~to_copy
      in
      let computation : Program_body.computation =
        { expr = body;
          return_cont = name;
          computed_values;
        }
      in
      let defn : Flambda_static.definition =
        { computation = Some computation;
          static_structure;
        }
      in
      let lifted = lifted @ [symbol, defn, to_copy] @ lifted' in
      let expr = Flambda.Expr.bind ~bindings:to_copy' ~body:handler in
      free_conts_handler, lifted, expr
    end else begin
      let handlers : Flambda.Let_cont_handlers.t =
        Nonrecursive {
          name;
          handler = handler_record;
        };
      in
      let expr : Flambda.Expr.t =
        Let_cont {
          body;
          handlers;
        }
      in
      let free_conts =
        Continuation.Set.union
          (Continuation.Set.remove name free_conts_body)
          (Flambda.Expr.free_continuations handler_record.handler)
      in
      free_conts, lifted, expr
    end
  | Let { var; kind; defining_expr; body; _ } ->
    let static_part_or_do_not_lift =
      match kind with
      | Value _ ->
        begin match defining_expr with
        | Simple _ -> Do_not_lift
        | Prim _
        | Set_of_closures _
        | Assign _
        | Read_mutable _ ->
          Lift (Block (
            Tag.Scannable.zero, Immutable, [Dynamically_computed var]))
        end
      | Naked_float -> Boxed_float (Var var)
      | Naked_int32 -> Boxed_int32 (Var var)
      | Naked_int64 -> Boxed_int64 (Var var)
      | Naked_nativeint -> Boxed_nativeint (Var var)
      | Naked_immediate -> Misc.fatal_errorf "Not yet implemented"
    in
    begin match static_part_or_do_not_lift with
    | Do_not_lift ->
      (* This let-expression is not to be lifted, but instead restated at the
         top of each lifted expression. *)
      let to_copy = (var, kind, defining_expr)::to_copy in
      let free_conts, lifted, body = lift ~importer body ~to_copy in
      let body =
        if Variable.Set.mem var (Flambda.Expr.free_variables body) then
          Flambda.Expr.create_let var kind defining_expr body
        else
          body
      in
      free_conts, lifted, body
    | Lift static_part ->







    let var' = Variable.rename var in

    let symbol, sym_defining_expr =
        let symbol =
          Flambda_utils.make_variable_symbol var
        in
        symbol,
          Flambda.Named.Read_symbol_field {
            symbol;
            logical_field = 0;
          }
    in
    let to_copy = (var, kind, sym_defining_expr)::to_copy in
    let free_conts, lifted, body = lift ~importer body ~to_copy in
    let return_cont, return_arity, expr =
        let return_cont = Continuation.create () in
        let return_arity = [K.value Must_scan] in
        let expr : Flambda.Expr.t =
          Flambda.Expr.create_let var' kind defining_expr
            (Apply_cont (return_cont, None, [var']))
        in
        return_cont, return_arity, expr
    in
    let descr : IS.t =
      { expr;
        return_cont;
        return_arity;
      }
    in
    let lifted = (symbol, descr, to_copy) :: lifted in
    let body = Flambda.Expr.create_let var kind sym_defining_expr body in
    free_conts, lifted, body
  | Let_cont { body; handlers; } ->
    let free_conts_body, lifted, body = lift ~importer body ~to_copy in
    let expr : Flambda.Expr.t =
      Let_cont {
        body;
        handlers;
      }
    in
    let free_and_bound_conts_handlers =
      Flambda.Let_cont_handlers.free_and_bound_continuations handlers
    in
    let free_conts =
      Continuation.Set.diff
        (Continuation.Set.union free_conts_body
          free_and_bound_conts_handlers.free)
        free_and_bound_conts_handlers.bound
    in
    free_conts, lifted, expr
  | Let_mutable _ | Apply _ | Apply_cont _ | Switch _ | Invalid _ ->
    let free_conts = Flambda.Expr.free_continuations expr in
    free_conts, [], expr

(* CR-someday mshinwell: Try to avoid having a separate substitution phase
   (so long as it doesn't complicate the code too much; the function above
   is already quite tricky). *)
let introduce_symbols ~importer defn =
  let _free_conts, lifted, expr = lift ~importer expr ~to_copy:[] in
  let lifted =
    List.map (fun (symbol, defn, to_copy) ->
        let to_copy, subst =
          List.fold_left (fun (to_copy, subst)
                  (var, kind, defining_expr) ->
              let var' = Variable.rename var in
              let to_copy = (var', kind, defining_expr) :: to_copy in
              to_copy, Variable.Map.add var var' subst)
            ([], Variable.Map.empty)
            to_copy
        in
        let to_copy =
          List.map (fun (var, kind, defining_expr) ->
              let defining_expr =
                Flambda.Named.toplevel_substitution ~importer subst
                  defining_expr
              in
              var, kind, defining_expr)
            to_copy
        in
        let expr = Flambda.Expr.toplevel_substitution ~importer subst expr in
        let descr = { descr with expr; } in
        symbol, descr, to_copy)
      lifted
  in
  lifted, expr

let add_extracted lifted program_body =
  List.fold_left
    (fun acc (symbol, (defn : Flambda_static.Program_body.definition), to_copy)
        : Flambda_static.Program_body.t ->
      let computation =
        Misc.Stdlib.Option.map
          (fun (computation : Flambda_static.Program_body.computation) ->
            let expr =
              List.fold_left (fun expr (var, kind, defining_expr) ->
                  let fvs = Flambda.Expr.free_variables expr in
                  if Variable.Set.mem var fvs then
                    Flambda.Expr.create_let var kind defining_expr expr
                  else
                    expr)
                computation.expr
                to_copy
            in
            { computation with expr; })
          defn.computation
      in
      Define_symbol (symbol, { defn with computation; }, acc))
    program_body
    (List.rev lifted)

let rec lift_program_body ~importer (body : Flambda_static.Program_body.t)
      : Flambda_static.Program_body.t =
  match program with
  | Define_symbol (defn, body)
    let body = lift_program_body ~importer body in
    let introduced, defn = introduce_symbols ~importer defn in
    add_extracted introduced
      (Flambda_static.Program_body.Define_symbol (symbol, defn, body))
  | Define_symbol_rec (defn, body) ->
    let body = lift_program_body body in
    let introduced, defn = introduce_symbols defn in
    add_extracted introduced
      (Flambda_static.Program_body.Define_symbol (symbol, defn, body))
  | Root _ -> program

let lift ~importer (program : Flambda_static.Program.t) =
  { program with
    program_body =
      lift_program_body ~importer ~type_of_name program.program_body;
  }
