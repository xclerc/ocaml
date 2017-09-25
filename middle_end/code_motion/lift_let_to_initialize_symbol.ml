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

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

let should_copy (named : Flambda.Named.t) =
  match named with
  | Symbol _ | Read_symbol_field _ | Const _ -> true
  | _ -> false

let rec lift ~importer (expr : Flambda.Expr.t) ~to_copy =
  match expr with
  | Let_cont ({ body; handlers = Nonrecursive { name; handler = ({
      params = [param]; handler; is_exn_handler; _ } as handler_record); }; })
      when not is_exn_handler ->
    let free_conts_body, lifted, body = lift ~importer body ~to_copy in
    let our_cont = Continuation.Set.singleton name in
    if Continuation.Set.is_empty free_conts_body then begin
      (* The continuation is unused; delete it. *)
      free_conts_body, lifted, body
    end else if Continuation.Set.equal free_conts_body our_cont then begin
      (* The body of this [Let_cont] can only return through [name], which
         means that [handler] postdominates [body].  As such we can cut off
         [body] and put it inside an [Initialize_symbol] whose continuation
         is [handler].
         We also augment [to_copy] to ensure that the binding of the existing
         variable to the new symbol is restated at the top of each subsequent
         lifted expression. *)
      let param_var = Flambda.Typed_parameter.var param in
      let param_ty = Flambda.Typed_parameter.ty param in
      let param_kind = Flambda_type.kind ~importer param_ty in
      let symbol = Flambda_utils.make_variable_symbol param_var in
      let defining_expr : Flambda.Named.t = Read_symbol_field (symbol, 0) in
      let to_copy = (param_var, param_kind, defining_expr)::to_copy in
      let free_conts_handler, lifted', handler =
        lift ~importer handler ~to_copy
      in
      let lifted =
        lifted
          @ [Tag.Scannable.zero, param_var, symbol, [name, body, to_copy]]
          @ lifted'
      in
      let expr =
        Flambda.Expr.create_let param_var param_kind defining_expr handler
      in
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
  | Let { var; kind; defining_expr; body; _ } when should_copy defining_expr ->
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
  | Let { var; kind; defining_expr; body; _ } ->
    (* This let-expression is to be lifted. *)
    let var' = Variable.rename var in
    let symbol = Flambda_utils.make_variable_symbol var in
    let sym_defining_expr : Flambda.Named.t =
      match defining_expr with
      | Prim (Pmakeblock (_tag, Immutable, _shape), _fields, _dbg) ->
        Symbol symbol
      | _ -> Read_symbol_field (symbol, 0)
    in
    let to_copy = (var, kind, sym_defining_expr)::to_copy in
    let free_conts, lifted, body = lift ~importer body ~to_copy in
    let tag, conts_exprs_and_to_copies =
      match defining_expr with
      | Prim (Pmakeblock (tag, Immutable, _shape), fields, _dbg) ->
        let conts_exprs_and_to_copies =
          List.map (fun field ->
              let cont = Continuation.create () in
              let expr : Flambda.Expr.t = Apply_cont (cont, None, [field]) in
              cont, expr, to_copy)
            fields
        in
        Tag.Scannable.create_exn tag, conts_exprs_and_to_copies
      | _ ->
        let cont = Continuation.create () in
        let expr : Flambda.Expr.t =
          Flambda.Expr.create_let var' kind defining_expr
            (Apply_cont (cont, None, [var']))
        in
        Tag.Scannable.zero, [cont, expr, to_copy]
    in
    let lifted = (tag, var, symbol, conts_exprs_and_to_copies) :: lifted in
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
  | Let_mutable _ | Apply _ | Apply_cont _ | Switch _ | Proved_unreachable ->
    let free_conts = Flambda.Expr.free_continuations expr in
    free_conts, [], expr

(* CR-someday mshinwell: Try to avoid having a separate substitution phase. *)
let introduce_symbols ~importer expr =
  let _free_conts, lifted, expr = lift ~importer expr ~to_copy:[] in
  let lifted =
    List.map (fun (tag, var, symbol, conts_exprs_and_to_copies) ->
        let conts_exprs_and_to_copies =
          List.map (fun (cont, expr, to_copy) ->
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
              let expr =
                Flambda.Expr.toplevel_substitution ~importer subst expr
              in
              cont, expr, to_copy)
            conts_exprs_and_to_copies
        in
        tag, var, symbol, conts_exprs_and_to_copies)
      lifted
  in
  lifted, expr

let add_extracted lifted program_body =
  List.fold_left (fun acc (tag, _var, symbol, conts_exprs_and_to_copies)
            : Flambda_static.Program_body.t ->
      let fields =
        List.map (fun (cont, expr, to_copy) ->
            let expr =
              List.fold_left (fun expr (var, kind, defining_expr) ->
                  let fvs = Flambda.Expr.free_variables expr in
                  if Variable.Set.mem var fvs then
                    Flambda.Expr.create_let var kind defining_expr expr
                  else
                    expr)
                expr
                to_copy
            in
            expr, cont)
          conts_exprs_and_to_copies
      in
      let descr : Flambda_static.Program_body.initialize_symbol =
        Values {
          tag;
          fields;
        }
      in
      Initialize_symbol (symbol, descr, acc))
    program_body
    (List.rev lifted)

(* XXX but we need to either reflect kinds fully in Initialize_symbol or
   restrict this pass e.g. to only operate on [Value] *)

let rec split_program ~importer (program : Flambda_static.Program_body.t)
      : Flambda_static.Program_body.t =
  match program with
  | End s -> End s
  | Let_symbol (s, def, program) ->
    Let_symbol (s, def, split_program ~importer program)
  | Let_rec_symbol (defs, program) ->
    Let_rec_symbol (defs, split_program ~importer program)
  | Effect (expr, cont, program) ->
    let program = split_program ~importer program in
    let introduced, expr = introduce_symbols ~importer expr in
    add_extracted introduced (Flambda.Effect (expr, cont, program))
  | Initialize_symbol (symbol, tag, ((_::_::_) as fields), program) ->
    (* CR-someday pchambart: currently the only initialize_symbol with more
       than 1 field is the module block. This could evolve, in that case
       this pattern should be handled properly. *)
    Initialize_symbol (symbol, tag, fields, split_program ~importer program)
  | Initialize_symbol (sym, tag, [], program) ->
    Let_symbol (sym, Block (tag, []), split_program ~importer program)
  | Initialize_symbol (symbol, tag, [field, cont], program) ->
    let program = split_program ~importer program in
    let introduced, field = introduce_symbols ~importer field in
    add_extracted introduced
      (Flambda.Initialize_symbol (symbol, tag, [field, cont], program))

let lift ~backend (program : Flambda_static.Program.t) =
  let module B = (val backend : Backend_intf.S) in
  let importer = (module B : Flambda_type.Importer) in
  { program with
    program_body = split_program ~importer program.program_body;
  }
