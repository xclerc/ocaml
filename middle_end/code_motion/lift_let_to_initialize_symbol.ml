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

(* CR mshinwell for pchambart: Given your changes in Closure_conversion, maybe
   we don't need the special [Pmakeblock] case here now. *)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module IS = Flambda_static.Program_body.Initialize_symbol

let should_copy (named : Flambda.Named.t) =
  match named with
  | Symbol _ | Read_symbol_field _ | Const _ -> true
  | _ -> false

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
         [body] and put it inside an [Initialize_symbol] whose continuation
         is [handler].
         We augment [to_copy] to ensure that the bindings of the variables
         currently serving as parameters to [handler] is/are restated at the
         top of each subsequent lifted expression. *)
      let arity = Flambda.Typed_parameter.List.arity ~importer params in
      let symbol =
        let linkage_name =
          Linkage_name.create
            (Format.asprintf "lifted_%a" Continuation.print name)
        in
        Symbol.create (Compilation_unit.get_current_exn ())
          linkage_name
          ~kind:(Symbol.mixed_kind arity)
      in
      let to_copy' =
        List.mapi (fun param_index param ->
            let defining_expr : Flambda.Named.t =
              Read_symbol_field {
                symbol;
                logical_field = param_index;
              }
            in
            let param_var = Flambda.Typed_parameter.var param in
            let param_kind = Flambda.Typed_parameter.kind ~importer param in
            param_var, param_kind, defining_expr)
          params
      in
      let to_copy = to_copy' @ to_copy in
      let free_conts_handler, lifted', handler =
        lift ~importer handler ~to_copy
      in
      let descr : IS.t =
        { expr = body;
          return_cont = name;
          return_arity = arity;
        }
      in
      let lifted = lifted @ [symbol, descr, to_copy] @ lifted' in
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
    let symbol, sym_defining_expr =
      (* We have a special case here for [Pmakeblock] to avoid relying on
         the unboxing pass for [Initialize_symbol] constructions when
         compiling module blocks (which must be represented in a particular
         way). *)
      match defining_expr with
      | Prim (Pmakeblock (tag, Immutable, _shape), _fields, _dbg) ->
        if not (Flambda_kind.is_value kind) then begin
          Misc.fatal_errorf "[Let]-binding of variable %a should be of kind \
              [Value] but is of kind %a.  Defining expression: %a"
            Variable.print var
            Flambda_kind.print kind
            Flambda.Named.print defining_expr
        end;
        let tag = Tag.create_exn tag in
        let symbol =
          Flambda_utils.make_variable_symbol var
            ~kind:(Symbol.value_kind tag)
        in
        symbol, Flambda.Named.Symbol (Symbol.Of_kind_value.of_symbol_exn symbol)
      | _ ->
        let symbol =
          Flambda_utils.make_variable_symbol var
            ~kind:(Symbol.mixed_kind [kind])
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
      match defining_expr with
      | Prim (Pmakeblock (_tag, Immutable, shape), fields, _dbg) ->
        let return_cont = Continuation.create () in
        let num_fields = List.length fields in
        let return_arity = Flambda_arity.of_block_shape shape ~num_fields in
        let fields' = Variable.List.rename fields in
        let field_renaming = List.combine fields fields' in
        assert (Flambda_arity.length return_arity = List.length fields');
        let bindings =
          List.map2 (fun (old_field, new_field) kind ->
              let defining_expr : Flambda.Named.t = Var old_field in
              new_field, kind, defining_expr)
            field_renaming
            return_arity
        in
        let body : Flambda.Expr.t = Apply_cont (return_cont, None, fields') in
        let expr = Flambda.Expr.bind ~bindings ~body in
        return_cont, return_arity, expr
      | _ ->
        let return_cont = Continuation.create () in
        let return_arity = [Flambda_kind.value Must_scan] in
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
let introduce_symbols ~importer expr =
  let _free_conts, lifted, expr = lift ~importer expr ~to_copy:[] in
  let lifted =
    List.map (fun (symbol, (descr : IS.t), to_copy) ->
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
  List.fold_left (fun acc (symbol, (descr : IS.t), to_copy)
        : Flambda_static.Program_body.t ->
      let expr =
        List.fold_left (fun expr (var, kind, defining_expr) ->
            let fvs = Flambda.Expr.free_variables expr in
            if Variable.Set.mem var fvs then
              Flambda.Expr.create_let var kind defining_expr expr
            else
              expr)
          descr.expr
          to_copy
      in
      let descr = { descr with expr; } in
      Initialize_symbol (symbol, descr, acc))
    program_body
    (List.rev lifted)

let rec lift_program ~importer (program : Flambda_static.Program_body.t)
      : Flambda_static.Program_body.t =
  match program with
  | End s -> End s
  | Let_symbol (s, def, program) ->
    Let_symbol (s, def, lift_program ~importer program)
  | Let_rec_symbol (defs, program) ->
    Let_rec_symbol (defs, lift_program ~importer program)
  | Effect (expr, cont, program) ->
    let program = lift_program ~importer program in
    let introduced, expr = introduce_symbols ~importer expr in
    add_extracted introduced
      (Flambda_static.Program_body.Effect (expr, cont, program))
  | Initialize_symbol (symbol, descr, program) ->
    let program = lift_program ~importer program in
    let introduced, expr = introduce_symbols ~importer descr.expr in
    add_extracted introduced
      (Flambda_static.Program_body.Initialize_symbol
        (symbol, { descr with expr; }, program))

let lift ~backend (program : Flambda_static.Program.t) =
  let module B = (val backend : Backend_intf.S) in
  let importer = (module B : Flambda_type.Importer) in
  { program with
    program_body = lift_program ~importer program.program_body;
  }
