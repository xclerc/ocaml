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

let dependency (expr:Flambda.Expr.t) = Flambda.free_symbols expr

(* CR-soon pchambart: copied from lift_constant.  Needs remerging *)
let constant_dependencies (const:Flambda_static.Constant_defining_value.t) =
  let closure_dependencies (set_of_closures:Flambda.Set_of_closures.t) =
    Flambda.free_symbols_named (Set_of_closures set_of_closures)
  in
  match const with
  | Allocated_const _ -> Symbol.Set.empty
  | Block (_, fields) ->
    let symbol_fields =
      Misc.Stdlib.List.filter_map (function
          | (Symbol s : Flambda_static.Constant_defining_value.t_block_field) ->
            Some s
          | Flambda.Const _ -> None)
        fields
    in
    Symbol.Set.of_list symbol_fields
  | Set_of_closures set_of_closures -> closure_dependencies set_of_closures
  | Project_closure (s, _) -> Symbol.Set.singleton s

let let_rec_dep defs dep =
  let add_deps l dep =
    List.fold_left (fun dep (sym, sym_dep) ->
        if Symbol.Set.mem sym dep then Symbol.Set.union dep sym_dep
        else dep)
      dep l
  in
  let defs_deps =
    List.map (fun (sym, def) -> sym, constant_dependencies def) defs
  in
  let rec fixpoint dep =
    let new_dep = add_deps defs_deps dep in
    if Symbol.Set.equal dep new_dep then dep
    else fixpoint new_dep
  in
  fixpoint dep

let no_effects_field_arity_0 (expr : Flambda.Expr.t) ~return_continuation =
  match expr with
  | Apply_cont (cont, None, [])
      when Continuation.equal cont return_continuation -> true
  | _ -> Effect_analysis.no_effects expr

let no_effects_field_arity_1 (expr : Flambda.Expr.t) ~return_continuation =
  match expr with
  | Let { var; defining_expr;
        body = Apply_cont (cont, None, [var']); _ }
      when Continuation.equal cont return_continuation
        && Effect_analysis.no_effects_named defining_expr ->
    assert (Variable.equal var var');  (* [var] is the only thing in scope *)
    true
  | _ -> Effect_analysis.no_effects expr

let rec loop (program : Flambda_static.Program.t_body)
      : Flambda_static.Program.t_body * Symbol.Set.t =
  match program with
  | Let_symbol (sym, def, program) ->
    let program, dep = loop program in
    if Symbol.Set.mem sym dep then
      Let_symbol (sym, def, program),
      Symbol.Set.union dep (constant_dependencies def)
    else
      program, dep
  | Let_rec_symbol (defs, program) ->
    let program, dep = loop program in
    let dep = let_rec_dep defs dep in
    let defs =
      List.filter (fun (sym, _) -> Symbol.Set.mem sym dep) defs
    in
    Let_rec_symbol (defs, program), dep
  | Initialize_symbol (sym, descr, program) ->
    let program, dep = loop program in
    if Symbol.Set.mem sym dep then
      let dep =
        List.fold_left (fun dep (field, _cont) ->
            Symbol.Set.union dep (dependency field))
          dep fields
      in
      Initialize_symbol (sym, descr, program), dep
    else begin
      List.fold_left (fun (program, dep) (field, cont) ->
          if no_effects_field_arity_1 field ~return_continuation:cont then
            program, dep
          else
            let new_dep = dependency field in
            let dep = Symbol.Set.union new_dep dep in
            let cont' = Continuation.create cont' in
            let result_kind =
              Flambda_static.Program_body.kind_of_initialize_symbol descr
            in
            let result_var = Variable.create "effect_result" in
            let result_type = Flambda_type.unknown result_kind in
            let result_param =
              Typed_parameter.create (Parameter.wrap result_var) result_type
            in
            let expr : Flambda.Expr.t =
              Let_cont {
                body = field;
                handlers = Nonrecursive {
                  name = cont;
                  handler = {
                    params = [result_param];
                    stub = false;
                    is_exn_handler = false;
                    handler = Apply_cont (cont', None, []);
                  };
                };
              };
            in
            Flambda.Effect (field, cont', program), dep)
        (program, dep) fields
    end
  | Effect (effect, cont, program) ->
    let program, dep = loop program in
    if no_effects_field_arity_0 effect ~return_continuation:cont then
      program, dep
    else begin
      let new_dep = dependency effect in
      let dep = Symbol.Set.union new_dep dep in
      Effect (effect, cont, program), dep
    end
  | End symbol -> program, Symbol.Set.singleton symbol

let remove_unused_program_constructs (program : Flambda_static.Program.t) =
  { program with
    program_body = fst (loop program.program_body);
  }
