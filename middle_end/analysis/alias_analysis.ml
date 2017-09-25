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

type allocation_point =
  | Symbol of Symbol.t
  | Variable of Variable.t

type allocated_const =
  | Normal of Allocated_const.t
  | Array of Lambda.array_kind * Asttypes.mutable_flag * Variable.t list
  | Duplicate_array of Lambda.array_kind * Asttypes.mutable_flag * Variable.t

type constant_project_var = {
  closure : Variable.t;
  closure_id : Closure_id.t;
  var : Var_within_closure.t;
}

type constant_defining_value =
  | Allocated_const of allocated_const
  | Block of Tag.t * Variable.t list
  | Set_of_closures of Flambda.Set_of_closures.t
  | Project_closure of Projection.Project_closure.t
  | Move_within_set_of_closures of Projection.Move_within_set_of_closures.t
  | Project_var of constant_project_var
  | Field of Variable.t * int
  | Symbol_field of Symbol.t * int
  | Const of Flambda.Const.t
  | Symbol of Symbol.t
  | Variable of Variable.t

type initialize_symbol_field = Variable.t option

type definitions = {
  variable : constant_defining_value Variable.Tbl.t;
  initialize_symbol : initialize_symbol_field list Symbol.Tbl.t;
  symbol : Flambda_static.Constant_defining_value.t Symbol.Tbl.t;
}

let print_constant_project_var ppf (project_var : constant_project_var) =
  Format.fprintf ppf "@[<2>(project_var@ %a@ from %a=%a)@]"
    Var_within_closure.print project_var.var
    Closure_id.print project_var.closure_id
    Variable.print project_var.closure

let print_constant_defining_value ppf = function
  | Allocated_const (Normal const) -> Allocated_const.print ppf const
  | Allocated_const (Array (_, _, vars)) ->
    Format.fprintf ppf "[| %a |]"
      (Format.pp_print_list Variable.print) vars
  | Allocated_const (Duplicate_array (_, _, var)) ->
    Format.fprintf ppf "dup_array(%a)" Variable.print var
  | Block (tag, vars) ->
    Format.fprintf ppf "[|%a: %a|]"
      Tag.print tag
      (Format.pp_print_list Variable.print) vars
  | Set_of_closures set -> Flambda.Set_of_closures.print ppf set
  | Project_closure project -> Projection.Project_closure.print ppf project
  | Move_within_set_of_closures move ->
    Projection.Move_within_set_of_closures.print ppf move
  | Project_var project -> print_constant_project_var ppf project
  | Field (var, field) -> Format.fprintf ppf "%a.(%d)" Variable.print var field
  | Symbol_field (sym, field) ->
    Format.fprintf ppf "%a.(%d)" Symbol.print sym field
  | Const const -> Flambda.Const.print ppf const
  | Symbol symbol -> Symbol.print ppf symbol
  | Variable var -> Variable.print ppf var

let rec resolve_definition
    (definitions: definitions)
    (var: Variable.t)
    (def: constant_defining_value)
    ~the_dead_constant : allocation_point =
  match def with
  | Allocated_const _
  | Block _
  | Set_of_closures _
  | Project_closure _
  | Const _
  | Move_within_set_of_closures _ ->
    Variable var
  | Project_var {var} ->
    fetch_variable definitions (Var_within_closure.unwrap var)
      ~the_dead_constant
  | Variable v ->
    fetch_variable definitions v
      ~the_dead_constant
  | Symbol sym -> Symbol sym
  | Field (v, n) ->
    begin match fetch_variable definitions v ~the_dead_constant with
    | Symbol s ->
      fetch_symbol_field definitions s n ~the_dead_constant
    | Variable v ->
      fetch_variable_field definitions v n ~the_dead_constant
    end
  | Symbol_field (symbol, field) ->
    fetch_symbol_field definitions symbol field ~the_dead_constant

and fetch_variable
    (definitions: definitions)
    (var: Variable.t)
    ~the_dead_constant : allocation_point =
  match Variable.Tbl.find definitions.variable var with
  | exception Not_found -> Variable var
  | def -> resolve_definition definitions var def ~the_dead_constant

and fetch_variable_field
    (definitions: definitions)
    (var: Variable.t)
    (field: int)
    ~the_dead_constant : allocation_point =
  match Variable.Tbl.find definitions.variable var with
  | Block (_, fields) ->
    begin match List.nth fields field with
    | exception Not_found -> Symbol the_dead_constant
    | v -> fetch_variable definitions v ~the_dead_constant
    end
  | exception Not_found ->
    Misc.fatal_errorf "No definition for field access to %a" Variable.print var
  | Symbol _ | Variable _ | Project_var _ | Field _ | Symbol_field _ ->
    (* Must have been resolved *)
    assert false
  | Const _ | Allocated_const _
  | Set_of_closures _ | Project_closure _ | Move_within_set_of_closures _ ->
    Symbol the_dead_constant

and fetch_symbol_field (definitions : definitions) (sym : Symbol.t)
      (field : int) ~the_dead_constant : allocation_point =
  match Symbol.Tbl.find definitions.symbol sym with
  | Block (_, fields) ->
    begin match List.nth fields field with
    | exception Not_found -> Symbol the_dead_constant
    | Symbol s -> Symbol s
    | Immediate _ -> Symbol sym
    end
  | exception Not_found ->
    begin match Symbol.Tbl.find definitions.initialize_symbol sym with
      | fields ->
        begin match List.nth fields field with
        | None ->
          Misc.fatal_errorf "Constant field access to an inconstant %a"
            Symbol.print sym
        | Some v ->
          fetch_variable definitions v ~the_dead_constant
        end
      | exception Not_found ->
        Misc.fatal_errorf "No definition for field access to %a"
          Symbol.print sym
    end
  | Allocated_const _ | Set_of_closures _ | Project_closure _ ->
    Symbol the_dead_constant

let run variable initialize_symbol symbol ~the_dead_constant =
  let definitions = { variable; initialize_symbol; symbol; } in
  Variable.Tbl.fold (fun var definition result ->
      let definition =
        resolve_definition definitions var definition ~the_dead_constant
      in
      Variable.Map.add var definition result)
    definitions.variable
    Variable.Map.empty
