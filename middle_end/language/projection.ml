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

module Project_closure = struct
  type t = {
    set_of_closures : Variable.t;
    closure_id : Closure_id.Set.t;
  }

  let free_variables t = Variable.Set.singleton t.set_of_closures

  let print ppf (t : t) =
    Format.fprintf ppf "@[<2>(project_closure@ %a@ from@ %a)@]"
      Closure_id.Set.print t.closure_id
      Variable.print t.set_of_closures
end

module Move_within_set_of_closures = struct
  type t = {
    closure : Variable.t;
    move : Closure_id.t Closure_id.Map.t;
  }

  let free_variables t = Variable.Set.singleton t.closure

  let print ppf (t : t) =
    Format.fprintf ppf
      "@[<2>(move_within_set_of_closures@ %a@ (closure = %a))@]"
      (Closure_id.Map.print Closure_id.print) t.move
      Variable.print t.closure
end

module Project_var = struct
  type t = {
    closure : Variable.t;
    var : Var_within_closure.t Closure_id.Map.t;
  }

  let free_variables t = Variable.Set.singleton t.closure

  let print ppf (t : t) =
    Format.fprintf ppf "@[<2>(project_var@ %a@ from %a)@]"
      (Closure_id.Map.print Var_within_closure.print) t.var
      Variable.print t.closure
end

type t =
  | Project_var of Project_var.t
  | Project_closure of Project_closure.t
  | Move_within_set_of_closures of Move_within_set_of_closures.t
  | Primitive_with_fixed_value of Flambda_primitive.With_fixed_value.t
  | Box_number of Flambda_kind.Boxable_number.t * Variable.t
  | Switch of Variable.t

let print ppf t =
  match t with
  | Project_closure (project_closure) ->
    Project_closure.print ppf project_closure
  | Project_var (project_var) -> Project_var.print ppf project_var
  | Move_within_set_of_closures (move_within_set_of_closures) ->
    Move_within_set_of_closures.print ppf move_within_set_of_closures
  | Primitive_with_fixed_value (prim, args) ->
    Format.fprintf ppf "Primitive_with_fixed_value (%a, %a)"
      Printlambda.primitive prim
      Variable.print_list args
  | Block_load (field, block) ->
    Format.fprintf ppf "Block_load (%d, %a)" field Variable.print block
  | Switch arg -> Format.fprintf ppf "Switch %a" Variable.print arg

let projecting_from t =
  match t with
  | Project_var { closure; _ } -> closure
  | Project_closure { set_of_closures; _ } -> set_of_closures
  | Move_within_set_of_closures { closure; _ } -> closure
  | Primitive_with_fixed_value (prim, [var]) ->
    begin match prim with
    | Pfield _ | Pisint | Pgettag | Punbox_float | Pbox_float
    | Punbox_int32 | Pbox_int32 | Punbox_int64 | Pbox_int64
    | Punbox_nativeint | Pbox_nativeint | Puntag_immediate
    | Ptag_immediate -> var
    | _ ->
      Misc.fatal_errorf "Unsupported pure primitive %a for CSE"
        Printlambda.primitive prim
    end
  | Primitive_with_fixed_value (prim, vars) ->
    Misc.fatal_errorf "Unsupported pure primitive, or wrong number of \
        arguments for pure primitive CSE: %a (%a)"
      Printlambda.primitive prim
      Variable.print_list vars
  | Box_number (_kind, var) -> var
  | Switch var -> var

let map_projecting_from t ~f : t =
  match t with
  | Project_var project_var ->
    let project_var : Project_var.t =
      { project_var with
        closure = f project_var.closure;
      }
    in
    Project_var project_var
  | Project_closure project_closure ->
    let project_closure : Project_closure.t =
      { project_closure with
        set_of_closures = f project_closure.set_of_closures;
      }
    in
    Project_closure project_closure
  | Move_within_set_of_closures move ->
    let move : Move_within_set_of_closures.t =
      { move with
        closure = f move.closure;
      }
    in
    Move_within_set_of_closures move
  | Primitive_with_fixed_value (prim, [var]) ->
    begin match prim with
    | Pfield _ | Pisint | Pgettag | Punbox_float | Pbox_float
    | Punbox_int32 | Pbox_int32 | Punbox_int64 | Pbox_int64
    | Punbox_nativeint | Pbox_nativeint | Puntag_immediate
    | Ptag_immediate -> Primitive_with_fixed_value (prim, [f var])
    | _ ->
      Misc.fatal_errorf "Unsupported pure primitive %a for CSE"
        Printlambda.primitive prim
    end
  | Primitive_with_fixed_value (prim, vars) ->
    Misc.fatal_errorf "Unsupported pure primitive, or wrong number of \
        arguments for pure primitive CSE: %a (%a)"
      Printlambda.primitive prim
      Variable.print_list vars
  | Block_load (field, block) -> Block_load (field, f block)
  | Switch var -> Switch (f var)

let free_variables t =
  match t with
  | Project_var proj -> Project_var.free_variables proj
  | Project_closure proj -> Project_closure.free_variables proj
  | Move_within_set_of_closures move ->
    Move_within_set_of_closures.free_variables move
  | Primitive_with_fixed_value (_prim, vars) -> Variable.Set.of_list vars
  | Block_load (_field, block) -> Variable.Set.singleton block
  | Switch var -> Variable.Set.singleton var
