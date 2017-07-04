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

(* CR-someday mshinwell: Move these three types into their own modules. *)

type project_closure = {
  set_of_closures : Variable.t;
  closure_id : Closure_id.Set.t;
}

type move_within_set_of_closures = {
  closure : Variable.t;
  move : Closure_id.t Closure_id.Map.t;
}

type project_var = {
  closure : Variable.t;
  (* closure_id : Closure_id.Set.t; *)
  var : Var_within_closure.t Closure_id.Map.t;
}

let compare_project_var
      ({ closure = closure1; var = var1; }
        : project_var)
      ({ closure = closure2; var = var2; }
        : project_var) =
  let c = Variable.compare closure1 closure2 in
  if c <> 0 then c
  else
    Closure_id.Map.compare Var_within_closure.compare var1 var2

let compare_move_within_set_of_closures
      ({ closure = closure1; move = move1; }
        : move_within_set_of_closures)
      ({ closure = closure2; move = move2; }
        : move_within_set_of_closures) =
  let c = Variable.compare closure1 closure2 in
  if c <> 0 then c
  else
    Closure_id.Map.compare Closure_id.compare move1 move2

let compare_project_closure
      ({ set_of_closures = set_of_closures1; closure_id = closure_id1; }
        : project_closure)
      ({ set_of_closures = set_of_closures2; closure_id = closure_id2; }
        : project_closure) =
  let c = Variable.compare set_of_closures1 set_of_closures2 in
  if c <> 0 then c
  else
    Closure_id.Set.compare closure_id1 closure_id2

let print_project_closure ppf (project_closure : project_closure) =
  Format.fprintf ppf "@[<2>(project_closure@ %a@ from@ %a)@]"
    Closure_id.Set.print project_closure.closure_id
    Variable.print project_closure.set_of_closures

let print_move_within_set_of_closures ppf
      (move_within_set_of_closures : move_within_set_of_closures) =
  Format.fprintf ppf
    "@[<2>(move_within_set_of_closures@ %a@ (closure = %a))@]"
    (Closure_id.Map.print Closure_id.print) move_within_set_of_closures.move
    Variable.print move_within_set_of_closures.closure

let print_project_var ppf (project_var : project_var) =
  Format.fprintf ppf "@[<2>(project_var@ %a@ from %a)@]"
    (Closure_id.Map.print Var_within_closure.print) project_var.var
    Variable.print project_var.closure

type t =
  | Project_var of project_var
  | Project_closure of project_closure
  | Move_within_set_of_closures of move_within_set_of_closures
  | Field of int * Variable.t
  | Prim of Lambda.primitive * Variable.t list
  | Switch of Variable.t

include Identifiable.Make (struct
  type nonrec t = t

  let compare t1 t2 =
    match t1, t2 with
    | Project_var project_var1, Project_var project_var2 ->
      compare_project_var project_var1 project_var2
    | Project_closure project_closure1, Project_closure project_closure2 ->
      compare_project_closure project_closure1 project_closure2
    | Move_within_set_of_closures move1, Move_within_set_of_closures move2 ->
      compare_move_within_set_of_closures move1 move2
    | Field (index1, var1), Field (index2, var2) ->
      let c = compare index1 index2 in
      if c <> 0 then c
      else Variable.compare var1 var2
    | Prim (prim1, args1), Prim (prim2, args2) ->
      let c = Pervasives.compare prim1 prim2 in
      if c <> 0 then c
      else Variable.compare_lists args1 args2
    | Switch arg1, Switch arg2 -> Variable.compare arg1 arg2
    | Project_var _, _ -> -1
    | _, Project_var _ -> 1
    | Project_closure _, _ -> -1
    | _, Project_closure _ -> 1
    | Move_within_set_of_closures _, _ -> -1
    | _, Move_within_set_of_closures _ -> 1
    | Prim _, _ -> -1
    | _, Prim _ -> 1
    | Switch _, _ -> -1
    | _, Switch _ -> 1

  let equal t1 t2 =
    (compare t1 t2) = 0

  let hash = Hashtbl.hash

  let print ppf t =
    match t with
    | Project_closure (project_closure) ->
      print_project_closure ppf project_closure
    | Project_var (project_var) -> print_project_var ppf project_var
    | Move_within_set_of_closures (move_within_set_of_closures) ->
      print_move_within_set_of_closures ppf move_within_set_of_closures
    | Field (field_index, var) ->
      Format.fprintf ppf "Field (%a, %d)" Variable.print var field_index
    | Prim (prim, args) ->
      Format.fprintf ppf "Prim (%a, %a)"
        Printlambda.primitive prim
        Variable.print_list args
    | Switch arg -> Format.fprintf ppf "Switch %a" Variable.print arg

  let output _ _ = failwith "Projection.output: not yet implemented"
end)

let projecting_from t =
  match t with
  | Project_var { closure; _ } -> closure
  | Project_closure { set_of_closures; _ } -> set_of_closures
  | Move_within_set_of_closures { closure; _ } -> closure
  | Field (_, var) -> var
  | Prim (Pisint, [var]) -> var
  | Prim (Pisint, _) -> Misc.fatal_error "Pisint with wrong number of arguments"
  | Prim (Pgettag, [var]) -> var
  | Prim (Pgettag, _) ->
    Misc.fatal_error "Pgettag with wrong number of arguments"
  | Prim (p, _) ->
    Misc.fatal_errorf "Unsupported pure primitive %a for CSE"
      Printlambda.primitive p
  | Switch var -> var

let map_projecting_from t ~f : t =
  match t with
  | Project_var project_var ->
    let project_var : project_var =
      { project_var with
        closure = f project_var.closure;
      }
    in
    Project_var project_var
  | Project_closure project_closure ->
    let project_closure : project_closure =
      { project_closure with
        set_of_closures = f project_closure.set_of_closures;
      }
    in
    Project_closure project_closure
  | Move_within_set_of_closures move ->
    let move : move_within_set_of_closures =
      { move with
        closure = f move.closure;
      }
    in
    Move_within_set_of_closures move
  | Field (field_index, var) -> Field (field_index, f var)
  | Prim (Pisint, [var]) -> Prim (Pisint, [f var])
  | Prim (Pisint, _) -> Misc.fatal_error "Pisint with wrong number of arguments"
  | Prim (Pgettag, [var]) -> Prim (Pgettag, [f var])
  | Prim (Pgettag, _) ->
    Misc.fatal_error "Pgettag with wrong number of arguments"
  | Prim (p, _) ->
    Misc.fatal_errorf "Unsupported pure primitive %a for CSE"
      Printlambda.primitive p
  | Switch var -> Switch (f var)
