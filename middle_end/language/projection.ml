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

  include Identifiable.Make (struct
    type nonrec t = t

    let compare
          ({ set_of_closures = set_of_closures1; closure_id = closure_id1; }
            : t)
          ({ set_of_closures = set_of_closures2; closure_id = closure_id2; }
            : t) =
      let c = Variable.compare set_of_closures1 set_of_closures2 in
      if c <> 0 then c
      else Closure_id.Set.compare closure_id1 closure_id2

    let equal t1 t2 =
      (compare t1 t2) = 0

    let hash = Hashtbl.hash

    let print ppf (t : t) =
      Format.fprintf ppf "@[<2>(project_closure@ %a@ from@ %a)@]"
        Closure_id.Set.print t.closure_id
        Variable.print t.set_of_closures
  end)
end

module Move_within_set_of_closures = struct
  type t = {
    closure : Variable.t;
    move : Closure_id.t Closure_id.Map.t;
  }

  let free_variables t = Variable.Set.singleton t.closure

  include Identifiable.Make (struct
    type nonrec t = t

    let compare
          ({ closure = closure1; move = move1; } : t)
          ({ closure = closure2; move = move2; } : t) =
      let c = Variable.compare closure1 closure2 in
      if c <> 0 then c
      else Closure_id.Map.compare Closure_id.compare move1 move2

    let equal t1 t2 =
      (compare t1 t2) = 0

    let hash = Hashtbl.hash

    let print ppf (t : t) =
      Format.fprintf ppf
        "@[<2>(move_within_set_of_closures@ %a@ (closure = %a))@]"
        (Closure_id.Map.print Closure_id.print) t.move
        Variable.print t.closure
  end)
end

module Project_var = struct
  type t = {
    closure : Variable.t;
    var : Var_within_closure.t Closure_id.Map.t;
  }

  let free_variables t = Variable.Set.singleton t.closure

  include Identifiable.Make (struct
    type nonrec t = t

    let compare
          ({ closure = closure1; var = var1; } : t)
          ({ closure = closure2; var = var2; } : t) =
      let c = Variable.compare closure1 closure2 in
      if c <> 0 then c
      else Closure_id.Map.compare Var_within_closure.compare var1 var2

    let equal t1 t2 =
      (compare t1 t2) = 0

    let hash = Hashtbl.hash

    let print ppf (t : t) =
      Format.fprintf ppf "@[<2>(project_var@ %a@ from %a)@]"
        (Closure_id.Map.print Var_within_closure.print) t.var
        Variable.print t.closure
  end)
end

type t =
  | Project_var of Project_var.t
  | Project_closure of Project_closure.t
  | Move_within_set_of_closures of Move_within_set_of_closures.t
  | Pure_primitive of Flambda_primitive.t
  | Field of int * Variable.t
  | Switch of Variable.t

include Identifiable.Make (struct
  type nonrec t = t

  let compare t1 t2 =
    match t1, t2 with
    | Project_var project_var1, Project_var project_var2 ->
      Project_var.compare project_var1 project_var2
    | Project_closure project_closure1, Project_closure project_closure2 ->
      Project_closure.compare project_closure1 project_closure2
    | Move_within_set_of_closures move1, Move_within_set_of_closures move2 ->
      Move_within_set_of_closures.compare move1 move2
    | Pure_primitive (prim1, args1), Pure_primitive (prim2, args2) ->
      let c = Pervasives.compare prim1 prim2 in
      if c <> 0 then c
      else Variable.compare_lists args1 args2
    | Field (field1, block1), Field (field2, block2) ->
      let c = Pervasives.compare field1 field2 in
      if c <> 0 then c
      else Variable.compare block1 block2
    | Switch arg1, Switch arg2 -> Variable.compare arg1 arg2
    | Project_var _, _ -> -1
    | _, Project_var _ -> 1
    | Project_closure _, _ -> -1
    | _, Project_closure _ -> 1
    | Move_within_set_of_closures _, _ -> -1
    | _, Move_within_set_of_closures _ -> 1
    | Pure_primitive _, _ -> -1
    | _, Pure_primitive _ -> 1
    | Field _, _ -> -1
    | _, Field _ -> 1

  let equal t1 t2 =
    (compare t1 t2) = 0

  let hash = Hashtbl.hash

  let print ppf t =
    match t with
    | Project_closure (project_closure) ->
      Project_closure.print ppf project_closure
    | Project_var (project_var) -> Project_var.print ppf project_var
    | Move_within_set_of_closures (move_within_set_of_closures) ->
      Move_within_set_of_closures.print ppf move_within_set_of_closures
    | Pure_primitive (prim, args) ->
      Format.fprintf ppf "Pure_primitive (%a, %a)"
        Printlambda.primitive prim
        Variable.print_list args
    | Field (field, block) ->
      Format.fprintf ppf "Field (%d, %a)" field Variable.print block
    | Switch arg -> Format.fprintf ppf "Switch %a" Variable.print arg
end)

let projecting_from t =
  match t with
  | Project_var { closure; _ } -> closure
  | Project_closure { set_of_closures; _ } -> set_of_closures
  | Move_within_set_of_closures { closure; _ } -> closure
  | Pure_primitive (prim, [var]) ->
    begin match prim with
    | Pfield _ | Pisint | Pgettag | Punbox_float | Pbox_float
    | Punbox_int32 | Pbox_int32 | Punbox_int64 | Pbox_int64
    | Punbox_nativeint | Pbox_nativeint | Puntag_immediate
    | Ptag_immediate -> var
    | _ ->
      Misc.fatal_errorf "Unsupported pure primitive %a for CSE"
        Printlambda.primitive prim
    end
  | Pure_primitive (prim, vars) ->
    Misc.fatal_errorf "Unsupported pure primitive, or wrong number of \
        arguments for pure primitive CSE: %a (%a)"
      Printlambda.primitive prim
      Variable.print_list vars
  | Field (_field, block) -> block
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
  | Pure_primitive (prim, [var]) ->
    begin match prim with
    | Pfield _ | Pisint | Pgettag | Punbox_float | Pbox_float
    | Punbox_int32 | Pbox_int32 | Punbox_int64 | Pbox_int64
    | Punbox_nativeint | Pbox_nativeint | Puntag_immediate
    | Ptag_immediate -> Pure_primitive (prim, [f var])
    | _ ->
      Misc.fatal_errorf "Unsupported pure primitive %a for CSE"
        Printlambda.primitive prim
    end
  | Pure_primitive (prim, vars) ->
    Misc.fatal_errorf "Unsupported pure primitive, or wrong number of \
        arguments for pure primitive CSE: %a (%a)"
      Printlambda.primitive prim
      Variable.print_list vars
  | Field (field, block) -> Field (field, f block)
  | Switch var -> Switch (f var)

let free_variables t =
  match t with
  | Project_var proj -> Project_var.free_variables proj
  | Project_closure proj -> Project_closure.free_variables proj
  | Move_within_set_of_closures move ->
    Move_within_set_of_closures.free_variables move
  | Pure_primitive (_prim, vars) -> Variable.Set.of_list vars
  | Field (_field, block) -> Variable.Set.singleton block
  | Switch var -> Variable.Set.singleton var
