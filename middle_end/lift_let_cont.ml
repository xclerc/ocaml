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

let rebuild_let_conts defs ~body =
  List.fold_left (fun body (name, handler) ->
      Flambda.Let_cont { name; body; handler; })
    body defs

let params_do_not_overlap_free_variables ~params ~handler =
  let params = Variable.Set.of_list params in
  let handler_fvs = Flambda.free_variables handler in
  Variable.Set.is_empty (Variable.Set.inter params handler_fvs)

let rec extract_let_conts acc (let_cont : Flambda.let_cont) =
  match let_cont with
  | { name; body = body1; handler = Handler {
        params; recursive; handler = Let_cont ({ body = _;
          handler = Handler { handler; _ }; _ } as let_cont2); }; }
      when params_do_not_overlap_free_variables ~params ~handler ->
    let acc, body2 = extract_let_conts acc let_cont2 in
    let acc =
      (name, Flambda.Handler { params; recursive; handler = body2; }) :: acc
    in
    extract acc body1
  | { name; body; handler; } ->
    let acc = (name, handler) :: acc in
    extract acc body

and extract acc (expr : Flambda.t) =
  match expr with
  | Let_cont let_cont -> extract_let_conts acc let_cont
  | _ -> acc, expr

let rec lift_let_conts_expr (expr : Flambda.t) : Flambda.t =
  match expr with
  | Let_cont let_cont ->
    let defs, body = extract_let_conts [] let_cont in
    let rev_defs =
      List.rev_map (fun (name, (handler : Flambda.let_cont_handler)) ->
          match handler with
          | Handler ({ handler; } as handler') ->
            name, Flambda.Handler {
              handler' with handler = lift_let_conts_expr handler; }
          | Alias _ -> name, handler)
        defs
    in
    let body = lift_let_conts_expr body in
    rebuild_let_conts (List.rev rev_defs) ~body
  | expr ->
    Flambda_iterators.map_subexpressions
      (lift_let_conts_expr)
      (lift_let_conts_named)
      expr

and lift_let_conts_named _var (named : Flambda.named) : Flambda.named =
  match named with
  | Set_of_closures set ->
    Set_of_closures
      (Flambda_iterators.map_function_bodies set ~f:lift_let_conts_expr)
  | Var _ | Symbol _ | Const _ | Allocated_const _ | Read_mutable _ | Assign _
  | Read_symbol_field (_, _) | Project_closure _ | Move_within_set_of_closures _
  | Project_var _ | Prim _ | Proved_unreachable -> named

let run program =
  Flambda_iterators.map_exprs_at_toplevel_of_program program
    ~f:lift_let_conts_expr
