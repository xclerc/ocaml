let iter_general = F0.Expr.iter_general

let iter f f_named t = iter_general ~toplevel:false f f_named (Is_expr t)
let iter_expr f t = iter f (fun _ -> ()) t
let iter_on_named f f_named t =
  iter_general ~toplevel:false f f_named (Is_named t)
let iter_named f_named t = iter (fun (_ : Expr.t) -> ()) f_named t
let iter_named_on_named f_named named =
  iter_general ~toplevel:false (fun (_ : Expr.t) -> ()) f_named
    (Is_named named)

let iter_toplevel f f_named t =
  iter_general ~toplevel:true f f_named (Is_expr t)
let iter_named_toplevel f f_named named =
  iter_general ~toplevel:true f f_named (Is_named named)

(* CR-soon mshinwell: Remove "let_rec" from these names *)
let iter_all_immutable_let_and_let_rec_bindings t ~f =
  iter_expr (function
      | Let { var; defining_expr; _ } -> f var defining_expr
      | _ -> ())
    t

let iter_all_toplevel_immutable_let_and_let_rec_bindings t ~f =
  iter_general ~toplevel:true
    (function
      | Let { var; defining_expr; _ } -> f var defining_expr
      | _ -> ())
    (fun _ -> ())
    (Is_expr t)

let iter_on_sets_of_closures f t =
  iter_named (function
      | Set_of_closures clos -> f clos
      | Var _ | Symbol _ | Const _ | Allocated_const _ | Read_mutable _
      | Assign _ | Read_symbol_field _ | Project_closure _
      | Move_within_set_of_closures _ | Project_var _ | Prim _ -> ())
    t
