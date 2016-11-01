(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2016 OCamlPro SAS                                          *)
(*   Copyright 2016 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** "Use CPS".
    -- A. Kennedy, "Compiling with Continuations Continued", ICFP 2007.
*)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module I = Ilambda
module L = Lambda

type proto_switch = {
  numconsts : int;
  consts : (int * L.lambda) list;
  numblocks : int;
  block_pats : I.switch_block_pattern list;
  blocks : L.lambda list;
  failaction : L.lambda option;
}

let check_let_rec_bindings bindings =
  List.map (fun (binding : Lambda.lambda) ->
      match binding with
      | Lfunction func -> func
      | _ ->
        Misc.fatal_error "Only [Lfunction] expressions are permitted in \
            [Lletrec] bindings upon entry to CPS conversion: %a"
          Printlambda.lam binding)
    bindings

let name_for_function (func : Lambda.lfunction) =
  (* Name anonymous functions by their source location, if known. *)
  if loc = Location.none then "anon-fn"
  else Format.asprintf "anon-fn[%a]" Location.print_compact loc

let rec cps_non_tail (lam : L.lambda) (k : Ident.t -> Ilambda.t) : Ilambda.t =
  match lam with
  | Lvar id -> k id
  | Lconst _ -> name_then_cps_non_tail "const" lam k
  | Lapply apply ->
    cps_non_tail apply.ap_func (fun func ->
      cps_non_tail_list apply.ap_args (fun args ->
        let continuation = Continuation.create () in
        let result_var = Ident.create "apply_result" in
        let after = k result_var in
        let apply : Ilambda.apply = {
          kind = Function;
          func;
          continuation;
          args;
          loc = apply.ap_loc;
          should_be_tailcall = apply.ap_should_be_tailcall;
          inlined = apply.ap_inlined;
          specialised = apply.ap_specialised;
        } in
        Let_cont (continuation, [result_var], after, Apply apply)))
  | Lfunction func -> name_then_cps_non_tail (name_for_function func) lam k
  (* The following specialised Llet cases help to avoid administrative
     redexes. *)
  | Llet (let_kind, value_kind, id, (Lvar id) as defining_expr, body) ->
    Let (let_kind, value_kind, id, Var id, cps_non_tail body k)
  | Llet (let_kind, value_kind, id, (Lconst const) as defining_expr, body) ->
    Let (let_kind, value_kind, id, Const const, cps_non_tail body k)
  | Llet (let_kind, value_kind, id, Lfunction func, body) ->
    let func = cps_function func in
    let body = cps_non_tail body k in
    Let (let_kind, value_kind, id, func, body)
  | Llet (let_kind, value_kind, id, Lprim (prim, args, loc), body) ->
    let body = cps_non_tail body k in
    cps_non_tail_list args (fun args ->
      Let (Strict, Pgenval, id, Prim (prim, args, loc), body))
  | Llet (let_kind, value_kind, id, defining_expr, body) ->
    let body = cps_non_tail body k in
    let after_body = Continuation.create () in
    let defining_expr = cps_tail defining_expr after_body in
    Let_cont (after_body, [id], body, defining_expr)
  | Lletrec (bindings, body) ->
    let idents, bindings = List.split bindings in
    let bindings = List.map cps_function (check_let_rec_bindings bindings) in
    let body = cps_non_tail body k in
    Let_rec (List.combine idents bindings, body)
  | Lprim (prim, args, loc) ->
    let result_var = Ident.create "prim_result" in
    cps_non_tail_list args (fun args ->
      Let (Strict, Pgenval, result_var, Prim (prim, args, loc), k result_var))
  | Lswitch (scrutinee, switch) ->
    let after_switch = Continuation.create () in
    let result_var = Ident.create "switch_result" in
    let after = k result_var in
    let block_nums, blocks = List.split switch.sw_blocks in
    let block_pats = List.map (fun tag -> I.Tag tag) block_nums in
    let proto_switch : proto_switch =
      { numconsts = switch.sw_numconsts;
        consts = switch.sw_numconsts;
        numblocks = switch.sw_numblocks;
        block_pats;
        blocks;
        failaction;
      }
    in
    Let_cont (after_switch, [result_var], after,
      cps_switch proto_switch ~scrutinee after_switch)
  | Lstringswitch (scrutinee, cases, default, loc) ->
    let after_switch = Continuation.create () in
    let result_var = Ident.create "stringswitch_result" in
    let after = k result_var in
    let strs, cases = List.split cases in
    let pats = List.map (fun str -> I.String str) strs in
    let proto_switch : proto_switch =
      { numconsts = 0;
        consts = [];
        numblocks = List.length pats;
        block_pats = pats;
        blocks = cases;
        failaction = default;
      }
    in
    Let_cont (after_switch, [result_var], after,
      cps_switch proto_switch ~scrutinee after_switch)
  | Lstaticraise (static_exn, args) ->
    let continuation = Continuation.unsafe_of_static_exn static_exn in
    cps_non_tail_list args (fun args -> I.Apply_cont (continuation, args))
  | Lstaticcatch (body, (static_exn, args), handler) ->
    let continuation = Continuation.unsafe_of_static_exn static_exn in
    let after_continuation = Continuation.create () in
    let result_var = Ident.create "staticcatch_result" in
    let body = cps_tail body after_continuation in
    let handler = cps_tail handler after_continuation in
    Let_cont (after_continuation, [], k result_var,
      Let_cont (continuation, args, handler, body))
  | Lsend (meth_kind, meth, obj, args, loc) ->
    cps_non_tail obj (fun func ->
      cps_non_tail_list args (fun args ->
        let continuation = Continuation.create () in
        let result_var = Ident.create "send_result" in
        let after = k result_var in
        let apply : Ilambda.apply = {
          kind = Method { kind = meth_kind; obj; };
          func = meth;
          continuation;
          args;
          loc;
          should_be_tailcall = false;
          inlined = Default_inline;
          specialised = Default_specialise;
        } in
        Let_cont (continuation, [result_var], after, Apply apply)))
  | Lsequence _ | Lifthenelse _ | Lwhile _ | Lfor _ | Lassign _ | Lifused _
  | Ltrywith _ ->
    Misc.fatal_errorf "Term should have been eliminated by [Prepare_lambda]: %a"
      Printlambda.lambda lam

and cps_tail (lam : L.lambda) (k : Continuation.t) : Ilambda.t =
  match lam with
  | Lvar id -> Apply_cont (k, [id])
  | Lconst _ -> name_then_cps_tail "const" lam k
  | Lapply apply ->
    cps_non_tail apply.ap_func (fun func ->
      cps_non_tail_list apply.ap_args (fun args ->
        let apply : I.apply = {
          func;
          continuation = k;
          args;
          loc = apply.ap_loc;
          should_be_tailcall = apply.ap_should_be_tailcall;
          inlined = apply.ap_inlined;
          specialised = apply.ap_specialised;
        } in
        Apply apply))
  | Lfunction func -> name_then_cps_tail (name_for_function func) lam k
  | Llet (let_kind, value_kind, id, (Lvar id) as defining_expr, body) ->
    Let (let_kind, value_kind, id, Var id, cps_tail body k)
  | Llet (let_kind, value_kind, id, (Lconst const) as defining_expr, body) ->
    Let (let_kind, value_kind, id, Const const, cps_tail body k)
  | Llet (let_kind, value_kind, id, Lfunction func, body) ->
    let func = cps_function func in
    let body = cps_tail body k in
    Let (let_kind, value_kind, id, func, body)
  | Llet (let_kind, value_kind, id, defining_expr, body) ->
    let body = cps_tail body k in
    let after_body = Continuation.create () in
    let defining_expr = cps_tail defining_expr after_body in
    Let_cont (after_body, [id], body, defining_expr)
  | Lletrec (bindings, body) ->
    let idents, bindings = List.split bindings in
    let bindings = List.map cps_function (check_let_rec_bindings bindings) in
    let body = cps_tail body k in
    Let_rec (List.combine idents bindings, body)
  | Lprim (prim, args, loc) ->
(* Old CC code.  Use the naming stuff
    let name = Printlambda.name_of_primitive p in
    let dbg = Debuginfo.from_location loc in
    Lift_code.lifting_helper (close_list t env args)
      ~evaluation_order:`Right_to_left
      ~name:(name ^ "_arg")
      ~create_body:(fun args ->
        name_expr (Prim (p, args, dbg))
          ~name)
*)
    let result_var = Ident.create "prim_result" in
    cps_non_tail_list args (fun args ->
      I.Let (Strict, Pgenval, result_var, Prim (prim, args, loc),
        Apply_cont (k, [result_var])))
  | Lswitch (scrutinee, switch) ->
    let block_nums, blocks = List.split switch.sw_blocks in
    let block_pats = List.map (fun tag -> I.Tag tag) block_nums in
    let proto_switch : proto_switch =
      { numconsts = switch.sw_numconsts;
        consts = switch.sw_numconsts;
        numblocks = switch.sw_numblocks;
        block_pats;
        blocks;
        failaction;
      }
    in
    cps_switch proto_switch ~scrutinee k
  | Lstringswitch (scrutinee, cases, default, loc) ->
    let strs, cases = List.split cases in
    let pats = List.map (fun str -> I.String str) strs in
    let proto_switch : proto_switch =
      { numconsts = 0;
        consts = [];
        numblocks = List.length pats;
        block_pats = pats;
        blocks = cases;
        failaction = default;
      }
    in
    cps_switch proto_switch ~scrutinee k
  | Lstaticraise (cont, args) ->
    let continuation = Continuation.unsafe_of_static_exn static_exn in
    cps_non_tail_list args (fun args -> I.Apply_cont (k, args))
  | Lstaticcatch (body, (cont, args), handler) ->
    let continuation = Continuation.unsafe_of_static_exn static_exn in
    let result_var = Ident.create "staticcatch_result" in
    let body = cps_tail body k in
    let handler = cps_tail handler k in
    Let_cont (continuation, args, handler, body)
  | Lsend (meth_kind, meth, obj, args, loc) ->
    cps_non_tail obj (fun func ->
      cps_non_tail_list args (fun args ->
        let apply : Ilambda.apply = {
          kind = Method { kind = meth_kind; obj; };
          func = meth;
          continuation = k;
          args;
          loc;
          should_be_tailcall = false;
          inlined = Default_inline;
          specialised = Default_specialise;
        } in
        Apply apply))
  | Lsequence _ | Lifthenelse _ | Lwhile _ | Lfor _ | Lassign _ | Lifused _
  | Ltrywith _ ->
    Misc.fatal_errorf "Term should have been eliminated by [Prepare_lambda]: %a"
      Printlambda.lambda lam

and name_then_cps_non_tail name lam k =
  let var = Ident.create name in
  cps_non_tail (Llet (Strict, Pgenval, var, lam, Lvar var)) k

and name_then_cps_tail name lam k =
  let var = Ident.create name in
  cps_tail (Llet (Strict, Pgenval, var, lam, Lvar var)) k

and cps_non_tail_list (lams : L.lambda list) (k : Ident.t list -> Ilambda.t) =
  match lams with
  | [] -> k []
  | lam::lams ->
    cps_non_tail lam (fun id ->
      cps_non_tail_list lams (fun lams -> k (lam::lams)))

and cps_function (func : Lambda.lfunction) : Ilambda.t =
  let body_cont = Continuation.create () in
  let free_idents_of_body = Lambda.free_variables func.body in
  let body = cps_tail func.body body_cont in
  let func : Ilambda.function_declaration =
    { kind = func.kind;
      continuation_param = body_cont;
      params = func.params;
      body;
      attr = func.attr;
      loc = func.loc;
      free_idents_of_body;
    }
  in
  Function func

and cps_switch (switch : proto_switch) ~scrutinee (k : Continuation.t) =
  let const_nums, consts = List.split switch.consts in
  let const_conts = List.map (fun _ -> Continuation.create ()) consts in
  let block_conts = List.map (fun _ -> Continuation.create ()) switch.blocks in
  let consts =
    List.combine const_nums (List.combine consts const_conts)
  in
  let blocks =
    List.combine switch.block_pats (List.combine switch.blocks block_conts)
  in
  let failaction_cont, failaction =
    match switch.failaction with
    | None -> None, None
    | Some failaction ->
      let cont = Continuation.create () in
      Some cont, Some (cont, failaction)
  in
  let switch : Ilambda.switch =
    { numconsts = switch.numconsts;
      consts = const_conts;
      numblocks = switch.numblocks;
      blocks = block_conts;
      failaction;
    }
  in
  cps_non_tail scrutinee (fun scrutinee ->
    let case_continuations =
      List.fold_right (fun (case, cont) acc ->
          I.Let_cont (cont, [], cps_tail case k, acc))
        (consts @ blocks)
        (I.Switch (scrutinee, switch))
    in
    match failaction with
    | None -> case_continuations
    | Some (cont, failaction) ->
      I.Let_cont (cont, [], cps_tail failaction k, case_continuations))

let lambda_to_ilambda lam =
  cps_tail lam (fun id -> I.Var id)
