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
        Misc.fatal_errorf "Only [Lfunction] expressions are permitted in \
            [Lletrec] bindings upon entry to CPS conversion: %a"
          Printlambda.lambda binding)
    bindings

let name_for_function (func : Lambda.lfunction) =
  (* Name anonymous functions by their source location, if known. *)
  if func.loc = Location.none then "anon-fn"
  else Format.asprintf "anon-fn[%a]" Location.print_compact func.loc

(* CR-soon mshinwell: Remove mutable state. *)
let static_exn_env = ref Numbers.Int.Map.empty

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
        I.Let_cont {
          name = continuation;
          params = [result_var];
          recursive = Nonrecursive;
          body = Apply apply;
          handler = after;
       }))
  | Lfunction func -> name_then_cps_non_tail (name_for_function func) lam k
  | Llet (Variable, value_kind, id, defining_expr, body) ->
    let temp_id = Ident.create "let_mutable" in
    let body = cps_non_tail body k in
    let after_defining_expr = Continuation.create () in
    let defining_expr = cps_tail defining_expr after_defining_expr in
    let let_mutable : I.let_mutable =
      { id;
        initial_value = temp_id;
        contents_kind = value_kind;
        body;
      }
    in
    Let_cont {
      name = after_defining_expr;
      params = [temp_id];
      recursive = Nonrecursive;
      body = defining_expr;
      handler = Let_mutable let_mutable;
   }
  (* The following specialised Llet cases help to avoid administrative
     redexes. *)
  | Llet (_let_kind, _value_kind, id, Lvar id', body) ->
    Let (id, Var id', cps_non_tail body k)
  | Llet (_let_kind, _value_kind, id, Lconst const, body) ->
    Let (id, Const const, cps_non_tail body k)
  | Llet (_let_kind, _value_kind, id, Lfunction func, body) ->
    let func = cps_function func in
    let body = cps_non_tail body k in
    Let (id, Function func, body)
  | Llet (_let_kind, _value_kind, id, Lprim (prim, args, loc), body) ->
    let body = cps_non_tail body k in
    cps_non_tail_list args (fun args ->
      I.Let (id, Prim (prim, args, loc), body))
  | Llet (_let_kind, _value_kind, id, defining_expr, body) ->
    (* CR-soon mshinwell / pchambart: keep value_kind in Ilambda and Flambda *)
    let body = cps_non_tail body k in
    let after_defining_expr = Continuation.create () in
    let defining_expr = cps_tail defining_expr after_defining_expr in
    Let_cont {
      name = after_defining_expr;
      params = [id];
      recursive = Nonrecursive;
      body = defining_expr;
      handler = body;
    }
  | Lletrec (bindings, body) ->
    let idents, bindings = List.split bindings in
    let bindings = List.map cps_function (check_let_rec_bindings bindings) in
    let body = cps_non_tail body k in
    Let_rec (List.combine idents bindings, body)
  | Lprim (prim, args, loc) ->
    let name = Printlambda.name_of_primitive prim in
    let result_var = Ident.create name in
    cps_non_tail_list args (fun args ->
      I.Let (result_var, Prim (prim, args, loc), k result_var))
  | Lswitch (scrutinee, switch) ->
    let after_switch = Continuation.create () in
    let result_var = Ident.create "switch_result" in
    let after = k result_var in
    let block_nums, blocks = List.split switch.sw_blocks in
    let block_pats = List.map (fun tag -> I.Tag tag) block_nums in
    let proto_switch : proto_switch =
      { numconsts = switch.sw_numconsts;
        consts = switch.sw_consts;
        numblocks = switch.sw_numblocks;
        block_pats;
        blocks;
        failaction = switch.sw_failaction;
      }
    in
    Let_cont {
      name = after_switch;
      params = [result_var];
      recursive = Nonrecursive;
      body = cps_switch proto_switch ~scrutinee after_switch;
      handler = after;
    }
  | Lstringswitch (scrutinee, cases, default, _loc) ->
    (* CR mshinwell: don't discard [loc] *)
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
    Let_cont {
      name = after_switch;
      params = [result_var];
      recursive = Nonrecursive;
      body = cps_switch proto_switch ~scrutinee after_switch;
      handler = after;
    }
  | Lstaticraise (static_exn, args) ->
    let continuation =
      match Numbers.Int.Map.find static_exn !static_exn_env with
      | exception Not_found ->
        Misc.fatal_errorf "Unbound static exception %d" static_exn
      | continuation -> continuation
    in
    cps_non_tail_list args (fun args -> I.Apply_cont (continuation, args))
  | Lstaticcatch (body, (static_exn, args), handler) ->
    let continuation = Continuation.create () in
    static_exn_env := Numbers.Int.Map.add static_exn continuation
      !static_exn_env;
    let after_continuation = Continuation.create () in
    let result_var = Ident.create "staticcatch_result" in
    let body = cps_tail body after_continuation in
    let handler = cps_tail handler after_continuation in
    Let_cont {
      name = after_continuation;
      params = [];
      recursive = Nonrecursive;
      body =
        Let_cont  {
          name = continuation;
          params = args;
          (* CR-someday mshinwell: Maybe we could improve this by communicating
             from [Prepare_lambda] which catches are recursive. *)
          recursive = Recursive;
          body;
          handler;
        };
      handler = k result_var;
    };
  | Lsend (meth_kind, meth, obj, args, loc) ->
    cps_non_tail obj (fun obj ->
      cps_non_tail meth (fun meth ->
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
          I.Let_cont {
            name = continuation;
            params = [result_var];
            recursive = Nonrecursive;
            body = after;
            handler = Apply apply;
          })))
  | Levent (lam, event) -> Event (cps_non_tail lam k, event)
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
          kind = Function;
          func;
          continuation = k;
          args;
          loc = apply.ap_loc;
          should_be_tailcall = apply.ap_should_be_tailcall;
          inlined = apply.ap_inlined;
          specialised = apply.ap_specialised;
        } in
        I.Apply apply))
  | Lfunction func -> name_then_cps_tail (name_for_function func) lam k
  | Llet (Variable, value_kind, id, defining_expr, body) ->
    let temp_id = Ident.create "let_mutable" in
    let body = cps_tail body k in
    let after_defining_expr = Continuation.create () in
    let defining_expr = cps_tail defining_expr after_defining_expr in
    let let_mutable : I.let_mutable =
      { id;
        initial_value = temp_id;
        contents_kind = value_kind;
        body;
      }
    in
    Let_cont {
      name = after_defining_expr;
      params = [temp_id];
      recursive = Nonrecursive;
      body = defining_expr;
      handler = Let_mutable let_mutable;
    }
  (* The following specialised Llet cases help to avoid administrative
     redexes. *)
  | Llet (_let_kind, _value_kind, id, Lvar id', body) ->
    Let (id, Var id', cps_tail body k)
  | Llet (_let_kind, _value_kind, id, Lconst const, body) ->
    Let (id, Const const, cps_tail body k)
  | Llet (_let_kind, _value_kind, id, Lfunction func, body) ->
    let func = cps_function func in
    let body = cps_tail body k in
    Let (id, Function func, body)
  | Llet (_let_kind, _value_kind, id, Lprim (prim, args, loc), body) ->
    let body = cps_tail body k in
    cps_non_tail_list args (fun args ->
      I.Let (id, Prim (prim, args, loc), body))
  | Llet (_let_kind, _value_kind, id, defining_expr, body) ->
    let body = cps_tail body k in
    let after_defining_expr = Continuation.create () in
    let defining_expr = cps_tail defining_expr after_defining_expr in
    Let_cont {
      name = after_defining_expr;
      params = [id];
      recursive = Nonrecursive;
      body = defining_expr;
      handler = body;
    }
  | Lletrec (bindings, body) ->
    let idents, bindings = List.split bindings in
    let bindings = List.map cps_function (check_let_rec_bindings bindings) in
    let body = cps_tail body k in
    Let_rec (List.combine idents bindings, body)
  | Lprim (prim, args, loc) ->
    (* CR mshinwell: Arrange for "args" to be named. *)
    let name = Printlambda.name_of_primitive prim in
    let result_var = Ident.create name in
    cps_non_tail_list args (fun args ->
      I.Let (result_var, Prim (prim, args, loc), Apply_cont (k, [result_var])))
  | Lswitch (scrutinee, switch) ->
    let block_nums, blocks = List.split switch.sw_blocks in
    let block_pats = List.map (fun tag -> I.Tag tag) block_nums in
    let proto_switch : proto_switch =
      { numconsts = switch.sw_numconsts;
        consts = switch.sw_consts;
        numblocks = switch.sw_numblocks;
        block_pats;
        blocks;
        failaction = switch.sw_failaction;
      }
    in
    cps_switch proto_switch ~scrutinee k
  | Lstringswitch (scrutinee, cases, default, _loc) ->
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
  | Lstaticraise (static_exn, args) ->
    let continuation =
      match Numbers.Int.Map.find static_exn !static_exn_env with
      | exception Not_found ->
        Misc.fatal_errorf "Unbound static exception %d" static_exn
      | continuation -> continuation
    in
    cps_non_tail_list args (fun args -> I.Apply_cont (continuation, args))
  | Lstaticcatch (body, (static_exn, args), handler) ->
    let continuation = Continuation.create () in
    static_exn_env := Numbers.Int.Map.add static_exn continuation
      !static_exn_env;
    let body = cps_tail body k in
    let handler = cps_tail handler k in
    Let_cont  {
      name = continuation;
      params = args;
      recursive = Recursive;  (* see CR comment above *)
      body;
      handler;
    };
  | Lsend (meth_kind, meth, obj, args, loc) ->
    cps_non_tail obj (fun obj ->
      cps_non_tail meth (fun meth ->
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
          I.Apply apply)))
  | Levent (lam, event) -> Event (cps_tail lam k, event)
  | Lsequence _ | Lifthenelse _ | Lwhile _ | Lfor _ | Lassign _ | Lifused _
  | Ltrywith _ ->
    Misc.fatal_errorf "Term should have been eliminated by [Prepare_lambda]: %a"
      Printlambda.lambda lam

and name_then_cps_non_tail name lam k =
  let var = Ident.create name in
  cps_non_tail (L.Llet (Strict, Pgenval, var, lam, Lvar var)) k

and name_then_cps_tail name lam k =
  let var = Ident.create name in
  cps_tail (L.Llet (Strict, Pgenval, var, lam, Lvar var)) k

and cps_non_tail_list (lams : L.lambda list) (k : Ident.t list -> Ilambda.t) =
  let lams = List.rev lams in  (* Always evaluate right-to-left. *)
  match lams with
  | [] -> k []
  | lam::lams ->
    cps_non_tail lam (fun id ->
      cps_non_tail_list lams (fun ids -> k (id::ids)))

and cps_function (func : Lambda.lfunction) : Ilambda.function_declaration =
  let body_cont = Continuation.create () in
  let free_idents_of_body = Lambda.free_variables func.body in
  let body = cps_tail func.body body_cont in
  { kind = func.kind;
    continuation_param = body_cont;
    params = func.params;
    body;
    attr = func.attr;
    loc = func.loc;
    free_idents_of_body;
  }

and cps_switch (switch : proto_switch) ~scrutinee (k : Continuation.t) =
  let const_nums, consts = List.split switch.consts in
  let const_conts = List.map (fun _ -> Continuation.create ()) consts in
  let block_conts = List.map (fun _ -> Continuation.create ()) switch.blocks in
  let consts = List.combine consts const_conts in
  let blocks = List.combine switch.blocks block_conts in
  let failaction_cont, failaction =
    match switch.failaction with
    | None -> None, None
    | Some failaction ->
      let cont = Continuation.create () in
      Some cont, Some (cont, failaction)
  in
  let switch : Ilambda.switch =
    { numconsts = switch.numconsts;
      consts = List.combine const_nums const_conts;
      numblocks = switch.numblocks;
      blocks = List.combine switch.block_pats block_conts;
      failaction = failaction_cont;
    }
  in
  cps_non_tail scrutinee (fun scrutinee ->
    let make_continuations desc ~init =
      List.fold_right (fun (case, cont) acc ->
          I.Let_cont {
            name = cont;
            params = [];
            recursive = Nonrecursive;
            body = acc;
            handler = cps_tail case k
          })
        desc
        init
    in
    let body = I.Switch (scrutinee, switch) in
    let init =
      match failaction with
      | None -> body
      | Some (cont, failaction) ->
        I.Let_cont {
          name = cont;
          params = [];
          recursive = Nonrecursive;
          body;
          handler = cps_tail failaction k;
        }
    in
    make_continuations consts ~init:(make_continuations blocks ~init))

let lambda_to_ilambda lam =
  static_exn_env := Numbers.Int.Map.empty;
  let the_end = Continuation.create () in
  cps_tail lam the_end, the_end
