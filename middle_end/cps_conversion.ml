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

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module I = Ilambda
module L = Lambda

(** "Use CPS".
    -- A. Kennedy, "Compiling with Continuations Continued", ICFP 2007.
*)

let rec cps_non_tail (lam : L.lambda) (k : Ident.t -> Ilambda.t) : Ilambda.t =
  match lam with
  | Lvar id -> k id
  | Lconst const ->
    let var = Ident.create "const" in
    cps_non_tail (Llet (Strict, Pgenval, var, Lconst const, Lvar var)) k
  | Lapply apply ->
    cps apply.ap_func ~is_tail:false (fun func ->
      cps_list apply.ap_args ~is_tail:false (fun args ->
        let continuation = Continuation.create () in
        let result_var = Ident.create "apply_result" in
        let after = k result_var in
        let apply : Ilambda.apply = {
          func;
          continuation;
          args;
          loc = apply.ap_loc;
          should_be_tailcall = apply.ap_should_be_tailcall;
          inlined = apply.ap_inlined;
          specialised = apply.ap_specialised;
        } in
        I.Let_cont (continuation, [result_var], after, Apply apply)))
  | Lfunction func -> cps_function func
  (* The following specialised Llet cases help to avoid administrative
     redexes. *)
  | Llet (let_kind, value_kind, id, (Lvar id) as defining_expr, body) ->
    I.Let (let_kind, value_kind, id, I.Var id, cps_non_tail body k)
  | Llet (let_kind, value_kind, id, (Lconst const) as defining_expr, body) ->
    I.Let (let_kind, value_kind, id, I.Const const, cps_non_tail body k)
  | Llet (let_kind, value_kind, id, Lfunction func, body) ->
    let func = cps_function func in
    I.Let (let_kind, value_kind, id, func, body)
  | Llet (let_kind, value_kind, id, Lprim (prim, args, loc), body) ->
    let body = cps_non_tail body k in
    cps_non_tail_list args (fun args ->
      I.Let (Strict, Pgenval, id, I.Prim (prim, args, loc), body))
  | Llet (let_kind, value_kind, id, defining_expr, body) ->
    let body = cps_non_tail body k in
    let after_body = Continuation.create () in
    let defining_expr = cps_tail defining_expr after_body in
    I.Let_cont (after_body, [id], body, defining_expr)
  | Lletrec (bindings, body) ->
    let idents, bindings = List.split bindings in
    let bindings =
      List.map (fun (binding : Lambda.lambda) ->
          match binding with
          | Lfunction func -> cps_function func
          | _ ->
            Misc.fatal_error "Only [Lfunction] expressions are permitted in \
                [Lletrec] bindings upon entry to CPS conversion: %a"
              binding)
        bindings
    in
    I.Let_rec (List.combine idents bindings)
  | Lprim (prim, args, loc) ->
    let result_var = Ident.create "prim_result" in
    cps_non_tail_list args (fun args ->
      I.Let (Strict, Pgenval, result_var, I.Prim (prim, args, loc), result))

  | Lswitch (scrutinee, switch) ->
    cps_non_tail scrutinee (fun scrutinee ->
      let const_nums, consts = List.split switch.sw_consts in
      let block_nums, blocks = List.split switch.sw_blocks in
      cps_option switch.sw_failaction ~is_tail (fun failaction ->
        cps_list consts ~is_tail (fun consts ->
          cps_list blocks ~is_tail (fun blocks ->
            let switch : Ilambda.switch =
              { numconsts = switch.sw_numconsts;
                consts = List.combine const_nums consts;
                numblocks = switch.sw_numblocks;
                blocks = List.combine block_nums blocks;
                failaction;
              }
            in
            k (I.Switch (scrutinee, switch))))))
  | Lstringswitch (scrutinee, cases, default, loc) ->
    cps scrutinee ~is_tail:false (fun scrutinee ->
      let patterns, cases = List.split cases in
      cps_list cases ~is_tail (fun cases ->
        let cases = List.combine patterns cases in
        cps_option default ~is_tail (fun default ->
          k (I.String_switch (scrutinee, cases, default, loc)))))
  | Lstaticraise (cont, args) ->
    cps_list args ~is_tail:false (fun args ->
      k (I.Apply_cont (cont, args)))
  | Lstaticcatch (body, (cont, args), handler) ->


    cps body ~is_tail (fun body ->
      cps handler ~is_tail (fun handler ->
        k (I.Let_cont (cont, args, ..., ...))))

  | Ltrywith (body, id, handler) ->
    cps body ~is_tail:false (fun body ->
      cps handler ~is_tail (fun handler ->
        k (I.Try_with (body, id, handler))))

  | Lifthenelse (cond, ifso, ifnot) ->
    let join_cont = Continuation.create () in
    let result_var = Ident.create "ifthenelse_result" in
    let ifso_cont = Continuation.create () in
    let ifnot_cont = Continuation.create () in
    cps_non_tail cond (fun cond ->
      let ifso = cps_tail ifso join_cont in
      let ifnot = cps_tail ifnot join_cont in
      I.Let_cont (join_cont, [result_var], k result_var,
        I.Let_cont (ifso_cont, [], ifso,
          I.Let_cont (ifnot_cont, [], ifnot,
            I.If_then_else (cond, ifso_cont, ifnot_cont)))))

  | Lsequence _ | Lwhile _ | Lfor _ | Lassign _ | Lifused _ ->
    Misc.fatal_errorf "Term should have been eliminated by [Prepare_lambda]: %a"
      Printlambda.lambda lam

and cps_list (lams : L.lambda list) ~is_tail (k : Variable.t list -> _) =
  match lams with
  | [] -> k []
  | lam::lams ->
    cps lam ~is_tail (fun lam ->
      cps_list lams ~is_tail (fun lams -> k (lam::lams)))

and cps_option lam_opt ~is_tail k =
  match lam_opt with
  | None -> k None
  | Some lam -> cps lam ~is_tail (fun lam -> k (Some lam))

and cps_tail (lam : L.lambda) (k : Continuation.t) =
  match lam with
  | Lvar _ ->
  | Lconst _ ->
  | Lapply apply ->
  | Lfunction func ->
  | Llet (let_kind, value_kind, id, defining_expr, body) ->
  | Lletrec (bindings, body) ->
  | Lprim (prim, args, loc) ->
  | Lswitch (scrutinee, switch) ->
  | Lstringswitch (scrutinee, cases, default, loc) ->
  | Lstaticraise (cont, args) ->
  | Lstaticcatch (body, (cont, args), handler) ->
  | Ltrywith (body, id, handler) ->
  | Lifthenelse (cond, ifso, ifnot) ->
  | Lsequence _ | Lwhile _ | Lfor _ | Lassign _ | Lifused _ ->
    Misc.fatal_errorf "Term should have been eliminated by [Prepare_lambda]: %a"
      Printlambda.lambda lam

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

let lambda_to_ilambda lam =
  let lam = add_default_argument_wrappers lam in
  cps lam ~is_tail:true (fun ilam -> ilam)
