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

module L = Lambda

let add_default_argument_wrappers lam =
  (* CR-someday mshinwell: Temporary hack to mark default argument wrappers
     as stubs.  Other possibilities:
     1. Change L.inline_attribute to add another ("stub") case;
     2. Add a "stub" field to the Lfunction record. *)
  let stubify body : L.lambda =
    let stub_prim =
      Primitive.simple ~name:Closure_conversion_aux.stub_hack_prim_name
        ~arity:1 ~alloc:false
    in
    Lprim (Pccall stub_prim, [body], Location.none)
  in
  let defs_are_all_functions (defs : (_ * L.lambda) list) =
    List.for_all (function (_, L.Lfunction _) -> true | _ -> false) defs
  in
  let f (lam : L.lambda) : L.lambda =
    match lam with
    | Llet (( Strict | Alias | StrictOpt), _k, id,
        Lfunction {kind; params; body = fbody; attr; loc}, body) ->
      begin match
        Simplif.split_default_wrapper id kind params fbody attr loc
          ~create_wrapper_body:stubify
      with
      | [fun_id, def] -> Llet (Alias, Pgenval, fun_id, def, body)
      | [fun_id, def; inner_fun_id, def_inner] ->
        Llet (Alias, Pgenval, inner_fun_id, def_inner,
              Llet (Alias, Pgenval, fun_id, def, body))
      | _ -> assert false
      end
    | Lletrec (defs, body) as lam ->
      if defs_are_all_functions defs then
        let defs =
          List.flatten
            (List.map
               (function
                 | (id, L.Lfunction {kind; params; body; attr; loc}) ->
                   Simplif.split_default_wrapper id kind params body attr loc
                     ~create_wrapper_body:stubify
                 | _ -> assert false)
               defs)
        in
        Lletrec (defs, body)
      else lam
    | lam -> lam
  in
  L.map f lam

type rhs_kind =
  | Block of int
  | Floatblock of int
  | Nonrec

let rec expr_size env = function
  | Uvar id ->
      begin try Ident.find_same id env with Not_found -> Nonrec end
  | Uclosure(fundecls, clos_vars) ->
      Block (fundecls_size fundecls + List.length clos_vars)
  | Ulet(_str, _kind, id, exp, body) ->
      expr_size (Ident.add id (expr_size env exp) env) body
  | Uletrec(_bindings, body) ->
      expr_size env body
  | Uprim(Pmakeblock _, args, _) ->
      Block (List.length args)
  | Uprim(Pmakearray((Paddrarray | Pintarray), _), args, _) ->
      Block (List.length args)
  | Uprim(Pmakearray(Pfloatarray, _), args, _) ->
      Floatblock (List.length args)
  | Uprim (Pduprecord ((Record_regular | Record_inlined _), sz), _, _) ->
      Block sz
  | Uprim (Pduprecord (Record_unboxed _, _), _, _) ->
      assert false
  | Uprim (Pduprecord (Record_extension, sz), _, _) ->
      Block (sz + 1)
  | Uprim (Pduprecord (Record_float, sz), _, _) ->
      Floatblock sz
  | Uprim (Pccall { prim_name; _ }, closure::_, _)
        when prim_name = "caml_check_value_is_closure" ->
      (* Used for "-clambda-checks". *)
      expr_size env closure
  | Usequence(_exp, exp') ->
      expr_size env exp'
  | _ -> Nonrec

let dissect_letrec ~bindings ~body =
  let dbg = Debuginfo.none in
  let bsz =
    List.map (fun (id, exp) -> (id, exp, expr_size Ident.empty exp))
      bindings
  in
  let op_alloc prim sz =
    Cop(Cextcall(prim, typ_val, true, None), [int_const sz], dbg) in
  let rec init_blocks = function
    | [] -> fill_nonrec bsz
    | (id, _exp, RHS_block sz) :: rem ->
        Clet(id, op_alloc "caml_alloc_dummy" sz,
          init_blocks rem)
    | (id, _exp, RHS_floatblock sz) :: rem ->
        Clet(id, op_alloc "caml_alloc_dummy_float" sz,
          init_blocks rem)
    | (id, _exp, RHS_nonrec) :: rem ->
        Clet (id, Cconst_int 0, init_blocks rem)
  and fill_nonrec = function
    | [] -> fill_blocks bsz
    | (_id, _exp, (RHS_block _ | RHS_floatblock _)) :: rem ->
        fill_nonrec rem
    | (id, exp, RHS_nonrec) :: rem ->
        Clet(id, transl env exp, fill_nonrec rem)
  and fill_blocks = function
    | [] -> cont
    | (id, exp, (RHS_block _ | RHS_floatblock _)) :: rem ->
        let op =
          Cop(Cextcall("caml_update_dummy", typ_void, false, None),
              [Cvar id; transl env exp], dbg) in
        Csequence(op, fill_blocks rem)
    | (_id, _exp, RHS_nonrec) :: rem ->
        fill_blocks rem
  in init_blocks bsz

let rec prepare (lam : L.lambda) (k : L.lambda -> L.lambda) =
  match lam with
  | Lvar _
  | Lconst _ -> k lam
  | Lapply apply ->
    prepare apply.ap_func (fun ap_func ->
      prepare_list apply.ap_args (fun ap_args ->
        k (L.Lapply {
          ap_func;
          ap_args;
          ap_loc = apply.ap_loc;
          ap_should_be_tailcall = apply.ap_should_be_tailcall;
          ap_inlined = apply.ap_inlined;
          ap_specialised = apply.ap_specialised;
        })))
  | Lfunction func ->
    prepare func.body (fun body ->
      k (L.Lfunction {
        kind = func.kind;
        params = func.params;
        body;
        attr = func.attr;
        loc = func.loc;
        free_idents_of_body;
      }))
  | Llet (let_kind, value_kind, id, defining_expr, body) ->
    prepare defining_expr (fun defining_expr ->
      prepare body (fun body ->
        k (L.Llet (let_kind, value_kind, id, defining_expr, body))))
  | Lletrec (bindings, body) ->
    let idents, bindings = List.split bindings in
    prepare_list bindings (fun bindings ->
      let bindings = List.combine idents bindings in
      prepare body (fun body ->
        k (dissect_letrec ~bindings ~body)))
  | Lprim (prim, args, loc) ->
    prepare_list args (fun args ->
      k (L.Lprim (prim, args, loc)))
  | Lswitch (scrutinee, switch) ->
    prepare scrutinee (fun scrutinee ->
      let const_nums, sw_consts = List.split switch.sw_consts in
      let block_nums, sw_blocks = List.split switch.sw_blocks in
      prepare_option switch.sw_failaction (fun sw_failaction ->
        prepare_list sw_consts (fun sw_consts ->
          prepare_list sw_blocks (fun sw_blocks ->
            let switch : L.lambda_switch =
              { sw_numconsts = switch.sw_numconsts;
                sw_consts = List.combine const_nums sw_consts;
                sw_numblocks = switch.sw_numblocks;
                sw_blocks = List.combine block_nums sw_blocks;
                sw_failaction;
              }
            in
            k (L.Lswitch (scrutinee, switch))))))
  | Lstringswitch (scrutinee, cases, default, loc) ->
    prepare scrutinee (fun scrutinee ->
      let patterns, cases = List.split cases in
      prepare_list cases (fun cases ->
        let cases = List.combine patterns cases in
        prepare_option default (fun default ->
          k (L.Lstringswitch (scrutinee, cases, default, loc)))))
  | Lstaticraise (cont, args) ->
    prepare_list args (fun args ->
      k (L.Lstaticraise (cont, args)))
  | Lstaticcatch (body, (cont, args), handler) ->
    prepare body (fun body ->
      prepare handler (fun handler ->
        k (L.Lstaticcatch (body, cont, args, handler))))
  | Ltrywith (body, id, handler) ->
    prepare body (fun body ->
      prepare handler (fun handler ->
        k (L.Ltrywith (body, id, handler))))
  | Lifthenelse (cond, ifso, ifnot) ->
    prepare cond (fun cond ->
      prepare ifso (fun ifso ->
        prepare ifnot (fun ifnot ->
          let switch : Lambda.lambda_switch =
            { sw_numconsts = 1;
              sw_consts = [0, ifnot];
              sw_numblocks = 0;
              sw_blocks = [];
              sw_failaction = Some ifso;
            }
          in
          Lswitch (cond, switch))))
  | Lsequence (lam1, lam2) ->
    let ident = Ident.create "sequence" in
    prepare (L.Llet (Strict, Pgenval, ident, lam1, lam2)) k
  | Lwhile (cond, body) ->
    let cont = L.next_raise_count () in
    let cond_result = Ident.create "cond_result" in
    let lam : L.lambda =
      Lstaticcatch (
        Lstaticraise (cont, []),
        (cont, []),
        Llet (Strict, Pgenval, cond_result, cond,
          Lifthenelse (Lvar cond_result,
            Lsequence (
              body,
              Lstaticraise (cont, [])),
            Lconst (Const_base (Const_int 0)))))
    in
    prepare lam k
  | Lfor (ident, start, stop, dir, body) ->
    let loc = Location.none in
    let cont = L.next_raise_count () in
    let stop_ident = Ident.create "stop" in
    let test =
      match dir with
      | Upto -> L.Lprim (Pintcomp Cle, [L.Lvar ident; L.Lvar stop_ident], loc)
      | Downto -> L.Lprim (Pintcomp Cge, [L.Lvar ident; L.Lvar stop_ident], loc)
    in
    let one : L.lambda = Lconst (Const_base (Const_int 1)) in
    let next_value_of_counter =
      match dir with
      | Upto -> L.Lprim (Paddint, [L.Lvar ident; one], loc)
      | Downto -> L.Lprim (Psubint, [L.Lvar ident; one], loc)
    in
    let lam : L.lambda =
      (* CR mshinwell: check evaluation order of start vs. end *)
      Llet (Strict, Pgenval, stop_ident, stop,
        Lstaticcatch (
          Lstaticraise (cont, [start]),
          (cont, [ident]),
          Lifthenelse (test,
            Lsequence (
              body,
              Lstaticraise (cont, [next_value_of_counter])),
            Lconst (Const_base (Const_int 0)))))
    in
    prepare lam k
  | Lassign _ ->
    Misc.fatal_error "Lassign is never expected in the Flambda middle end"
  | Lsend (meth_kind, meth, obj, args, loc) ->
    prepare meth (fun meth ->
      prepare obj (fun obj ->
        prepare_list args (fun args ->
          k (L.Lsend (meth_kind, meth, obj, args, loc)))))
  | Levent (body, event) ->
    prepare body (fun body ->
      k (L.Levent (body, event)))
  | Lifused _ ->
    (* [Lifused] is used to mark that this expression should be alive only if
       an identifier is.  Every use should have been removed by
       [Simplif.simplify_lets], either by replacing by the inner expression,
       or by completely removing it (replacing by unit). *)
    Misc.fatal_error "[Lifused] should have been removed by \
        [Simplif.simplify_lets]"

and prepare_list lams k =
  match lams with
  | [] -> k []
  | lam::lams ->
    prepare lam (fun lam ->
      prepare_list lams (fun lams -> k (lam::lams)))

and prepare_option lam_opt k =
  match lam_opt with
  | None -> k None
  | Some lam -> prepare lam (fun lam -> k (Some lam))

let run lam =
  let lam = add_default_argument_wrappers lam in
  prepare lam (fun lam -> lam)
