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

let rec cps (lam : L.lambda) ~is_tail k =
  match lam with
  | Lvar id -> k (I.Var id)
  | Lconst const -> k (I.Const const)
  | Lapply apply ->
    cps apply.ap_func ~is_tail:false (fun func ->
      cps_list apply.ap_args ~is_tail:false (fun args ->
        k (I.Apply {
          func;
          args;
          loc = apply.ap_loc;
          should_be_tailcall = apply.ap_should_be_tailcall;
          inlined = apply.ap_inlined;
          specialised = apply.ap_specialised;
        })))
  | Lfunction func ->
    let free_idents_of_body = Lambda.free_variables func.body in
    cps func.body ~is_tail (fun body ->
      k (I.Function {
        kind = func.kind;
        params = func.params;
        body;
        attr = func.attr;
        loc = func.loc;
        free_idents_of_body;
      }))
  | Llet (let_kind, value_kind, id, defining_expr, body) ->
    cps defining_expr ~is_tail:false (fun defining_expr ->
      cps body ~is_tail (fun body ->
        I.Let (let_kind, value_kind, id, defining_expr, body)))
  | Lletrec (bindings, body) ->
    let idents, bindings = List.split bindings in
    cps_list bindings ~is_tail:false (fun bindings ->
      let bindings = List.combine idents bindings in
      cps body ~is_tail (fun body ->
        I.Let_rec (bindings, body)))
  | Lprim (prim, args, loc) ->
    cps_list args ~is_tail:false (fun args ->
      k (I.Prim (prim, args, loc)))
  | Lswitch (scrutinee, switch) ->
    cps scrutinee ~is_tail:false (fun scrutinee ->
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
        k (I.Let_cont (body, cont, args, handler))))
  | Ltrywith (body, id, handler) ->
    cps body ~is_tail:false (fun body ->
      cps handler ~is_tail (fun handler ->
        k (I.Try_with (body, id, handler))))
  | Lifthenelse (cond, ifso, ifnot) ->
    cps cond ~is_tail:false (fun cond ->
      cps ifso ~is_tail (fun ifso ->
        cps ifnot ~is_tail (fun ifnot ->
          k (I.If_then_else (cond, ifso, ifnot)))))
  | Lsequence (lam1, lam2) ->
    let ident = Ident.create "sequence" in
    cps (L.Llet (Strict, Pgenval, ident, lam1, lam2)) ~is_tail k
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
    cps lam k ~is_tail
  | Lfor (ident, start, stop, dir, body) ->
    let loc = Location.none in
    let cont = L.next_raise_count () in
    let test =
      match dir with
      | Upto -> L.Lprim (Pintcomp Cle, [L.Lvar ident; stop], loc)
      | Downto -> L.Lprim (Pintcomp Cge, [L.Lvar ident; stop], loc)
    in
    let one : L.lambda = Lconst (Const_base (Const_int 1)) in
    let next_value_of_counter =
      match dir with
      | Upto -> L.Lprim (Paddint, [L.Lvar ident; one], loc)
      | Downto -> L.Lprim (Psubint, [L.Lvar ident; one], loc)
    in
    let lam : L.lambda =
      Lstaticcatch (
        Lstaticraise (cont, [start]),
        (cont, []),
        Lifthenelse (test,
          Lsequence (
            body,
            Lstaticraise (cont, [next_value_of_counter])),
          Lconst (Const_base (Const_int 0))))
    in
    cps lam k ~is_tail
  | Lassign _ ->
    Misc.fatal_error "Lassign is never expected in the Flambda middle end"
  | Lsend (meth_kind, meth, obj, args, loc) ->
    cps meth ~is_tail:false (fun meth ->
      cps obj ~is_tail:false (fun obj ->
        cps_list args ~is_tail:false (fun args ->
          k (I.Send (meth_kind, meth, obj, args, loc)))))
  | Levent (body, event) ->
    cps body ~is_tail (fun body ->
      k (I.Event (body, event)))
  | Lifused _ ->
    (* [Lifused] is used to mark that this expression should be alive only if
       an identifier is.  Every use should have been removed by
       [Simplif.simplify_lets], either by replacing by the inner expression,
       or by completely removing it (replacing by unit). *)
    Misc.fatal_error "[Lifused] should have been removed by \
        [Simplif.simplify_lets]"

and cps_list lams ~is_tail k =
  match lams with
  | [] -> k []
  | lam::lams ->
    cps lam ~is_tail (fun lam ->
      cps_list lams ~is_tail (fun lams -> k (lam::lams)))

and cps_option lam_opt ~is_tail k =
  match lam_opt with
  | None -> k None
  | Some lam -> cps lam ~is_tail (fun lam -> k (Some lam))

let lambda_to_ilambda lam =
  let lam = add_default_argument_wrappers lam in
  cps lam ~is_tail:true (fun ilam -> ilam)
