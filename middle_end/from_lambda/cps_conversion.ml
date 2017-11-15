(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2016--2017 OCamlPro SAS                                    *)
(*   Copyright 2016--2017 Jane Street Group LLC                           *)
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
let try_stack = ref []
let try_stack_at_handler = ref Continuation.Map.empty

let _print_stack ppf stack =
  Format.fprintf ppf "%a"
    (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ")
      (fun ppf (_id, cont) -> Format.fprintf ppf "%a" Continuation.print cont))
    stack

(* Uses of [Lstaticfail] that jump out of try-with handlers need special care:
   the correct number of pop trap operations must be inserted. *)
let compile_staticfail ~(continuation : Continuation.t) ~args =
  let try_stack_at_handler =
    match Continuation.Map.find continuation !try_stack_at_handler with
    | exception Not_found ->
      Misc.fatal_errorf "No try stack recorded for handler %a"
        Continuation.print continuation
    | stack -> stack
  in
  let try_stack_now = !try_stack in
(*
Format.eprintf "staticfail now %a handler %a\n%!"
  print_stack try_stack_now
  print_stack try_stack_at_handler;
*)
  if List.length try_stack_at_handler > List.length try_stack_now then begin
    Misc.fatal_errorf "Cannot jump to continuation %a: it would involve \
        jumping into a try-with body"
      Continuation.print continuation
  end;
  assert (Continuation.Set.subset
    (Continuation.Set.of_list (List.map snd try_stack_at_handler))
    (Continuation.Set.of_list (List.map snd try_stack_now)));
  let outer_wrapper_cont = Continuation.create () in
  let rec add_pop_traps ~prev_cont ~body ~try_stack_now ~try_stack_at_handler =
    let add_pop id cont ~try_stack_now =
      let wrapper_cont = Continuation.create () in
      let trap_action : I.trap_action =
        Pop { id; exn_handler = cont; }
      in
      let body =
        match body with
        | Some body -> body
        | None -> I.Apply_cont (wrapper_cont, None, [])
      in
      let body =
        I.Let_cont {
          name = wrapper_cont;
          administrative = false;
          is_exn_handler = false;
          params = [];
          recursive = Non_recursive;
          body;
          handler = Apply_cont (prev_cont, Some trap_action, []);
        }
      in
      add_pop_traps ~prev_cont:wrapper_cont ~body:(Some body)
        ~try_stack_now ~try_stack_at_handler
    in
    match try_stack_now, try_stack_at_handler with
    | [], [] -> body
    | (id1, cont1) :: try_stack_now, (id2, cont2) :: _ ->
      if Trap_id.equal id1 id2 then begin
        assert (Continuation.equal cont1 cont2);
        body
      end else begin
        add_pop id1 cont1 ~try_stack_now
      end
    | (id, cont) :: try_stack_now, [] ->
      add_pop id cont ~try_stack_now
    | [], _ :: _ -> assert false  (* see above *)
  in
  let body =
    add_pop_traps ~prev_cont:outer_wrapper_cont
      ~body:None
      ~try_stack_now
      ~try_stack_at_handler
  in
  match body with
  | None -> I.Apply_cont (continuation, None, args)
  | Some body ->
    I.Let_cont {
      name = outer_wrapper_cont;
      administrative = false;
      is_exn_handler = false;
      params = [];
      recursive = Non_recursive;
      body;
      handler = Apply_cont (continuation, None, args);
    }

module N = Num_continuation_uses

let rec cps_non_tail (lam : L.lambda) (k : Ident.t -> Ilambda.t) : Ilambda.t =
  match lam with
  | Lvar id -> k id
  | Lconst _ -> name_then_cps_non_tail "const" lam k
  | Lapply apply ->
    cps_non_tail_list apply.ap_args (fun args ->
      cps_non_tail apply.ap_func (fun func ->
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
          administrative = false;
          is_exn_handler = false;
          params = [result_var];
          recursive = Non_recursive;
          body = Apply apply;
          handler = after;
       }))
  | Lfunction func -> name_then_cps_non_tail (name_for_function func) lam k
  | Llet (Variable, value_kind, id, defining_expr, body) ->
    let temp_id = Ident.create "let_mutable" in
    let body = cps_non_tail body k in
    let after_defining_expr = Continuation.create () in
    let defining_expr, k_count_defining_expr =
      cps_tail defining_expr after_defining_expr
    in
    let let_mutable : I.let_mutable =
      { id;
        initial_value = temp_id;
        contents_kind = value_kind;
        body;
      }
    in
    Let_cont {
      name = after_defining_expr;
      administrative = N.linear k_count_defining_expr;
      is_exn_handler = false;
      params = [temp_id];
      recursive = Non_recursive;
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
    Let_rec ([id, func], body)
  | Llet (_let_kind, _value_kind, id, Lprim (prim, args, loc), body) ->
    let body = cps_non_tail body k in
    cps_non_tail_list args (fun args ->
      I.Let (id, Prim (prim, args, loc), body))
  | Llet (_let_kind, _value_kind, id, Lassign (being_assigned, new_value),
      body) ->
    let body = cps_non_tail body k in
    cps_non_tail new_value (fun new_value ->
      I.Let (id, Assign { being_assigned; new_value; }, body))
  | Llet (_let_kind, _value_kind, id, defining_expr, body) ->
    (* CR-soon mshinwell / pchambart: keep value_kind in Ilambda and Flambda *)
    let body = cps_non_tail body k in
    let after_defining_expr = Continuation.create () in
    let defining_expr, k_count_defining_expr =
      cps_tail defining_expr after_defining_expr
    in
    Let_cont {
      name = after_defining_expr;
      administrative = N.linear k_count_defining_expr;
      is_exn_handler = false;
      params = [id];
      recursive = Non_recursive;
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
  | Lswitch (scrutinee, switch, _loc) ->
    begin match switch.sw_blocks with
    | [] -> ()
    | _ -> Misc.fatal_error "Lswitch `block' cases are forbidden"
    end;
    let after_switch = Continuation.create () in
    let result_var = Ident.create "switch_result" in
    let after = k result_var in
    let proto_switch : proto_switch =
      { numconsts = switch.sw_numconsts;
        consts = switch.sw_consts;
        failaction = switch.sw_failaction;
      }
    in
    let body, k_count = cps_switch proto_switch ~scrutinee after_switch in
    Let_cont {
      name = after_switch;
      administrative = N.linear k_count;
      is_exn_handler = false;
      params = [result_var];
      recursive = Non_recursive;
      body;
      handler = after;
    }
  | Lstringswitch _ ->
    Misc.fatal_error "Lstringswitch must be expanded prior to CPS conversion"
  | Lstaticraise (static_exn, args) ->
    let continuation =
      match Numbers.Int.Map.find static_exn !static_exn_env with
      | exception Not_found ->
        Misc.fatal_errorf "Unbound static exception %d" static_exn
      | continuation -> continuation
    in
    cps_non_tail_list args (fun args -> compile_staticfail ~continuation ~args)
  | Lstaticcatch (body, (static_exn, args), handler) ->
    let continuation = Continuation.create () in
    static_exn_env := Numbers.Int.Map.add static_exn continuation
      !static_exn_env;
    try_stack_at_handler := Continuation.Map.add continuation !try_stack
      !try_stack_at_handler;
    let after_continuation = Continuation.create () in
    let result_var = Ident.create "staticcatch_result" in
    let body, _k_count = cps_tail body after_continuation in
    let handler, _k_count = cps_tail handler after_continuation in
    Let_cont {
      name = after_continuation;
      administrative = false;
      is_exn_handler = false;
      params = [result_var];
      recursive = Non_recursive;
      body =
        Let_cont {
          name = continuation;
          administrative = false;
          is_exn_handler = false;
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
            administrative = false;
            is_exn_handler = false;
            params = [result_var];
            recursive = Non_recursive;
            body = Apply apply;
            handler = after;
          })))
  | Ltrywith (body, id, handler) ->
    let body_result = Ident.create "body_result" in
    let result_var = Ident.create "try_with_result" in
    let body_continuation = Continuation.create () in
    let handler_continuation = Continuation.create () in
    let poptrap_continuation = Continuation.create () in
    let after_continuation = Continuation.create () in
    let trap = Trap_id.create () in
    let old_try_stack = !try_stack in
    try_stack := (trap, handler_continuation) :: old_try_stack;
    let body, _k_count = cps_tail body poptrap_continuation in
    try_stack := old_try_stack;
    let handler, _k_count = cps_tail handler after_continuation in
    Let_cont {
      name = after_continuation;
      administrative = false;
      is_exn_handler = false;
      params = [result_var];
      recursive = Non_recursive;
      body =
        Let_cont {
          name = handler_continuation;
          administrative = false;
          is_exn_handler = true;
          params = [id];
          recursive = Non_recursive;
          body =
            Let_cont {
              name = poptrap_continuation;
              administrative = false;
              is_exn_handler = false;
              params = [body_result];
              recursive = Non_recursive;
              body =
                Let_cont {
                  name = body_continuation;
                  administrative = false;
                  is_exn_handler = false;
                  params = [];
                  recursive = Non_recursive;
                  body =
                    Apply_cont (body_continuation,
                      Some (I.Push {
                        id = trap;
                        exn_handler = handler_continuation;
                      }),
                      []);
                  handler = body;
                };
              handler = Apply_cont (after_continuation,
                Some (I.Pop { id = trap; exn_handler = handler_continuation; }),
                [body_result]);
            };
          handler;
        };
      handler = k result_var;
    }
  | Lassign _ -> name_then_cps_non_tail "assign" lam k
  | Levent (lam, event) -> Event (cps_non_tail lam k, event)
  | Lsequence _ | Lifthenelse _ | Lwhile _ | Lfor _ | Lifused _ ->
    Misc.fatal_errorf "Term should have been eliminated by [Prepare_lambda]: %a"
      Printlambda.lambda lam

(** [cps_tail lam k] returns the Ilambda term together with the number of
    uses in that term of the continuation [k]. *)
and cps_tail (lam : L.lambda) (k : Continuation.t) : Ilambda.t * N.t =
  match lam with
  | Lvar id -> Apply_cont (k, None, [id]), N.One
  | Lconst _ -> name_then_cps_tail "const" lam k
  | Lapply apply ->
    cps_non_tail_list apply.ap_args (fun args ->
      cps_non_tail apply.ap_func (fun func ->
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
        I.Apply apply)), N.Many
  | Lfunction func -> name_then_cps_tail (name_for_function func) lam k
  | Llet (Variable, value_kind, id, defining_expr, body) ->
    let temp_id = Ident.create "let_mutable" in
    let body, k_count = cps_tail body k in
    let after_defining_expr = Continuation.create () in
    let defining_expr, k_count_defining_expr =
      cps_tail defining_expr after_defining_expr
    in
    let let_mutable : I.let_mutable =
      { id;
        initial_value = temp_id;
        contents_kind = value_kind;
        body;
      }
    in
    Let_cont {
      name = after_defining_expr;
      administrative = N.linear k_count_defining_expr;
      is_exn_handler = false;
      params = [temp_id];
      recursive = Non_recursive;
      body = defining_expr;
      handler = Let_mutable let_mutable;
    }, k_count
  (* The following specialised Llet cases help to avoid administrative
     redexes. *)
  | Llet (_let_kind, _value_kind, id, Lvar id', body) ->
    let body, k_count = cps_tail body k in
    Let (id, Var id', body), k_count
  | Llet (_let_kind, _value_kind, id, Lconst const, body) ->
    let body, k_count = cps_tail body k in
    Let (id, Const const, body), k_count
  | Llet (_let_kind, _value_kind, id, Lfunction func, body) ->
    let func = cps_function func in
    let body, k_count = cps_tail body k in
    Let_rec ([id, func], body), k_count
  | Llet (_let_kind, _value_kind, id, Lprim (prim, args, loc), body) ->
    let body, k_count = cps_tail body k in
    cps_non_tail_list args (fun args ->
      I.Let (id, Prim (prim, args, loc), body)), k_count
  | Llet (_let_kind, _value_kind, id, Lassign (being_assigned, new_value),
      body) ->
    let body, k_count = cps_tail body k in
    cps_non_tail new_value (fun new_value ->
      I.Let (id, Assign { being_assigned; new_value; }, body)), k_count
  | Llet (_let_kind, _value_kind, id, defining_expr, body) ->
    let body, k_count = cps_tail body k in
    let after_defining_expr = Continuation.create () in
    let defining_expr, k_count_defining_expr =
      cps_tail defining_expr after_defining_expr
    in
    Let_cont {
      name = after_defining_expr;
      administrative = N.linear k_count_defining_expr;
      is_exn_handler = false;
      params = [id];
      recursive = Non_recursive;
      body = defining_expr;
      handler = body;
    }, k_count
  | Lletrec (bindings, body) ->
    let idents, bindings = List.split bindings in
    let bindings = List.map cps_function (check_let_rec_bindings bindings) in
    let body, k_count = cps_tail body k in
    Let_rec (List.combine idents bindings, body), k_count
  | Lprim (prim, args, loc) ->
    (* CR mshinwell: Arrange for "args" to be named. *)
    let name = Printlambda.name_of_primitive prim in
    let result_var = Ident.create name in
    cps_non_tail_list args (fun args ->
      I.Let (result_var, Prim (prim, args, loc),
        Apply_cont (k, None, [result_var]))),
    N.One
  | Lswitch (scrutinee, switch, _loc) ->
    begin match switch.sw_blocks with
    | [] -> ()
    | _ -> Misc.fatal_error "Lswitch `block' cases are forbidden"
    end;
    let proto_switch : proto_switch =
      { numconsts = switch.sw_numconsts;
        consts = switch.sw_consts;
        failaction = switch.sw_failaction;
      }
    in
    cps_switch proto_switch ~scrutinee k
  | Lstringswitch _ ->
    Misc.fatal_error "Lstringswitch must be expanded prior to CPS conversion"
  | Lstaticraise (static_exn, args) ->
    let continuation =
      match Numbers.Int.Map.find static_exn !static_exn_env with
      | exception Not_found ->
        Misc.fatal_errorf "Unbound static exception %d" static_exn
      | continuation -> continuation
    in
    cps_non_tail_list args (fun args -> compile_staticfail ~continuation ~args),
      N.One
  | Lstaticcatch (body, (static_exn, args), handler) ->
    let continuation = Continuation.create () in
    static_exn_env := Numbers.Int.Map.add static_exn continuation
      !static_exn_env;
    try_stack_at_handler := Continuation.Map.add continuation !try_stack
      !try_stack_at_handler;
    let body, k_count_body = cps_tail body k in
    let handler, k_count_handler = cps_tail handler k in
    Let_cont {
      name = continuation;
      administrative = false;
      is_exn_handler = false;
      params = args;
      recursive = Recursive;  (* see CR comment above *)
      body;
      handler;
    }, N.(+) k_count_body k_count_handler;
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
          I.Apply apply))), N.Many
  | Lassign _ -> name_then_cps_tail "assign" lam k
  | Levent (lam, event) ->
    let ilam, k_count = cps_tail lam k in
    Event (ilam, event), k_count
  | Ltrywith (body, id, handler) ->
    let body_result = Ident.create "body_result" in
    let body_continuation = Continuation.create () in
    let handler_continuation = Continuation.create () in
    let poptrap_continuation = Continuation.create () in
    let trap = Trap_id.create () in
    let old_try_stack = !try_stack in
    try_stack := (trap, handler_continuation) :: old_try_stack;
    let body, _k_count = cps_tail body poptrap_continuation in
    try_stack := old_try_stack;
    let handler, k_count_handler = cps_tail handler k in
    Let_cont {
      name = handler_continuation;
      administrative = false;
      is_exn_handler = true;
      params = [id];
      recursive = Non_recursive;
      body =
        Let_cont {
          name = poptrap_continuation;
          administrative = false;
          is_exn_handler = false;
          params = [body_result];
          recursive = Non_recursive;
          body =
            Let_cont {
              name = body_continuation;
              administrative = false;
              is_exn_handler = false;
              params = [];
              recursive = Non_recursive;
              body =
                Apply_cont (body_continuation,
                  Some (I.Push {
                    id = trap;
                    exn_handler = handler_continuation;
                  }),
                  []);
              handler = body;
            };
          handler = Apply_cont (k, Some (
            I.Pop { id = trap; exn_handler = handler_continuation; }),
            [body_result]);
        };
      handler;
    }, N.(+) k_count_handler N.One;
  | Lsequence _ | Lifthenelse _ | Lwhile _ | Lfor _ | Lifused _ ->
    Misc.fatal_errorf "Term should have been eliminated by [Prepare_lambda]: %a"
      Printlambda.lambda lam

and name_then_cps_non_tail name lam k =
  let var = Ident.create name in
  cps_non_tail (L.Llet (Strict, Pgenval, var, lam, Lvar var)) k

and name_then_cps_tail name lam k =
  let var = Ident.create name in
  cps_tail (L.Llet (Strict, Pgenval, var, lam, Lvar var)) k

and cps_non_tail_list lams k =
  let lams = List.rev lams in  (* Always evaluate right-to-left. *)
  cps_non_tail_list_core lams k

and cps_non_tail_list_core (lams : L.lambda list)
      (k : Ident.t list -> Ilambda.t) =
  match lams with
  | [] -> k []
  | lam::lams ->
    cps_non_tail lam (fun id ->
      cps_non_tail_list_core lams (fun ids -> k (ids @ [id])))

and cps_function (func : Lambda.lfunction) : Ilambda.function_declaration =
  let body_cont = Continuation.create () in
  let free_idents_of_body = Lambda.free_variables func.body in
  let stub, body =
    match func.body with
    | Lprim (Pccall { Primitive. prim_name; }, [body], _)
       when prim_name = Prepare_lambda.stub_hack_prim_name -> true, body
    | body -> false, body
  in
  let body, _k_count = cps_tail body body_cont in
  { kind = func.kind;
    continuation_param = body_cont;
    params = List.map (fun param -> param, Lambda.Pgenval) func.params;
    return = Pgenval;
    body;
    attr = func.attr;
    loc = func.loc;
    free_idents_of_body;
    stub;
  }

and cps_switch (switch : proto_switch) ~scrutinee (k : Continuation.t) =
  let const_nums, consts = List.split switch.consts in
  let const_conts = List.map (fun _ -> Continuation.create ()) consts in
  let consts = List.combine consts const_conts in
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
      failaction = failaction_cont;
    }
  in
  (* CR mshinwell: tidy this up *)
  (* CR mshinwell: Also think about the "One / Many" thing as seen in the
     context of "apply" or "send".  (Those must be "many" since the
     continuations are used in non-inlinable positions.)  We should at least
     add a comment about this. *)
  let k_count_ref = ref N.Zero in
  let make_continuations desc ~init =
    let ilam, k_count =
      List.fold_right (fun (case, cont) (acc, k_count) ->
          let handler, k_count' = cps_tail case k in
          let acc =
            I.Let_cont {
              name = cont;
              administrative = false;
              is_exn_handler = false;
              params = [];
              recursive = Non_recursive;
              body = acc;
              handler;
            }
          in
          acc, N.(+) k_count k_count')
        desc
        (init, N.Zero)
    in
    k_count_ref := N.(+) !k_count_ref k_count;
    ilam
  in
  let ilam =
    cps_non_tail scrutinee (fun scrutinee ->
      let body = I.Switch (scrutinee, switch) in
      let init =
        match failaction with
        | None -> body
        | Some (cont, failaction) ->
          let handler, k_count = cps_tail failaction k in
          k_count_ref := N.(+) !k_count_ref k_count;
          I.Let_cont {
            name = cont;
            administrative = false;
            is_exn_handler = false;
            params = [];
            recursive = Non_recursive;
            body;
            handler;
          }
      in
      make_continuations consts ~init)
  in
  ilam, !k_count_ref

let lambda_to_ilambda lam =
  static_exn_env := Numbers.Int.Map.empty;
  try_stack := [];
  try_stack_at_handler := Continuation.Map.empty;
  let the_end = Continuation.create () in
  let ilam, _k_count = cps_tail lam the_end in
  ilam, the_end
