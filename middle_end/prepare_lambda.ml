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

type block_type = Normal | Float

let dissect_letrec ~bindings ~body =
  let bindings_with_sizes =
    List.map (fun (id, binding) -> id, binding, L.size_of_lambda binding)
      bindings
  in
  let recursive_blocks, nonrecursives, functions =
    List.fold_left (fun (recursive_blocks, nonrecursives, functions)
              (id, binding, (kind : L.rhs_kind)) ->
        match kind with
        | RHS_function (_, _, funct) ->
          recursive_blocks, nonrecursive_blocks,
            (id, Lfunction funct)::functions
        | RHS_block size ->
          (id, Normal, size, binding) :: recursive_blocks, nonrecursive_blocks,
            functions
        | RHS_floatblock size ->
          (id, Float, size, binding) :: recursive_blocks, nonrecursive_blocks,
            functions
        | RHS_nonrec ->
          recursive_blocks, (id, binding) :: nonrecursives, functions
      ([], [], [])
      bindings
  in
  let loc = Location.none in
  let preallocations =
    List.map (fun (id, block_type, size) ->
        let fn =
          match block_type with
          | Normal -> "caml_alloc_dummy"
          | Float -> "caml_alloc_dummy_float"
        in
        let size : L.lambda = Lconst (Const_base (Const_int size)) in
        id, Lprim (Pccall fn, [size], loc))
      recursive_blocks
  in
  let fillings =
    List.map (fun (id, _block_type, _size, binding) ->
        let seq = Ident.create "sequence" in
        seq, Lprim (Pccall "caml_update_dummy", [Lvar id; binding], loc))
      recursive_blocks
  in
  List.fold_left (fun (id, binding) body ->
      Llet (Strict, Pgenval, id, binding, body))
    (Lletrec (functions, body))
    (preallocations @ nonrecursives @ fillings)

let simplify_primitive prim args loc =
  match prim, args with
  | Prim ((Pdivint Safe | Pmodint Safe
           | Pdivbint { is_safe = Safe } | Pmodbint { is_safe = Safe }) as prim,
           [arg1; arg2], loc)
      when not !Clflags.fast -> (* not -unsafe *)
    let arg2 = close t env arg2 in
    let arg1 = close t env arg1 in
    let numerator = Variable.create "numerator" in
    let denominator = Variable.create "denominator" in
    let zero = Variable.create "zero" in
    let is_zero = Variable.create "is_zero" in
    let exn = Variable.create "division_by_zero" in
    let exn_symbol =
      t.symbol_for_global' Predef.ident_division_by_zero
    in
    let dbg = Debuginfo.from_location loc in
    let zero_const : Flambda.named =
      match prim with
      | Pdivint _ | Pmodint _ ->
        Const (Int 0)
      | Pdivbint { size = Pint32 } | Pmodbint { size = Pint32 } ->
        Allocated_const (Int32 0l)
      | Pdivbint { size = Pint64 } | Pmodbint { size = Pint64 } ->
        Allocated_const (Int64 0L)
      | Pdivbint { size = Pnativeint } | Pmodbint { size = Pnativeint } ->
        Allocated_const (Nativeint 0n)
      | _ -> assert false
    in
    let prim : Lambda.primitive =
      match prim with
      | Pdivint _ -> Pdivint Unsafe
      | Pmodint _ -> Pmodint Unsafe
      | Pdivbint { size } -> Pdivbint { size; is_safe = Unsafe }
      | Pmodbint { size } -> Pmodbint { size; is_safe = Unsafe }
      | _ -> assert false
    in
    let comparison : Lambda.primitive =
      match prim with
      | Pdivint _ | Pmodint _ -> Pintcomp Ceq
      | Pdivbint { size } | Pmodbint { size } -> Pbintcomp (size, Ceq)
      | _ -> assert false
    in
    t.imported_symbols <- Symbol.Set.add exn_symbol t.imported_symbols;
    Flambda.create_let zero zero_const
      (Flambda.create_let exn (Symbol exn_symbol)
        (Flambda.create_let denominator (Expr arg2)
          (Flambda.create_let numerator (Expr arg1)
            (Flambda.create_let is_zero
              (Prim (comparison, [zero; denominator], dbg))
                (If_then_else (is_zero,
                  name_expr (Prim (Praise Raise_regular, [exn], dbg))
                    ~name:"dummy",
                  (* CR-someday pchambart: find the right event.
                     mshinwell: I briefly looked at this, and couldn't
                     figure it out.
                     lwhite: I don't think any of the existing events
                     are suitable. I had to add a new one for a similar
                     case in the array data types work.
                     mshinwell: deferred CR *)
                  name_expr ~name:"result"
                    (Prim (prim, [numerator; denominator], dbg))))))))
  | Prim ((Pdivint Safe | Pmodint Safe
           | Pdivbint { is_safe = Safe } | Pmodbint { is_safe = Safe }), _, _)
      when not !Clflags.fast ->
    Misc.fatal_error "Pdivint / Pmodint must have exactly two arguments"
  | Prim (Psequor, [arg1; arg2], _) ->
    let arg1 = close t env arg1 in
    let arg2 = close t env arg2 in
    let const_true = Variable.create "const_true" in
    let cond = Variable.create "cond_sequor" in
    Flambda.create_let const_true (Const (Int 1))
      (Flambda.create_let cond (Expr arg1)
        (If_then_else (cond, Var const_true, arg2)))
  | Prim (Psequand, [arg1; arg2], _) ->
    let arg1 = close t env arg1 in
    let arg2 = close t env arg2 in
    let const_false = Variable.create "const_false" in
    let cond = Variable.create "cond_sequand" in
    Flambda.create_let const_false (Const (Int 0))
      (Flambda.create_let cond (Expr arg1)
        (If_then_else (cond, arg2, Var const_false)))
  | Prim ((Psequand | Psequor), _, _) ->
    Misc.fatal_error "Psequand / Psequor must have exactly two arguments"
  | Prim (Pidentity, [arg], _) -> close t env arg
  | Prim (Pdirapply, [funct; arg], loc)
  | Prim (Prevapply, [arg; funct], loc) ->
    let apply : Ilambda.apply =
      { func = funct;
        args = [arg];
        loc = loc;
        should_be_tailcall = false;
        (* CR-someday lwhite: it would be nice to be able to give
           inlined attributes to functions applied with the application
           operators. *)
        inlined = Default_inline;
        specialised = Default_specialise;
      }
    in
    close_apply t env apply
  | Prim (Praise kind, [arg], loc) ->
    let arg_var = Variable.create "raise_arg" in
    let dbg = Debuginfo.from_location loc in
    Flambda.create_let arg_var (Expr (close t env arg))
      (name_expr
        (Prim (Praise kind, [arg_var], dbg))
        ~name:"raise")
  | Prim (Pfield _, [Prim (Pgetglobal id, [],_)], _)
      when Ident.same id t.current_unit_id ->
    Misc.fatal_errorf "[Pfield (Pgetglobal ...)] for the current compilation \
        unit is forbidden upon entry to the middle end"
  | Prim (Psetfield (_, _, _), [Prim (Pgetglobal _, [], _); _], _) ->
    Misc.fatal_errorf "[Psetfield (Pgetglobal ...)] is \
        forbidden upon entry to the middle end"
  | Prim (Pgetglobal id, [], _) when Ident.is_predef_exn id ->
    let symbol = t.symbol_for_global' id in
    t.imported_symbols <- Symbol.Set.add symbol t.imported_symbols;
    name_expr (Symbol symbol) ~name:"predef_exn"
  | Prim (Pgetglobal id, [], _) ->
    assert (not (Ident.same id t.current_unit_id));
    let symbol = t.symbol_for_global' id in
    t.imported_symbols <- Symbol.Set.add symbol t.imported_symbols;
    name_expr (Symbol symbol) ~name:"Pgetglobal"

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
      k (simplify_primitive prim args loc))
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
    let cont = L.next_raise_count () in
    let loc = Location.none in
    let lam =
      Lstaticcatch (
        Lsequence (
          Lprim (Ppushtrap, [], loc),
          Lsequence (
            body,
            Lprim (Ppoptrap, [], loc))),
        (cont, [id]),
        handler)
    in
    prepare lam k
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
