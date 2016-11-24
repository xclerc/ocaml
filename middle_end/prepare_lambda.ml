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
[@@@ocaml.warning "-32"] (* XXX temporary *)

module L = Lambda

let stub_hack_prim_name = "*stub*"

let add_default_argument_wrappers lam =
  (* CR-someday mshinwell: Temporary hack to mark default argument wrappers
     as stubs.  Other possibilities:
     1. Change L.inline_attribute to add another ("stub") case;
     2. Add a "stub" field to the Lfunction record. *)
  let stubify body : L.lambda =
    let stub_prim =
      Primitive.simple ~name:stub_hack_prim_name
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
  let bindings_with_kinds =
    List.map (fun (id, binding) -> id, binding, L.size_of_lambda binding)
      bindings
  in
  let recursive_blocks, nonrecursives, functions =
    List.fold_left (fun (recursive_blocks, nonrecursives, functions)
              (id, binding, (kind : L.rhs_kind)) ->
        match kind with
        | RHS_function (_, _, funct) ->
          recursive_blocks, nonrecursives,
            (id, L.Lfunction funct)::functions
        | RHS_block size ->
          (id, Normal, size, binding) :: recursive_blocks, nonrecursives,
            functions
        | RHS_floatblock size ->
          (id, Float, size, binding) :: recursive_blocks, nonrecursives,
            functions
        | RHS_nonrec ->
          recursive_blocks, (id, binding) :: nonrecursives, functions)
      ([], [], [])
      bindings_with_kinds
  in
  let loc = Location.none in
  let preallocations =
    List.map (fun (id, block_type, size, _binding) ->
        let fn =
          match block_type with
          | Normal -> "caml_alloc_dummy"
          | Float -> "caml_alloc_dummy_float"
        in
        let desc = Primitive.simple ~name:fn ~arity:1 ~alloc:true in
        let size : L.lambda = Lconst (Const_base (Const_int size)) in
        id, L.Lprim (Pccall desc, [size], loc))
      recursive_blocks
  in
  let fillings =
    List.map (fun (id, _block_type, _size, binding) ->
        let seq = Ident.create "sequence" in
        let desc =
          Primitive.simple ~name:"caml_update_dummy" ~arity:2 ~alloc:true
        in
        seq, L.Lprim (Pccall desc, [L.Lvar id; binding], loc))
      recursive_blocks
  in
  List.fold_left (fun body (id, binding) ->
      L.Llet (Strict, Pgenval, id, binding, body))
    (L.Lletrec (functions, body))
    (preallocations @ nonrecursives @ fillings)

module Env : sig
  type t

  val create : current_unit_id:Ident.t -> t

  val current_unit_id : t -> Ident.t

  val add_mutable : t -> Ident.t -> t
  val is_mutable : t -> Ident.t -> bool

  val add_current_exception_continuation : t -> int -> t
  val add_continuation : t -> int -> t

  val required_poptrap_for_staticraise : t -> int -> int list
end = struct
  type t = {
    current_unit_id : Ident.t;
    mutables : Ident.Set.t;
    current_exception_continuation : int list;
    current_exception_depth : int;
    handler_exception_continuation : int Numbers.Int.Map.t; (* exception depth *)
  }

  let create ~current_unit_id =
    { current_unit_id;
      mutables = Ident.Set.empty;
      current_exception_continuation = [];
      current_exception_depth = 0;
      handler_exception_continuation = Numbers.Int.Map.empty;
    }

  let current_unit_id t = t.current_unit_id

  let add_mutable t id =
    assert (not (Ident.Set.mem id t.mutables));
    { t with mutables = Ident.Set.add id t.mutables; }

  let is_mutable t id =
    Ident.Set.mem id t.mutables

  let add_current_exception_continuation t cont =
    { t with
      current_exception_continuation =
        cont :: t.current_exception_continuation;
      current_exception_depth = 1 + t.current_exception_depth;
    }

  let add_continuation t cont =
    { t with
      handler_exception_continuation =
        Numbers.Int.Map.add cont t.current_exception_depth
          t.handler_exception_continuation;
    }

  let required_poptrap_for_staticraise t cont =
    let continuation_depth =
      Numbers.Int.Map.find cont t.handler_exception_continuation
    in
    let number_of_required_poptraps =
      t.current_exception_depth - continuation_depth
    in
    let head, _ =
      Misc.Stdlib.List.split_at number_of_required_poptraps
        t.current_exception_continuation
    in
    head

end

let sequence (lam1, lam2) =
  let ident = Ident.create "sequence" in
  L.Llet (Strict, Pgenval, ident, lam1, lam2)

let rec simplify_primitive env (prim : L.primitive) args loc =
  match prim, args with
  | Prim ((Pdivint Safe | Pmodint Safe
           | Pdivbint { is_safe = Safe } | Pmodbint { is_safe = Safe }) as prim,
           [arg1; arg2], loc)
      when not !Clflags.fast -> (* not -unsafe *)
    let numerator = Variable.create "numerator" in
    let denominator = Variable.create "denominator" in
    let zero = Variable.create "zero" in
    let is_zero = Variable.create "is_zero" in
    let exn = Variable.create "division_by_zero" in
    let zero_const : Lambda.structured_constant =
      match prim with
      | Pdivint _ | Pmodint _ ->
        Const_base (Const_int 0)
      | Pdivbint { size = Pint32 } | Pmodbint { size = Pint32 } ->
        Const_base (Const_int32 0l)
      | Pdivbint { size = Pint64 } | Pmodbint { size = Pint64 } ->
        Const_base (Const_int64 0L)
      | Pdivbint { size = Pnativeint } | Pmodbint { size = Pnativeint } ->
        Const_base (Const_nativeint 0n)
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
    Llet (Strict, Pgenval, zero, zero_const
      (Llet (Strict, Pgenval, exn, Predef.ident_division_by_zero,
        (Llet (Strict, Pgenval, denominator, arg2,
          (Llet (Strict, Pgenval, numerator, arg1,
            (Llet (Strict, Pgenval, is_zero,
              (Lprim (comparison, [zero; denominator], loc))
                (Lifthenelse (is_zero,
                  Lprim (Praise Raise_regular, [exn], loc),
                  (* CR-someday pchambart: find the right event.
                     mshinwell: I briefly looked at this, and couldn't
                     figure it out.
                     lwhite: I don't think any of the existing events
                     are suitable. I had to add a new one for a similar
                     case in the array data types work.
                     mshinwell: deferred CR *)
                  Lprim (prim, [numerator; denominator], loc))))))))))))
  | Prim ((Pdivint Safe | Pmodint Safe
           | Pdivbint { is_safe = Safe } | Pmodbint { is_safe = Safe }), _, _)
      when not !Clflags.fast ->
    Misc.fatal_error "Pdivint / Pmodint must have exactly two arguments"
  | Psequor, [arg1; arg2] ->
    let const_true = Ident.create "const_true" in
    let cond = Ident.create "cond_sequor" in
    prepare env (
      L.Llet (Strict, Pgenval, const_true, Lconst (Const_base (Const_int 1)),
        (L.Llet (Strict, Pgenval, cond, arg1,
          (Lifthenelse (Lvar cond, Lvar const_true, arg2))))))
      (fun lam -> lam)
  | Psequand, [arg1; arg2] ->
    let const_false = Ident.create "const_false" in
    let cond = Ident.create "cond_sequand" in
    (* CR mshinwell: This recursion is a bit ugly.  Factor out a helper
       function for constructing if-then-else-like switches? *)
    prepare env (
      L.Llet (Strict, Pgenval, const_false, Lconst (Const_base (Const_int 0)),
        (L.Llet (Strict, Pgenval, cond, arg1,
          (Lifthenelse (Lvar cond, arg2, Lvar const_false))))))
      (fun lam -> lam)
  | (Psequand | Psequor), _ ->
    Misc.fatal_error "Psequand / Psequor must have exactly two arguments"
  | Pidentity, [arg] -> arg
  | Pdirapply, [funct; arg]
  | Prevapply, [arg; funct] ->
    let apply : L.lambda_apply =
      { ap_func = funct;
        ap_args = [arg];
        ap_loc = loc;
        ap_should_be_tailcall = false;
        (* CR-someday lwhite: it would be nice to be able to give
           inlined attributes to functions applied with the application
           operators. *)
        ap_inlined = Default_inline;
        ap_specialised = Default_specialise;
      }
    in
    L.Lapply apply
  | _, _ -> L.Lprim (prim, args, loc)

and prepare env (lam : L.lambda) (k : L.lambda -> L.lambda) =
  match lam with
  | Lvar id ->
    (* The special [Pread_mutable] primitive eases the translation to
       [Read_mutable] in Flambda. *)
    if Env.is_mutable env id then
      k (Lprim (Pread_mutable id, [], Location.none))
    else
      k lam
  | Lconst _ -> k lam
  | Lapply apply ->
    prepare env apply.ap_func (fun ap_func ->
      prepare_list env apply.ap_args (fun ap_args ->
        k (L.Lapply {
          ap_func;
          ap_args;
          ap_loc = apply.ap_loc;
          ap_should_be_tailcall = apply.ap_should_be_tailcall;
          ap_inlined = apply.ap_inlined;
          ap_specialised = apply.ap_specialised;
        })))
  | Lfunction func ->
    prepare env func.body (fun body ->
      k (L.Lfunction {
        kind = func.kind;
        params = func.params;
        body;
        attr = func.attr;
        loc = func.loc;
      }))
  | Llet (let_kind, value_kind, id, defining_expr, body) ->
    prepare env defining_expr (fun defining_expr ->
      let env =
        match let_kind with
        | Strict | StrictOpt | Alias -> env
        | Variable -> Env.add_mutable env id
      in
      prepare env body (fun body ->
        k (L.Llet (let_kind, value_kind, id, defining_expr, body))))
  | Lletrec (bindings, body) ->
    let idents, bindings = List.split bindings in
    prepare_list env bindings (fun bindings ->
      let bindings = List.combine idents bindings in
      prepare env body (fun body ->
        k (dissect_letrec ~bindings ~body)))
  | Lprim (Pfield _, [Lprim (Pgetglobal id, [],_)], _)
      when Ident.same id (Env.current_unit_id env) ->
    Misc.fatal_error "[Pfield (Pgetglobal ...)] for the current compilation \
      unit is forbidden upon entry to the middle end"
  | Lprim (Psetfield (_, _, _), [Lprim (Pgetglobal _, [], _); _], _) ->
    Misc.fatal_error "[Psetfield (Pgetglobal ...)] is \
      forbidden upon entry to the middle end"
  | Lprim (prim, args, loc) ->
    prepare_list env args (fun args ->
      k (simplify_primitive env prim args loc))
  | Lswitch (scrutinee, switch) ->
    prepare env scrutinee (fun scrutinee ->
      let const_nums, sw_consts = List.split switch.sw_consts in
      let block_nums, sw_blocks = List.split switch.sw_blocks in
      prepare_option env switch.sw_failaction (fun sw_failaction ->
        prepare_list env sw_consts (fun sw_consts ->
          prepare_list env sw_blocks (fun sw_blocks ->
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
    prepare env scrutinee (fun scrutinee ->
      let patterns, cases = List.split cases in
      prepare_list env cases (fun cases ->
        let cases = List.combine patterns cases in
        prepare_option env default (fun default ->
          k (L.Lstringswitch (scrutinee, cases, default, loc)))))
  | Lstaticraise (cont, args) ->
    prepare_list env args (fun args ->
      k (L.Lstaticraise (cont, args)))
  | Lstaticcatch (body, (cont, args), handler) ->
    let env_body = Env.add_continuation env cont in
    prepare env_body body (fun body ->
      prepare env handler (fun handler ->
        k (L.Lstaticcatch (body, (cont, args), handler))))
  | Ltrywith (body, id, handler) ->
    prepare env body (fun body ->
      prepare env handler (fun handler ->
        k (L.Ltrywith (body, id, handler))))
  | Lifthenelse (cond, ifso, ifnot) ->
    prepare env cond (fun cond ->
      prepare env ifso (fun ifso ->
        prepare env ifnot (fun ifnot ->
          let switch : Lambda.lambda_switch =
            { sw_numconsts = 2;
              sw_consts = [0, ifnot; 1, ifso];
              sw_numblocks = 0;
              sw_blocks = [];
              sw_failaction = None;
            }
          in
          k (L.Lswitch (cond, switch)))))
  | Lsequence (lam1, lam2) ->
    let ident = Ident.create "sequence" in
    prepare env (L.Llet (Strict, Pgenval, ident, lam1, lam2)) k
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
    prepare env lam k
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
    prepare env lam k
  | Lassign (ident, lam) ->
    if not (Env.is_mutable env ident) then begin
      Misc.fatal_errorf "Lassign on non-mutable variable %a"
        Ident.print ident
    end;
    prepare env lam (fun lam -> k (L.Lassign (ident, lam)))
  | Lsend (meth_kind, meth, obj, args, loc) ->
    prepare env meth (fun meth ->
      prepare env obj (fun obj ->
        prepare_list env args (fun args ->
          k (L.Lsend (meth_kind, meth, obj, args, loc)))))
  | Levent (body, event) ->
    prepare env body (fun body ->
      k (L.Levent (body, event)))
  | Lifused _ ->
    (* [Lifused] is used to mark that this expression should be alive only if
       an identifier is.  Every use should have been removed by
       [Simplif.simplify_lets], either by replacing by the inner expression,
       or by completely removing it (replacing by unit). *)
    Misc.fatal_error "[Lifused] should have been removed by \
        [Simplif.simplify_lets]"

and prepare_list env lams k =
  match lams with
  | [] -> k []
  | lam::lams ->
    prepare env lam (fun lam ->
      prepare_list env lams (fun lams -> k (lam::lams)))

and prepare_option env lam_opt k =
  match lam_opt with
  | None -> k None
  | Some lam -> prepare env lam (fun lam -> k (Some lam))

let run lam =
  let current_unit_id =
    Compilation_unit.get_persistent_ident
      (Compilation_unit.get_current_exn ())
  in
  let env = Env.create ~current_unit_id in
  let lam = add_default_argument_wrappers lam in
  prepare env lam (fun lam -> lam)
