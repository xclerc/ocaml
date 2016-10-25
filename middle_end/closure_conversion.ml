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

module Env = Closure_conversion_aux.Env
module Function_decls = Closure_conversion_aux.Function_decls
module Function_decl = Function_decls.Function_decl
module IdentSet = Lambda.IdentSet

let name_expr = Flambda_utils.name_expr

type t = {
  current_unit_id : Ident.t;
  symbol_for_global' : (Ident.t -> Symbol.t);
  filename : string;
  mutable imported_symbols : Symbol.Set.t;
}

(** Generate a wrapper ("stub") function that accepts a tuple argument and
    calls another function with arguments extracted in the obvious
    manner from the tuple. *)
let tupled_function_call_stub original_params unboxed_version
      : Flambda.function_declaration =
  let tuple_param =
    Variable.rename ~append:"tupled_stub_param" unboxed_version
  in
  let params = List.map (fun p -> Variable.rename p) original_params in
  let call : Flambda.t =
    Apply ({
        func = unboxed_version;
        args = params;
        (* CR-someday mshinwell for mshinwell: investigate if there is some
           redundancy here (func is also unboxed_version) *)
        kind = Direct (Closure_id.wrap unboxed_version);
        dbg = Debuginfo.none;
        inline = Default_inline;
        specialise = Default_specialise;
      })
  in
  let _, body =
    List.fold_left (fun (pos, body) param ->
        let lam : Flambda.named =
          Prim (Pfield pos, [tuple_param], Debuginfo.none)
        in
        pos + 1, Flambda.create_let param lam body)
      (0, call) params
  in
  Flambda.create_function_declaration ~params:[tuple_param]
    ~body ~stub:true ~dbg:Debuginfo.none ~inline:Default_inline
    ~specialise:Default_specialise ~is_a_functor:false

let rec eliminate_const_block (const : Lambda.structured_constant)
      : Lambda.lambda =
  match const with
  | Const_block (tag, consts) ->
    (* CR-soon mshinwell for lwhite: fix location *)
    Prim (Pmakeblock (tag, Asttypes.Immutable, None),
      List.map eliminate_const_block consts, Location.none)
  | Const_base _
  | Const_pointer _
  | Const_immstring _
  | Const_float_array _ -> Lconst const

let rec close_const t env (const : Lambda.structured_constant)
      : Flambda.named * string =
  match const with
  | Const_base (Const_int c) -> Const (Int c), "int"
  | Const_base (Const_char c) -> Const (Char c), "char"
  | Const_base (Const_string (s, _)) ->
    if Config.safe_string then Allocated_const (Immutable_string s), "immstring"
    else Allocated_const (String s), "string"
  | Const_base (Const_float c) ->
    Allocated_const (Float (float_of_string c)), "float"
  | Const_base (Const_int32 c) -> Allocated_const (Int32 c), "int32"
  | Const_base (Const_int64 c) -> Allocated_const (Int64 c), "int64"
  | Const_base (Const_nativeint c) ->
    Allocated_const (Nativeint c), "nativeint"
  | Const_pointer c -> Const (Const_pointer c), "pointer"
  | Const_immstring c -> Allocated_const (Immutable_string c), "immstring"
  | Const_float_array c ->
    Allocated_const (Immutable_float_array (List.map float_of_string c)),
      "float_array"
  | Const_block _ ->
    Expr (close t env (eliminate_const_block const)), "const_block"

and close t env (lam : Ilambda.t) : Flambda.t =
  match lam with
  | Var id ->
    begin match Env.find_var_exn env id with
    | var -> Var var
    | exception Not_found ->
      match Env.find_mutable_var_exn env id with
      | mut_var -> name_expr (Read_mutable mut_var) ~name:"read_mutable"
      | exception Not_found ->
        Misc.fatal_errorf "Closure_conversion.close: unbound identifier %a"
          Ident.print id
    end
  | Const cst ->
    let cst, name = close_const t env cst in
    name_expr cst ~name:("const_" ^ name)
  | Let ((Strict | Alias | StrictOpt), _value_kind, id, defining_expr, body) ->
    (* TODO: keep value_kind in flambda *)
    let var = Variable.create_with_same_name_as_ident id in
    let defining_expr =
      close_let_bound_expression t var env defining_expr
    in
    let body = close t (Env.add_var env id var) body in
    Flambda.create_let var defining_expr body
  | Let (Variable, block_kind, id, defining_expr, body) ->
    let mut_var = Mutable_variable.of_ident id in
    let var = Variable.create_with_same_name_as_ident id in
    let defining_expr =
      close_let_bound_expression t var env defining_expr
    in
    let body = close t (Env.add_mutable_var env id mut_var) body in
    Flambda.create_let var defining_expr
      (Let_mutable
         { var = mut_var;
           initial_value = var;
           body;
           contents_kind = block_kind })
  | Function { kind; params; body; attr; loc; } ->
    let name =
      (* Name anonymous functions by their source location, if known. *)
      if loc = Location.none then "anon-fn"
      else Format.asprintf "anon-fn[%a]" Location.print_compact loc
    in
    let closure_bound_var = Variable.create name in
    (* CR-soon mshinwell: some of this is now very similar to the let rec case
       below *)
    let set_of_closures_var = Variable.create ("set_of_closures_" ^ name) in
    let set_of_closures =
      let decl =
        Function_decl.create ~let_rec_ident:None ~closure_bound_var ~kind
          ~params ~body ~inline:attr.inline ~specialise:attr.specialise
          ~is_a_functor:attr.is_a_functor ~loc
      in
      close_functions t env (Function_decls.create [decl])
    in
    let project_closure : Flambda.project_closure =
      { set_of_closures = set_of_closures_var;
        closure_id = Closure_id.wrap closure_bound_var;
      }
    in
    Flambda.create_let set_of_closures_var set_of_closures
      (name_expr (Project_closure (project_closure))
        ~name:("project_closure_" ^ name))
  | Apply apply ->
    close_apply t env apply
  | Let_rec (defs, body) ->
    let env =
      List.fold_right (fun (id,  _) env ->
          Env.add_var env id (Variable.create_with_same_name_as_ident id))
        defs env
    in
    let function_declarations =
      (* Identify any bindings in the [let rec] that are functions.  These
         will be named after the corresponding identifier in the [let rec]. *)
      List.map (function
          | (let_rec_ident,
             Ilambda.Function { kind; params; body; attr; loc }) ->
            let closure_bound_var =
              Variable.create_with_same_name_as_ident let_rec_ident
            in
            let function_declaration =
              Function_decl.create ~let_rec_ident:(Some let_rec_ident)
                ~closure_bound_var ~kind ~params ~body
                ~inline:attr.inline ~specialise:attr.specialise
                ~is_a_functor:attr.is_a_functor ~loc
            in
            Some function_declaration
          | _ -> None)
        defs
    in
    begin match
      Misc.Stdlib.List.some_if_all_elements_are_some function_declarations
    with
    | Some function_declarations ->
      (* When all the bindings are (syntactically) functions, we can
         eliminate the [let rec] construction, instead producing a normal
         [Let] that binds a set of closures containing all of the functions.
      *)
      (* CR-someday lwhite: This is a very syntactic criteria. Adding an
         unused value to a set of recursive bindings changes how
         functions are represented at runtime. *)
      let name =
        (* The Microsoft assembler has a 247-character limit on symbol
           names, so we keep them shorter to try not to hit this. *)
        if Sys.win32 then begin
          match defs with
          | (id, _)::_ -> (Ident.unique_name id) ^ "_let_rec"
          | _ -> "let_rec"
        end else begin
          String.concat "_and_"
            (List.map (fun (id, _) -> Ident.unique_name id) defs)
        end
      in
      let set_of_closures_var = Variable.create name in
      let set_of_closures =
        close_functions t env (Function_decls.create function_declarations)
      in
      let body =
        List.fold_left (fun body decl ->
            let let_rec_ident = Function_decl.let_rec_ident decl in
            let closure_bound_var = Function_decl.closure_bound_var decl in
            let let_bound_var = Env.find_var env let_rec_ident in
            (* Inside the body of the [let], each function is referred to by
               a [Project_closure] expression, which projects from the set of
               closures. *)
            (Flambda.create_let let_bound_var
              (Project_closure {
                set_of_closures = set_of_closures_var;
                closure_id = Closure_id.wrap closure_bound_var;
              })
              body))
          (close t env body) function_declarations
      in
      Flambda.create_let set_of_closures_var set_of_closures body
    | None ->
      (* If the condition above is not satisfied, we build a [Let_rec]
         expression; any functions bound by it will have their own
         individual closures. *)
      let defs =
        List.map (fun (id, def) ->
            let var = Env.find_var env id in
            var, close_let_bound_expression t ~let_rec_ident:id var env def)
          defs
      in
      Let_rec (defs, close t env body)
    end
  | Send (kind, meth, obj, args, loc) ->
    let meth_var = Variable.create "meth" in
    let obj_var = Variable.create "obj" in
    let dbg = Debuginfo.from_location loc in
    Flambda.create_let meth_var (Expr (close t env meth))
      (Flambda.create_let obj_var (Expr (close t env obj))
        (Lift_code.lifting_helper (close_list t env args)
          ~evaluation_order:`Right_to_left
          ~name:"send_arg"
          ~create_body:(fun args ->
              Send { kind; meth = meth_var; obj = obj_var; args; dbg; })))
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
      | Pdivbint { size } | Pmodbint { size } -> Pbintcomp (size,Ceq)
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
  | Prim (p, args, loc) ->
    (* One of the important consequences of the ANF-like representation
       here is that we obtain names corresponding to the components of
       blocks being made (with [Pmakeblock]).  This information can be used
       by the simplification pass to increase the likelihood of eliminating
       the allocation, since some field accesses can be tracked back to known
       field values. *)
    let name = Printlambda.name_of_primitive p in
    let dbg = Debuginfo.from_location loc in
    Lift_code.lifting_helper (close_list t env args)
      ~evaluation_order:`Right_to_left
      ~name:(name ^ "_arg")
      ~create_body:(fun args ->
        name_expr (Prim (p, args, dbg))
          ~name)
  | Switch (arg, sw) ->
    let scrutinee = Variable.create "switch" in
    let aux (i, lam) = i, close t env lam in
    let zero_to_n = Numbers.Int.zero_to_n in
    Flambda.create_let scrutinee (Expr (close t env arg))
      (Switch (scrutinee,
        { numconsts = zero_to_n (sw.sw_numconsts - 1);
          consts = List.map aux sw.sw_consts;
          numblocks = zero_to_n (sw.sw_numblocks - 1);
          blocks = List.map aux sw.sw_blocks;
          failaction = Misc.may_map (close t env) sw.sw_failaction;
        }))
  | String_switch (arg, sw, def, _) ->
    let scrutinee = Variable.create "string_switch" in
    Flambda.create_let scrutinee (Expr (close t env arg))
      (String_switch (scrutinee,
        List.map (fun (s, e) -> s, close t env e) sw,
        Misc.may_map (close t env) def))
  | Apply_cont (cont, args) ->
    Lift_code.lifting_helper (close_list t env args)
      ~evaluation_order:`Right_to_left
      ~name:"apply_cont_arg"
      ~create_body:(fun args ->
        let cont = Env.find_continuation env cont in
        Apply_cont (cont, args))
  | Let_cont (body, (i, ids), handler) ->
    let cont = Cont_variable.create () in
    let env = Env.add_continuation env i cont in
    let vars = List.map (Variable.create_with_same_name_as_ident) ids in
    Let_cont (cont, vars, close t env body,
      close t (Env.add_vars env ids vars) handler)
  | Try_with (body, id, handler) ->
    let var = Variable.create_with_same_name_as_ident id in
    Try_with (close t env body, var, close t (Env.add_var env id var) handler)
  | If_then_else (cond, ifso, ifnot) ->
    let cond = close t env cond in
    let cond_var = Variable.create "cond" in
    Flambda.create_let cond_var (Expr cond)
      (If_then_else (cond_var, close t env ifso, close t env ifnot))
  | Event (lam, _) -> close t env lam

and close_apply t env { ap_func; ap_args; ap_loc; ap_should_be_tailcall = _;
      ap_inlined; ap_specialised; } =
  Lift_code.lifting_helper (close_list t env ap_args)
    ~evaluation_order:`Right_to_left
    ~name:"apply_arg"
    ~create_body:(fun args ->
      let func = close t env ap_func in
      let func_var = Variable.create "apply_funct" in
      Flambda.create_let func_var (Expr func)
        (Apply ({
            func = func_var;
            args;
            kind = Indirect;
            dbg = Debuginfo.from_location ap_loc;
            inline = ap_inlined;
            specialise = ap_specialised;
          })))

(** Perform closure conversion on a set of function declarations, returning a
    set of closures.  (The set will often only contain a single function;
    the only case where it cannot is for "let rec".) *)
and close_functions t external_env function_declarations : Flambda.named =
  let closure_env_without_parameters =
    Function_decls.closure_env_without_parameters
      external_env function_declarations
  in
  let all_free_idents = Function_decls.all_free_idents function_declarations in
  let close_one_function map decl =
    let body = Function_decl.body decl in
    let loc = Function_decl.loc decl in
    let dbg = Debuginfo.from_location loc in
    let params = Function_decl.params decl in
    (* Create fresh variables for the elements of the closure (cf.
       the comment on [Function_decl.closure_env_without_parameters], above).
       This induces a renaming on [Function_decl.free_idents]; the results of
       that renaming are stored in [free_variables]. *)
    let closure_env =
      List.fold_right (fun id env ->
          Env.add_var env id (Variable.create_with_same_name_as_ident id))
        params closure_env_without_parameters
    in
    (* If the function is the wrapper for a function with an optional
       argument with a default value, make sure it always gets inlined.
       CR-someday pchambart: eta-expansion wrapper for a primitive are
       not marked as stub but certainly should *)
    let stub, body =
      match Function_decl.primitive_wrapper decl with
      | None -> false, body
      | Some wrapper_body -> true, wrapper_body
    in
    let params = List.map (Env.find_var closure_env) params in
    let closure_bound_var = Function_decl.closure_bound_var decl in
    let body = close t closure_env body in
    let fun_decl =
      Flambda.create_function_declaration ~params ~body ~stub ~dbg
        ~inline:(Function_decl.inline decl)
        ~specialise:(Function_decl.specialise decl)
        ~is_a_functor:(Function_decl.is_a_functor decl)
    in
    match Function_decl.kind decl with
    | Curried -> Variable.Map.add closure_bound_var fun_decl map
    | Tupled ->
      let unboxed_version = Variable.rename closure_bound_var in
      let generic_function_stub =
        tupled_function_call_stub params unboxed_version
      in
      Variable.Map.add unboxed_version fun_decl
        (Variable.Map.add closure_bound_var generic_function_stub map)
  in
  let function_decls =
    Flambda.create_function_declarations
      ~funs:
        (List.fold_left close_one_function Variable.Map.empty
          (Function_decls.to_list function_declarations))
  in
  (* The closed representation of a set of functions is a "set of closures".
     (For avoidance of doubt, the runtime representation of the *whole set* is
     a single block with tag [Closure_tag].) *)
  let set_of_closures =
    let free_vars =
      IdentSet.fold (fun var map ->
          let internal_var =
            Env.find_var closure_env_without_parameters var
          in
          let external_var : Flambda.specialised_to =
            { var = Env.find_var external_env var;
              projection = None;
            }
          in
          Variable.Map.add internal_var external_var map)
        all_free_idents Variable.Map.empty
    in
    Flambda.create_set_of_closures ~function_decls ~free_vars
      ~specialised_args:Variable.Map.empty
      ~direct_call_surrogates:Variable.Map.empty
  in
  Set_of_closures set_of_closures

and close_list t sb l = List.map (close t sb) l

and close_let_bound_expression t ?let_rec_ident let_bound_var env
      (lam : Lambda.lambda) : Flambda.named =
  match lam with
  | Lfunction { kind; params; body; attr; loc; } ->
    (* Ensure that [let] and [let rec]-bound functions have appropriate
       names. *)
    let closure_bound_var = Variable.rename let_bound_var in
    let decl =
      Function_decl.create ~let_rec_ident ~closure_bound_var ~kind ~params
        ~body ~inline:attr.inline ~specialise:attr.specialise
        ~is_a_functor:attr.is_a_functor ~loc
    in
    let set_of_closures_var =
      Variable.rename let_bound_var ~append:"_set_of_closures"
    in
    let set_of_closures =
      close_functions t env (Function_decls.create [decl])
    in
    let project_closure : Flambda.project_closure =
      { set_of_closures = set_of_closures_var;
        closure_id = Closure_id.wrap closure_bound_var;
      }
    in
    Expr (Flambda.create_let set_of_closures_var set_of_closures
      (name_expr (Project_closure (project_closure))
        ~name:(Variable.unique_name let_bound_var)))
  | lam -> Expr (close t env lam)

let lambda_to_flambda ~backend ~module_ident ~size ~filename lam
      : Flambda.program =
  let module Backend = (val backend : Backend_intf.S) in
  let compilation_unit = Compilation_unit.get_current_exn () in
  let t =
    { current_unit_id = Compilation_unit.get_persistent_ident compilation_unit;
      symbol_for_global' = Backend.symbol_for_global';
      filename;
      imported_symbols = Symbol.Set.empty;
    }
  in
  let module_symbol = Backend.symbol_for_global' module_ident in
  let block_symbol =
    let linkage_name = Linkage_name.create "module_as_block" in
    Symbol.create compilation_unit linkage_name
  in
  (* The global module block is built by accessing the fields of all the
     introduced symbols. *)
  (* CR-soon mshinwell for mshinwell: Add a comment describing how modules are
     compiled. *)
  let fields =
    Array.init size (fun pos ->
      let pos_str = string_of_int pos in
      let sym_v = Variable.create ("block_symbol_" ^ pos_str) in
      let result_v = Variable.create ("block_symbol_get_" ^ pos_str) in
      let value_v = Variable.create ("block_symbol_get_field_" ^ pos_str) in
      Flambda.create_let
        sym_v (Symbol block_symbol)
         (Flambda.create_let result_v
            (Prim (Pfield 0, [sym_v], Debuginfo.none))
            (Flambda.create_let value_v
              (Prim (Pfield pos, [result_v], Debuginfo.none))
              (Var value_v))))
  in
  let module_initializer : Flambda.program_body =
    Initialize_symbol (
      block_symbol,
      Tag.create_exn 0,
      [close t Env.empty lam],
      Initialize_symbol (
        module_symbol,
        Tag.create_exn 0,
        Array.to_list fields,
        End module_symbol))
  in
  { imported_symbols = t.imported_symbols;
    program_body = module_initializer;
  }
