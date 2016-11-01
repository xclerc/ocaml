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
      : Ilambda.t =
  match const with
  | Const_block (tag, consts) ->
    (* CR-soon mshinwell for lwhite: fix location *)
    Prim (Pmakeblock (tag, Asttypes.Immutable, None),
      List.map eliminate_const_block consts, Location.none)
  | Const_base _
  | Const_pointer _
  | Const_immstring _
  | Const_float_array _ -> Const const

let rec close_const t env (const : Lambda.structured_constant) : Flambda.named =
  match const with
  | Const_base (Const_int c) -> Const (Int c)
  | Const_base (Const_char c) -> Const (Char c)
  | Const_base (Const_string (s, _)) ->
    if Config.safe_string then Allocated_const (Immutable_string s)
    else Allocated_const (String s)
  | Const_base (Const_float c) ->
    Allocated_const (Float (float_of_string c))
  | Const_base (Const_int32 c) -> Allocated_const (Int32 c)
  | Const_base (Const_int64 c) -> Allocated_const (Int64 c)
  | Const_base (Const_nativeint c) ->
    Allocated_const (Nativeint c)
  | Const_pointer c -> Const (Const_pointer c)
  | Const_immstring c -> Allocated_const (Immutable_string c)
  | Const_float_array c ->
    Allocated_const (Immutable_float_array (List.map float_of_string c))
  | Const_block _ ->
    Expr (close t env (eliminate_const_block const))

and close t env (lam : Ilambda.t) : Flambda.t =
  match lam with
  | Let (id, defining_expr, body) ->
    let var = Variable.create_with_same_name_as_ident id in
    let defining_expr = close_let_bound_expression t var env defining_expr in
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
  | Apply { func; args; loc; should_be_tailcall = _;
      inlined; specialised; } ->
    Apply ({
      func = Env.find_var_or_mutable_var_exn env func;
      args = Env.find_vars_or_mutable_vars_exn env args;
      kind = Indirect;
      dbg = Debuginfo.from_location loc;
      inline = inlined;
      specialise = specialised;
    })
  | Let_rec (defs, body) ->
    let env =
      List.fold_right (fun (id,  _) env ->
          Env.add_var env id (Variable.create_with_same_name_as_ident id))
        defs env
    in
    let function_declarations =
      (* Functions will be named after the corresponding identifier in the
         [let rec]. *)
      List.map (function
          | (let_rec_ident,
              { kind; params; body; attr; loc; free_idents_of_body; }) ->
            let closure_bound_var =
              Variable.create_with_same_name_as_ident let_rec_ident
            in
            let function_declaration =
              Function_decl.create ~let_rec_ident:(Some let_rec_ident)
                ~closure_bound_var ~kind ~params ~body
                ~inline:attr.inline ~specialise:attr.specialise
                ~is_a_functor:attr.is_a_functor ~loc ~free_idents_of_body
            in
            function_declaration)
        defs
    in
    (* We eliminate the [let rec] construction, instead producing a normal
       [Let] that binds a set of closures containing all of the functions.
       ([let rec] on non-functions was removed in [Prepare_lambda].)
    *)
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
  | Let_cont (i, ids, handler, body) ->
    let cont = Continuation.create () in
    let env = Env.add_continuation env i cont in
    let vars = List.map (Variable.create_with_same_name_as_ident) ids in
    Let_cont (cont, vars, close t env body,
      close t (Env.add_vars env ids vars) handler)
  | Apply_cont (cont, args) ->
    Lift_code.lifting_helper (close_list t env args)
      ~evaluation_order:`Right_to_left
      ~name:"apply_cont_arg"
      ~create_body:(fun args ->
        let cont = Env.find_continuation env cont in
        Apply_cont (cont, args))
  | Switch (arg, sw) ->
    let scrutinee = Variable.create "switch" in
    let aux (i, lam) = i, close t env lam in
    let zero_to_n = Numbers.Int.zero_to_n in
    Flambda.create_let scrutinee (Expr (close t env arg))
      (Switch (scrutinee,
        { numconsts = zero_to_n (sw.numconsts - 1);
          consts = List.map aux sw.consts;
          numblocks = zero_to_n (sw.numblocks - 1);
          blocks = List.map aux sw.blocks;
          failaction = Misc.may_map (close t env) sw.failaction;
        }))
  | Event (lam, _) -> close t env lam

and close_named t env (named : Ilambda.named) : Flambda.named =
  match named with
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
  | Const cst -> close_const t env cst
  | Function { kind; params; body; attr; loc; free_idents_of_body; } ->
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
          ~free_idents_of_body
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
    let args = Env.find_vars_or_mutable_vars env args in
    Prim (p, args, loc)

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
(* CR mshinwell: think about this
    (* If the function is the wrapper for a function with an optional
       argument with a default value, make sure it always gets inlined.
       CR-someday pchambart: eta-expansion wrapper for a primitive are
       not marked as stub but certainly should *)
    let stub, body =
      match Function_decl.primitive_wrapper decl with
      | None -> false, body
      | Some wrapper_body -> true, wrapper_body
    in
*)
    let stub = false in
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
      (lam : Ilambda.named) : Flambda.named =
  match lam with
  | Function { kind; params; body; attr; loc; free_idents_of_body; } ->
    (* Ensure that [let] and [let rec]-bound functions have appropriate
       names. *)
    let closure_bound_var = Variable.rename let_bound_var in
    let decl =
      Function_decl.create ~let_rec_ident ~closure_bound_var ~kind ~params
        ~body ~inline:attr.inline ~specialise:attr.specialise
        ~is_a_functor:attr.is_a_functor ~loc ~free_idents_of_body
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

let ilambda_to_flambda ~backend ~module_ident ~size ~filename
      (ilam, ilam_result_cont) : Flambda.program =
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
      let continuation = Continuation.create () in
      let flam =
        Flambda.create_let
          sym_v (Symbol block_symbol)
          (Flambda.create_let result_v
              (Prim (Pfield 0, [sym_v], Debuginfo.none))
              (Flambda.create_let value_v
                (Prim (Pfield pos, [result_v], Debuginfo.none))
                (Apply_cont (continuation, [value_v]))))
      in
      flam, continuation)
  in
  let module_initializer : Flambda.program_body =
    Initialize_symbol (
      block_symbol,
      Tag.create_exn 0,
      [close t Env.empty ilam, ilam_result_cont],
      Initialize_symbol (
        module_symbol,
        Tag.create_exn 0,
        Array.to_list fields,
        End module_symbol))
  in
  { imported_symbols = t.imported_symbols;
    program_body = module_initializer;
  }
