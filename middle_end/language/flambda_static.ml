(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module Program = struct
  let all_lifted_constant_sets_of_closures program =
    let set = ref Set_of_closures_id.Set.empty in
    List.iter (function
        | (_, Flambda.Set_of_closures {
            function_decls = { set_of_closures_id } }) ->
          set := Set_of_closures_id.Set.add set_of_closures_id !set
        | _ -> ())
      (all_lifted_constants program);
    !set

  let all_sets_of_closures program =
    let list = ref [] in
    Flambda_iterators.iter_on_set_of_closures_of_program program
      ~f:(fun ~constant:_ set_of_closures ->
          list := set_of_closures :: !list);
    !list

  let all_sets_of_closures_map program =
    let r = ref Set_of_closures_id.Map.empty in
    Flambda_iterators.iter_on_set_of_closures_of_program program
      ~f:(fun ~constant:_ set_of_closures ->
        r := Set_of_closures_id.Map.add
            set_of_closures.function_decls.set_of_closures_id
            set_of_closures !r);
    !r

  let all_function_decls_indexed_by_set_of_closures_id program =
    Set_of_closures_id.Map.map
      (fun { Flambda. function_decls; _ } -> function_decls)
      (all_sets_of_closures_map program)

  let all_function_decls_indexed_by_closure_id program =
    let aux_fun function_decls fun_var _ map =
      let closure_id = Closure_id.wrap fun_var in
      Closure_id.Map.add closure_id function_decls map
    in
    let aux _ ({ function_decls; _ } : Flambda.Set_of_closures.t) map =
      Variable.Map.fold (aux_fun function_decls) function_decls.funs map
    in
    Set_of_closures_id.Map.fold aux (all_sets_of_closures_map program)
      Closure_id.Map.empty

  let all_lifted_constants (program : Flambda_static.Program.t) =
    let rec loop (program : Flambda_static.Program.t_body) =
      match program with
      | Let_symbol (symbol, decl, program) -> (symbol, decl) :: (loop program)
      | Let_rec_symbol (decls, program) ->
        List.fold_left (fun l (symbol, decl) -> (symbol, decl) :: l)
          (loop program)
          decls
      | Initialize_symbol (_, _, _, program)
      | Effect (_, _, program) -> loop program
      | End _ -> []
    in
    loop program.program_body

  let all_lifted_constants_as_map program =
    Symbol.Map.of_list (all_lifted_constants program)

  let initialize_symbols (program : Flambda_static.Program.t) =
    let rec loop (program : Flambda_static.Program.t_body) =
      match program with
      | Initialize_symbol (symbol, tag, fields, program) ->
        (symbol, tag, fields) :: (loop program)
      | Effect (_, _, program)
      | Let_symbol (_, _, program)
      | Let_rec_symbol (_, program) -> loop program
      | End _ -> []
    in
    loop program.program_body

  let imported_symbols (program : Flambda_static.Program.t) =
    program.imported_symbols

  let needed_import_symbols (program : Flambda_static.Program.t) =
    let dependencies = Flambda.free_symbols_program program in
    let defined_symbol =
      Symbol.Set.union
        (Symbol.Set.of_list
          (List.map fst (all_lifted_constants program)))
        (Symbol.Set.of_list
          (List.map (fun (s, _, _) -> s) (initialize_symbols program)))
    in
    Symbol.Set.diff dependencies defined_symbol

  let introduce_needed_import_symbols program : Flambda_static.Program.t =
    { program with
      imported_symbols = needed_import_symbols program;
    }

  let root_symbol (program : Flambda_static.Program.t) =
    let rec loop (program : Flambda_static.Program.t_body) =
      match program with
      | Effect (_, _, program)
      | Let_symbol (_, _, program)
      | Let_rec_symbol (_, program)
      | Initialize_symbol (_, _, _, program) -> loop program
      | End root ->
        root
    in
    loop program.program_body

  let make_closure_map program =
    let map = ref Closure_id.Map.empty in
    let add_set_of_closures ~constant:_ : Flambda.Set_of_closures.t -> unit =
        fun { function_decls } ->
      Variable.Map.iter (fun var _ ->
          let closure_id = Closure_id.wrap var in
          map := Closure_id.Map.add closure_id function_decls !map)
        function_decls.funs
    in
    Flambda_iterators.iter_on_set_of_closures_of_program
      program
      ~f:add_set_of_closures;
    !map
end


let iter_exprs_at_toplevel_of_program (program : Flambda_static0.Program.t) ~f =
  let rec loop (program : Flambda_static0.Program_body.t) =
    match program with
    | Let_symbol (_, Set_of_closures set_of_closures, program) ->
      Variable.Map.iter (fun _ (function_decl : F0.Function_declaration.t) ->
          f ~continuation_arity:function_decl.return_arity
            function_decl.continuation_param function_decl.body)
        set_of_closures.function_decls.funs;
      loop program
    | Let_rec_symbol (defs, program) ->
      List.iter (function
          | (_, CDV.Set_of_closures set_of_closures) ->
            Variable.Map.iter
              (fun _ (function_decl : F0.Function_declaration.t) ->
                f ~continuation_arity:function_decl.return_arity
                  function_decl.continuation_param function_decl.body)
              set_of_closures.function_decls.funs
          | _ -> ()) defs;
      loop program
    | Let_symbol (_, _, program) ->
      loop program
    | Initialize_symbol (_, _, fields, program) ->
      List.iter (fun (field, cont) ->
          f ~continuation_arity:[Flambda_kind.value ()] cont field)
        fields;
      loop program
    | Effect (expr, cont, program) ->
      f ~continuation_arity:[Flambda_kind.value ()] cont expr;
      loop program
    | End _ -> ()
  in
  loop program.program_body

(* CR mshinwell: think of a better name *)
let iter_exprs_at_toplevels_in_program (program : Flambda_static0.Program.t) ~f =
  iter_exprs_at_toplevel_of_program program
    ~f:(fun ~continuation_arity cont expr ->
      let rec iter_expr ~continuation_arity cont expr =
        iter_named (fun (named : Named.t) ->
            match named with
            | Set_of_closures set_of_closures ->
              Variable.Map.iter
                (fun _ (function_decl : F0.Function_declaration.t) ->
                  iter_expr ~continuation_arity:function_decl.return_arity
                    function_decl.continuation_param
                    function_decl.body)
                set_of_closures.function_decls.funs
            | _ -> ())
          expr;
        f ~continuation_arity cont expr
      in
      iter_expr ~continuation_arity cont expr)

let iter_named_of_program program ~f =
  iter_exprs_at_toplevel_of_program program
    ~f:(fun ~continuation_arity:_ _ e -> iter_named f e)

let iter_on_set_of_closures_of_program
      (program : Flambda_static0.Program.t) ~f =
  let rec loop (program : Flambda_static0.Program_body.t) =
    match program with
    | Let_symbol (_, Set_of_closures set_of_closures, program) ->
      f ~constant:true set_of_closures;
      Variable.Map.iter (fun _ (function_decl : F0.Function_declaration.t) ->
          iter_on_sets_of_closures (f ~constant:false) function_decl.body)
        set_of_closures.function_decls.funs;
      loop program
    | Let_rec_symbol (defs, program) ->
      List.iter (function
          | (_, CDV.Set_of_closures set_of_closures) ->
            f ~constant:true set_of_closures;
            Variable.Map.iter
              (fun _ (function_decl : F0.Function_declaration.t) ->
                iter_on_sets_of_closures (f ~constant:false) function_decl.body)
              set_of_closures.function_decls.funs
          | _ -> ()) defs;
      loop program
    | Let_symbol (_, _, program) ->
      loop program
    | Initialize_symbol (_, _, fields, program) ->
      List.iter (fun (field, _cont) ->
          iter_on_sets_of_closures (f ~constant:false) field)
        fields;
      loop program
    | Effect (expr, _cont, program) ->
      iter_on_sets_of_closures (f ~constant:false) expr;
      loop program
    | End _ -> ()
  in
  loop program.program_body

let iter_constant_defining_values_on_program
      (program : Flambda_static0.Program.t) ~f =
  let rec loop (program : Flambda_static0.Program_body.t) =
    match program with
    | Let_symbol (_, const, program) ->
      f const;
      loop program
    | Let_rec_symbol (defs, program) ->
      List.iter (fun (_, const) -> f const) defs;
      loop program
    | Initialize_symbol (_, _, _, program) ->
      loop program
    | Effect (_, _, program) ->
      loop program
    | End _ -> ()
  in
  loop program.program_body

let iter_apply_on_program program ~f =
  iter_exprs_at_toplevel_of_program program
    ~f:(fun ~continuation_arity:_ _cont expr ->
      iter (function
          | Apply apply -> f apply
          | _ -> ())
        (fun _ -> ())
        expr)




let map_sets_of_closures_of_program (program : Flambda_static0.Program.t)
    ~(f : F0.Set_of_closures.t -> F0.Set_of_closures.t) =
  let rec loop (program : Flambda_static0.Program_body.t)
        : Flambda_static0.Program_body.t =
    let map_constant_set_of_closures (set_of_closures:F0.Set_of_closures.t) =
      let done_something = ref false in
      let function_decls =
        let funs =
          Variable.Map.map (fun
                  (function_decl : F0.Function_declaration.t) ->
              let body = map_sets_of_closures ~f function_decl.body in
              if body == function_decl.body then
                function_decl
              else begin
                done_something := true;
                F0.Function_declaration.update_body function_decl ~body
              end)
            set_of_closures.function_decls.funs
        in
        if not !done_something then
          set_of_closures.function_decls
        else
          F0.Function_declarations.update set_of_closures.function_decls
            ~funs
      in
      let new_set_of_closures = f set_of_closures in
      if new_set_of_closures == set_of_closures then
        set_of_closures
      else
        F0.Set_of_closures.create ~function_decls
          ~free_vars:set_of_closures.free_vars
          ~direct_call_surrogates:set_of_closures.direct_call_surrogates
    in
    match program with
    | Let_symbol (symbol, Set_of_closures set_of_closures, program') ->
      let new_set_of_closures = map_constant_set_of_closures set_of_closures in
      let new_program' = loop program' in
      if new_set_of_closures == set_of_closures
          && new_program' == program' then
        program
      else
        let const = CDV.create_set_of_closures new_set_of_closures in
        Let_symbol (symbol, const, new_program')
    | Let_symbol (symbol, const, program') ->
      let new_program' = loop program' in
      if new_program' == program' then
        program
      else
        Let_symbol (symbol, const, new_program')
    | Let_rec_symbol (defs, program') ->
      let done_something = ref false in
      let defs =
        List.map (function
            | (var, CDV.Set_of_closures set_of_closures) ->
              let new_set_of_closures =
                map_constant_set_of_closures set_of_closures
              in
              if not (new_set_of_closures == set_of_closures) then begin
                done_something := true
              end;
              let const = CDV.create_set_of_closures new_set_of_closures in
              var, const
            | def -> def)
          defs
      in
      let new_program' = loop program' in
      if new_program' == program' && not !done_something then
        program
      else
        Let_rec_symbol (defs, loop program')
    | Initialize_symbol (symbol, tag, fields, program') ->
      let done_something = ref false in
      let fields =
        List.map (fun (field, cont) ->
            let new_field = map_sets_of_closures field ~f in
            if not (new_field == field) then begin
              done_something := true
            end;
            new_field, cont)
          fields
      in
      let new_program' = loop program' in
      if new_program' == program' && not !done_something then
        program
      else
        Initialize_symbol (symbol, tag, fields, new_program')
    | Effect (expr, cont, program') ->
      let new_expr = map_sets_of_closures expr ~f in
      let new_program' = loop program' in
      if new_expr == expr && new_program' == program' then
        program
      else
        Effect (new_expr, cont, new_program')
    | End _ -> program
  in
  { program with
    program_body = loop program.program_body;
  }

let map_exprs_at_toplevel_of_program (program : Flambda_static0.Program.t)
    ~(f : Expr.t -> Expr.t) =
  let rec loop (program : Flambda_static0.Program_body.t)
        : Flambda_static0.Program_body.t =
    let map_constant_set_of_closures (set_of_closures:F0.Set_of_closures.t) =
      let done_something = ref false in
      let funs =
        Variable.Map.map (fun (function_decl : F0.Function_declaration.t) ->
            let body = f function_decl.body in
            if body == function_decl.body then
              function_decl
            else begin
              done_something := true;
              F0.Function_declaration.update_body function_decl ~body
            end)
          set_of_closures.function_decls.funs
      in
      if not !done_something then
        set_of_closures
      else
        let function_decls =
          F0.Function_declarations.update set_of_closures.function_decls
            ~funs
        in
        F0.Set_of_closures.create ~function_decls
          ~free_vars:set_of_closures.free_vars
          ~direct_call_surrogates:set_of_closures.direct_call_surrogates
    in
    (* CR-soon mshinwell: code very similar to the above function *)
    match program with
    | Let_symbol (symbol, Set_of_closures set_of_closures, program') ->
      let new_set_of_closures = map_constant_set_of_closures set_of_closures in
      let new_program' = loop program' in
      if new_set_of_closures == set_of_closures
          && new_program' == program' then
        program
      else
        let const = CDV.create_set_of_closures new_set_of_closures in
        Let_symbol (symbol, const, new_program')
    | Let_symbol (symbol, const, program') ->
      let new_program' = loop program' in
      if new_program' == program' then
        program
      else
        Let_symbol (symbol, const, new_program')
    | Let_rec_symbol (defs, program') ->
      let done_something = ref false in
      let defs =
        List.map (function
            | (var, CDV.Set_of_closures set_of_closures) ->
              let new_set_of_closures =
                map_constant_set_of_closures set_of_closures
              in
              if not (new_set_of_closures == set_of_closures) then begin
                done_something := true
              end;
              let const = CDV.create_set_of_closures new_set_of_closures in
              var, const
            | def -> def)
          defs
      in
      let new_program' = loop program' in
      if new_program' == program' && not !done_something then
        program
      else
        Let_rec_symbol (defs, new_program')
    | Initialize_symbol (symbol, tag, fields, program') ->
      let done_something = ref false in
      let fields =
        List.map (fun (field, cont) ->
            let new_field = f field in
            if not (new_field == field) then begin
              done_something := true
            end;
            new_field, cont)
          fields
      in
      let new_program' = loop program' in
      if new_program' == program' && not !done_something then
        program
      else
        Initialize_symbol (symbol, tag, fields, new_program')
    | Effect (expr, cont, program') ->
      let new_expr = f expr in
      let new_program' = loop program' in
      if new_expr == expr && new_program' == program' then
        program
      else
        Effect (new_expr, cont, new_program')
    | End _ -> program
  in
  { program with
    program_body = loop program.program_body;
  }

let map_named_of_program (program : Flambda_static0.Program.t)
      ~(f : Variable.t -> Named.t -> Named.t)
      : Flambda_static0.Program.t =
  map_exprs_at_toplevel_of_program program
      ~f:(fun expr -> map_named_with_id f expr)
