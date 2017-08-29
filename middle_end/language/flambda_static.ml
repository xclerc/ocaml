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
