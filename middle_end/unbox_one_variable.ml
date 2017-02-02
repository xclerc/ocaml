(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2017 OCamlPro SAS                                          *)
(*   Copyright 2017 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module A = Simple_value_approx

module How_to_unbox = struct
  (* CR mshinwell: We need a comment about ordering (e.g. when two of these
     are composed).  Relevant for [Unbox_returns] in particular.  We should
     maybe try to statically enforce the right ordering. *)
  type t = {
    being_unboxed_to_wrapper_params_being_unboxed : Variable.t Variable.Map.t;
    add_bindings_in_wrapper : Flambda.expr -> Flambda.expr;
    new_arguments_for_call_in_wrapper : Variable.t list;
    new_params : (Variable.t * Projection.t) list;
    build_boxed_value_from_new_params :
      (Variable.t * (Flambda.expr -> Flambda.expr)) list;
  }

  let create () =
    { being_unboxed_to_wrapper_params_being_unboxed = Variable.Map.empty;
      add_bindings_in_wrapper = (fun expr -> expr);
      new_arguments_for_call_in_wrapper = [];
      new_params = [];
      build_boxed_value_from_new_params = [];
    }

  let new_specialised_args t =
    List.fold_left (fun new_specialised_args (param, projection) ->
        let spec_to : Flambda.specialised_to =
          { var = None;
            projection = Some projection;
          }
        in
        Variable.Map.add param spec_to new_specialised_args)
      Variable.Map.empty
      t.new_params

  let merge t1 t2 =
    { being_unboxed_to_wrapper_params_being_unboxed =
        Variable.Map.union (fun _ param1 param2 ->
            assert (Variable.equal param1 param2);
            Some param1)
          t1.being_unboxed_to_wrapper_params_being_unboxed
          t2.being_unboxed_to_wrapper_params_being_unboxed;
      add_bindings_in_wrapper = (fun expr ->
        t2.add_bindings_in_wrapper (
          t1.add_bindings_in_wrapper expr));
      new_arguments_for_call_in_wrapper =
        t1.new_arguments_for_call_in_wrapper
          @ t2.new_arguments_for_call_in_wrapper;
      new_params = t1.new_params @ t2.new_params;
    }

  let merge_variable_map t_map =
    Variable.Map.fold (fun _param t1 t2 -> merge t1 t2) t_map (create ())
end

let how_to_unbox_core ~has_constant_ctors:_ ~blocks ~being_unboxed
      : How_to_unbox.t =
  let dbg = Debuginfo.none in
  let wrapper_param_being_unboxed = Variable.rename being_unboxed in
  let being_unboxed_to_wrapper_params_being_unboxed =
    Variable.Map.add being_unboxed wrapper_param_being_unboxed
      Variable.Map.empty
  in
  let is_int = Variable.rename ~append:"_is_int" being_unboxed in
  let is_int_in_wrapper = Variable.rename is_int in
  (* CR-soon mshinwell: On [discriminant] add information that tells us
     about the individual unboxed field parameters _given that_ we are
     in some particular case of a match on [discriminant] (GADT-style). *)
  let discriminant = Variable.rename ~append:"_discr" being_unboxed in
  let discriminant_in_wrapper = Variable.rename discriminant in
  let max_size =
    Tag.Map.fold (fun _tag fields max_size ->
        max (Array.length fields) max_size)
      blocks 0
  in
  let field_arguments_for_call_in_wrapper =
    Array.to_list (Array.init max_size (fun index ->
        Variable.create (Printf.sprintf "field%d" index)))
  in
  let is_int_in_wrapper' = Variable.rename is_int_in_wrapper in
  let discriminant_in_wrapper' = Variable.rename discriminant_in_wrapper in
  let new_arguments_for_call_in_wrapper = [
      is_int_in_wrapper';
      discriminant_in_wrapper';
    ] @ field_arguments_for_call_in_wrapper
  in
  let tags_to_sizes = Tag.Map.map (fun fields -> Array.length fields) blocks in
  let all_tags = Tag.Map.keys blocks in
  let sizes_to_filler_conts =
    List.fold_left (fun sizes_to_filler_conts size ->
        Numbers.Int.Map.add size (Continuation.create ()) sizes_to_filler_conts)
      Numbers.Int.Map.empty
      (Tag.Map.data tags_to_sizes)
  in
  let tags_to_sizes_and_boxing_conts =
    Tag.Map.map (fun size -> size, Continuation.create ()) tags_to_sizes
  in
  let unit_value = Variable.create "unit" in
  let all_units = Array.to_list (Array.init max_size (fun _ -> unit_value)) in
  let add_bindings_in_wrapper expr =
    let is_int_cont = Continuation.create () in
    let is_block_cont = Continuation.create () in
    let join_cont = Continuation.create () in
    let tag = Variable.create "tag" in
    let is_int_switch : Flambda.switch =
      { numconsts = Numbers.Int.Set.singleton 0;
        consts = [0, is_block_cont];
        numblocks = Numbers.Int.Set.empty;
        blocks = [];
        failaction = Some is_int_cont;
      }
    in
    let add_fill_fields_conts expr =
      Numbers.Int.Map.fold (fun size filler_cont expr : Flambda.expr ->
          let fields =
            Array.init max_size (fun index ->
              if index < size then
                let name = Printf.sprintf "_field%d" index in
                index, Some (Variable.rename ~append:name being_unboxed)
              else
                index, None)
          in
          let fields_for_apply =
            List.map (fun (_index, var_opt) ->
                match var_opt with
                | None -> unit_value
                | Some var -> var)
              (Array.to_list fields)
          in
          let filler : Flambda.expr =
            Array.fold_right (fun (index, var_opt) filler ->
                match var_opt with
                | None -> filler
                | Some var ->
                    Flambda.create_let var
                      (Prim (Pfield index, [wrapper_param_being_unboxed], dbg))
                      filler)
              fields
              (Flambda.Apply_cont (join_cont, None,
                [is_int_in_wrapper; tag] @ fields_for_apply))
          in
          Let_cont {
            body = expr;
            handlers = Nonrecursive {
              name = filler_cont;
              handler = {
                params = [];
                stub = false;
                is_exn_handler = false;
                handler = filler;
                specialised_args = Variable.Map.empty;
              };
            }
          })
        sizes_to_filler_conts
        expr      
    in
    let fill_fields_switch : Flambda.switch =
      let numconsts =
        Tag.Set.fold (fun tag numconsts ->
            Numbers.Int.Set.add (Tag.to_int tag) numconsts)
          all_tags
          Numbers.Int.Set.empty
      in
      let consts =
        Numbers.Int.Map.fold (fun size filler_cont consts ->
            Tag.Map.fold (fun tag fields consts ->
                if Array.length fields = size then
                  (Tag.to_int tag, filler_cont) :: consts
                else
                  consts)
              blocks
              consts)
          sizes_to_filler_conts
          []
      in
      { numconsts;
        consts = List.rev consts;
        numblocks = Numbers.Int.Set.empty;
        blocks = [];
        failaction = None;
      }
    in
    Flambda.create_let unit_value (Const (Int 0))
      (Flambda.create_let is_int_in_wrapper
        (Prim (Pisint, [wrapper_param_being_unboxed], dbg))
        (Let_cont {
          body = Let_cont {
            body = Let_cont {
              body = Switch (is_int_in_wrapper, is_int_switch);
              handlers = Nonrecursive {
                name = is_int_cont;
                handler = {
                  params = [];
                  handler = Apply_cont (join_cont, None,
                    [is_int_in_wrapper; wrapper_param_being_unboxed]
                      @ all_units);
                  stub = false;
                  is_exn_handler = false;
                  specialised_args = Variable.Map.empty;
                };
              };
            };
            handlers = Nonrecursive {
              name = is_block_cont;
              handler = {
                params = [];
                handler =
                  Flambda.create_let tag
                    (Prim (Pgettag, [wrapper_param_being_unboxed], dbg))
                    (add_fill_fields_conts (
                      (Switch (tag, fill_fields_switch))));
                stub = false;
                is_exn_handler = false;
                specialised_args = Variable.Map.empty;
              };
            };
          };
          handlers = Nonrecursive {
            name = join_cont;
            handler = {
              params = new_arguments_for_call_in_wrapper;
              handler = expr;
              stub = false;
              is_exn_handler = false;
              specialised_args = Variable.Map.empty;
            };
          }
        }))
  in
  let fields_with_projections =
    Array.to_list (Array.init max_size (fun index ->
      let append = string_of_int index in
      let var = Variable.rename ~append being_unboxed in
      let projection : Projection.t = Field (index, being_unboxed) in
      var, projection))
  in
  (* CR mshinwell: This next section is only needed for [Unbox_returns] at
     present; we shouldn't run it unless required. *)
  let boxing_is_int_cont = Continuation.create () in
  let boxing_is_block_cont = Continuation.create () in
  let boxing_is_int_switch : Flambda.switch =
    { numconsts = Numbers.Int.Set.singleton 0;
      consts = [0, boxing_is_block_cont];
      numblocks = Numbers.Int.Set.empty;
      blocks = [];
      failaction = Some boxing_is_int_cont;
    }
  in
  let boxing_switch : Flambda.switch =
    let numconsts =
      Tag.Set.fold (fun tag numconsts ->
          Numbers.Int.Set.add (Tag.to_int tag) numconsts)
        all_tags
        Numbers.Int.Set.empty
    in
    let consts =
      Numbers.Int.Map.fold (fun size boxing_cont consts ->
          Tag.Map.fold (fun tag fields consts ->
              if Array.length fields = size then
                (Tag.to_int tag, boxing_cont) :: consts
              else
                consts)
            blocks
            consts)
        sizes_to_boxing_conts
        []
    in
    { numconsts;
      consts = List.rev consts;
      numblocks = Numbers.Int.Set.empty;
      blocks = [];
      failaction = None;
    }
  in
  let build_boxed_value_from_new_params =
    let boxed = Variable.rename ~append:"_boxed" being_unboxed in
    let join_cont = Continuation.create () in
    let build (expr : Flambda.expr) : Flambda.expr =
      let add_boxing_conts expr =
        Numbers.Int.Map.fold (fun tag (size, boxing_cont) expr : Flambda.expr ->
            let boxed = Variable.rename boxed in
            let fields =
              List.rev (List.fold_left (fun (fields, index) (field, _proj) ->
                  if index >= size then fields, index + 1
                  else (field :: fields), index + 1)
                ([], 0)
                fields_with_projections)
            in
            Flambda.create_let boxed
              (Prim (Pmakeblock (tag, Immutable, Pgenval), fields, dbg))
              (Flambda.Apply_cont (join_cont, None, [boxed])))
          tags_to_sizes_and_boxing_consts
          expr
      in
      (* CR mshinwell: This structure of code is kind of the same as that
         above---maybe we can share something. *)
      Let_cont {
        body = Let_cont {
          body = Let_cont {
            body = Switch (is_int, boxing_is_int_switch);
            handlers = Nonrecursive {
              name = boxing_is_block_cont;
              handler = {
                params = [];
                handler =
                  add_boxing_conts (Switch (discriminant, boxing_switch));
                stub = false;
                is_exn_handler = false;
                specialised_args = Variable.Map.empty;
              };
            };
          };
          handlers = Nonrecursive {
            name = boxing_is_int_cont;
            handler = {
              params = [];
              handler = Apply_cont (join_cont, None, [discriminant]);
              stub = false;
              is_exn_handler = false;
              specialised_args = Variable.Map.empty;
            };
          };
        };
        handlers = Nonrecursive {
          name = join_cont;
          handler = {
            params = boxed;
            handler = expr;
            stub = false;
            is_exn_handler = false;
            specialised_args = Variable.Map.empty;
          };
        };
      }
    in
    [boxed, build]
  in
  { being_unboxed_to_wrapper_params_being_unboxed;
    add_bindings_in_wrapper;
    new_arguments_for_call_in_wrapper;
    new_params = [
      is_int, Projection.Prim (Pisint, [being_unboxed]);
      discriminant, Projection.Prim (Pgettag, [being_unboxed]);
    ] @ fields_with_projections;
    build_boxed_value_from_new_params;
  }

let how_to_unbox ~being_unboxed ~being_unboxed_approx =
  match A.check_approx_for_variant being_unboxed_approx with
  | Wrong -> None
  | Ok approx ->
    let has_constant_ctors =
      match approx with
      | Blocks _ -> false
      | Blocks_and_immediates (_, imms) | Immediates imms ->
        not (A.Unionable.Immediate.Set.is_empty imms)
    in
    let blocks =
      match approx with
      | Blocks blocks | Blocks_and_immediates (blocks, _) -> blocks
      | Immediates _ -> Tag.Map.empty
    in
    if Tag.Map.is_empty blocks then None
    else Some (how_to_unbox_core ~has_constant_ctors ~blocks ~being_unboxed)
