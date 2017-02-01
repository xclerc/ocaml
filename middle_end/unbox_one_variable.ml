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

module How_to_unbox = struct
  type t = {
    being_unboxed_to_wrapper_params_being_unboxed : Variable.t Variable.Map.t;
    add_bindings_in_wrapper : Flambda.expr -> Flambda.expr;
    new_arguments_for_call_in_wrapper : Variable.t list;
    new_params : (Variable.t * Projection.t) list;
  }

  let create () =
    { being_unboxed_to_wrapper_params_being_unboxed = Variable.Map.empty;
      add_bindings_in_wrapper = (fun expr -> expr);
      new_arguments_for_call_in_wrapper = [];
      new_params = [];
    }

  let new_specialised_args t =
    List.fold_left2 (fun new_specialised_args param projection ->
        let spec_to : Flambda.specialised_to =
          { var = None;
            projection = Some projection;
          }
        in
        Variable.Map.add param spec_to new_specialised_args)
      Variable.Map.empty
      t.new_params
      t.new_projections

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

  let merge_option t1 t2 =
    match t1, t2 with
    | None, None -> None
    | Some t1, None -> Some t1
    | None, Some t2 -> Some t2
    | Some t1, Some t2 -> Some (merge t1 t2)

  let merge_variable_map t_map =
    Variable.Map.fold (fun _param t1 t2 -> merge t1 t2) t_map (create ())
end

let how_to_unbox_core ~has_constant_ctors ~blocks ~being_unboxed =
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
        max (Array.length size) max_size)
      blocks 0
  in
  let field_arguments_for_call_in_wrapper =
    Array.to_list (Array.init (fun index ->
        Variable.create (Printf.sprintf "field%d" index))
     max_size)
  in
  let tags_to_sizes = Tag.Map.map (fun fields -> Array.length fields) blocks in
  let all_tags = Tag.Map.keys blocks in
  let sizes_to_filler_conts =
    Tag.Set.fold (fun size sizes_to_filler_conts ->
        Tag.Map.add size (Continuation.create ()) sizes_to_filler_conts)
      (Tag.Map.data tags_to_sizes)
      Tag.Map.empty
  in
  let unit_value = Variable.create "unit" in
  let n_units n =
    Array.to_list (Array.init (fun _ -> Var unit_value) n)
  in
  let all_units = n_units max_size in
  let add_bindings_in_wrapper expr =
    let is_int_cont = Continuation.create () in
    let is_block_cont = Continuation.create () in
    let join_cont = Continuation.create () in
    let new_arguments_for_call_in_wrapper = [
        is_int_in_wrapper;
        discriminant_in_wrapper;
      ] @ field_arguments_for_call_in_wrapper;
    in
    let tag = Variable.create "tag" in
    let is_int = Variable.create "is_int" in
    let is_int_switch : Flambda.switch =
      { numconsts = Numbers.Int.Set.singleton 0;
        consts = [0, is_block_cont];
        numblocks = Numbers.Int.Set.empty;
        blocks = [];
        failaction = Some is_int_cont;
      }
    in
    let add_fill_fields_conts expr =
      Tag.Map.fold (fun size filler_cont expr ->
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
              (Apply_cont (join_cont, None, [is_int; tag] @ fields_for_apply))
          in
          Let_cont {
            body =
            handler = Nonrecursive {
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
      let all_tags =
        List.map (fun tag -> Tag.to_int tag) (Tag.Set.to_list all_tags)
      in
      let consts =
        Tag.Map.fold (fun _size filler_cont consts ->
            (Tag.to_int tag, filler_cont) :: consts)
          sizes_to_filler_conts
          []
      in
      { numconsts = all_tags;
        consts = List.rev consts;
        numblocks = Numbers.Int.Set.empty;
        blocks = [];
        failaction = None;
      }
    in
    Flambda.create_let unit_value (Const (Int 0))
      (Flambda.create_let is_int
        (Prim (Pisint, [wrapper_param_being_unboxed], dbg))
        (Let_cont {
          body = Let_cont {
            body = Let_cont {
              body = Switch (is_int, is_int_switch);
              handlers = Nonrecursive {
                name = is_int_cont;
                handler = {
                  params = [];
                  handler = Apply_cont (join_cont, None,
                    [is_int; wrapper_param_being_unboxed] @ all_units);
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
                  add_fill_fields_conts (
                    Flambda.create_let tag
                      (Prim (Pgettag, [wrapper_param_being_unboxed], dbg))
                      (Switch (tag, fill_fields_switch)));
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
  let make_field_projection ~index : Projection.t * Variable.t =
    Prim (Pfield index, [being_unboxed]), fields.(index)
  in
  let fields_with_projections =
    Array.to_list (Array.init (fun index ->
        let append = string_of_int index in
        let var = Variable.rename ~append being_unboxed in
        let projection = make_field_projection ~index in
        var, projection)
      max_size)
  in
  let how_to_unbox : How_to_unbox.t =
    { being_unboxed_to_wrapper_params_being_unboxed;
      add_bindings_in_wrapper;
      new_arguments_for_call_in_wrapper;
      new_params = [
        is_int, Prim (Pisint, [being_unboxed]);
        discriminant, Prim (Pgettag, [being_unboxed]);
      ] @ fields_with_projections;
    }
  in
  Some how_to_unbox

let how_to_unbox ~begin_unboxed ~being_unboxed_approx =
  match A.check_approx_for_variant being_unboxed_approx with
  | Wrong -> None
  | Some approx ->
    let has_constant_ctors =
      match approx with
      | Blocks _ -> false
      | Blocks_and_immediates (_, imms) | Immediates imms ->
        not (Immediate.Set.is_empty imms)
    in
    let blocks =
      match approx with
      | Blocks blocks | Blocks_and_immediates (blocks, _) -> blocks
      | Immediates _ -> Tag.Map.empty
    in
    how_to_unbox_core ~has_constant_ctors ~blocks ~being_unboxed
