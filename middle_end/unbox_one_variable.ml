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
    (* CR mshinwell: combine these next two?  They must be in sync *)
    new_params : Variable.t list;
    new_projections : Projection.t list;
    wrap_body : Flambda.expr -> Flambda.expr;
  }

  let create () =
    { being_unboxed_to_wrapper_params_being_unboxed = Variable.Map.empty;
      add_bindings_in_wrapper = (fun expr -> expr);
      new_arguments_for_call_in_wrapper = [];
      new_params = [];
      new_projections = [];
      wrap_body = (fun expr -> expr);
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
      new_projections = t1.new_projections @ t2.new_projections;
      wrap_body = (fun expr -> t2.wrap_body (t1.wrap_body expr));
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
  let max_tag_int = Obj.last_non_constant_constructor_tag in
  let for_discriminant =
    (* See the [Switch] case in [Inline_and_simplify] for details of the
       encoding of the variant discriminant. *)
    if not has_constant_ctors then None
    else
      let discriminant = Variable.rename ~append:"_discr" being_unboxed in
      let discriminant_in_wrapper = Variable.rename discriminant in
      let is_constant_ctor =
        Variable.rename ~append:"_is_const" being_unboxed
      in
      let isint_projection : Projection.t * Variable.t =
        Prim (Pisint, [being_unboxed]), is_constant_ctor
      in
      let switch_projection : Projection.t * Variable.t =
        Switch being_unboxed, discriminant
      in
      let add_bindings_in_wrapper expr =
        let max_tag_plus_one = Variable.create "max_tag" in
        let is_int_cont = Continuation.create () in
        let is_block_cont = Continuation.create () in
        let join_cont = Continuation.create () in
        let shifted_tag = Variable.create "shifted_tag" in
        let tag = Variable.create "tag" in
        let is_int = Variable.create "is_int" in
        let switch : Flambda.switch =
          { numconsts = Numbers.Int.Set.singleton 0;
            consts = [0, is_block_cont];
            numblocks = Numbers.Int.Set.empty;
            blocks = [];
            failaction = Some is_int_cont;
          }
        in
        (* The following examines the value in [wrapper_param_being_unboxed]
           and creates the discriminant from it. *)
        Flambda.create_let max_tag_plus_one (Const (Int (max_tag_int + 1)))
          (Let_cont {
            body = Let_cont {
              body = Let_cont {
                body =
                  Flambda.create_let is_int
                    (Prim (Pisint, [wrapper_param_being_unboxed], dbg))
                    (Switch (is_int, switch));
                handlers = Nonrecursive {
                  name = is_int_cont;
                  handler = {
                    params = [];
                    handler =
                      Flambda.create_let shifted_tag
                        (Prim (Paddint,
                          [wrapper_param_being_unboxed; max_tag_plus_one],
                          dbg))
                        (Apply_cont (join_cont, None, [shifted_tag]));
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
                  (* This body could theoretically use [Switch], which for
                     direct calls could be optimised out entirely, but for
                     indirect calls might be rather verbose.  (It would also be
                     a nuisance to construct, requiring one continuation per
                     tag.) *)
                  handler =
                    Flambda.create_let tag
                      (Prim (Pgettag, [wrapper_param_being_unboxed], dbg))
                      (Apply_cont (join_cont, None, [tag]));
                  stub = false;
                  is_exn_handler = false;
                  specialised_args = Variable.Map.empty;
                };
              };
            };
            handlers = Nonrecursive {
              name = join_cont;
              handler = {
                params = [discriminant_in_wrapper];
                handler = expr;
                stub = false;
                is_exn_handler = false;
                specialised_args = Variable.Map.empty;
              };
            }
          })
      in
      let wrap_body expr =
        let max_tag = Variable.create "max_tag" in
        Flambda.create_let max_tag (Const (Int max_tag_int))
          (Flambda.create_let is_constant_ctor
            (Prim (Pintcomp Cgt, [discriminant; max_tag], dbg))
            expr)
      in
      let how_to_unbox : How_to_unbox.t =
        { being_unboxed_to_wrapper_params_being_unboxed;
          add_bindings_in_wrapper;
          new_arguments_for_call_in_wrapper = [discriminant_in_wrapper];
          new_params = [discriminant];
          new_projections = [isint_projection; switch_projection];
          wrap_body;
        }
      in
      Some how_to_unbox
  in
  let for_fields =
    let max_size =
      Tag.Map.fold (fun _tag fields max_size ->
          max (Array.length size) max_size)
        blocks 0
    in
    let fields =
      Array.init max_size (fun index ->
        let name = Printf.sprintf "_field%d" index in
        Variable.rename ~append:name being_unboxed)
    in
    let fields_in_wrapper_with_bindings =
      Array.to_list (Array.init max_size
        (fun index ->
          let field_in_wrapper = Variable.rename fields.(index) in
          let binding : Flambda.named =
            Prim (Pfield index, [wrapper_param_being_unboxed], dbg)
          in
          field_in_wrapper, binding))
    in
    let add_bindings_in_wrapper body =
      List.fold_left (fun body (field, binding) ->
          Flambda.create_let field binding body)
        body
        fields_in_wrapper_with_bindings
    in
    let fields_in_wrapper =
      List.map (fun (field_in_wrapper, _) -> field_in_wrapper)
        fields_in_wrapper_with_bindings
    in
    let make_field_projection ~index : Projection.t * Variable.t =
      Prim (Pfield index, [being_unboxed]), fields.(index)
    in
    let field_projections =
      Array.to_list (Array.init (fun index ->
          make_field_projection ~index)
        max_size)
    in
    let how_to_unbox : How_to_unbox.t =
      { being_unboxed_to_wrapper_params_being_unboxed;
        add_bindings_in_wrapper;
        new_arguments_for_call_in_wrapper = fields_in_wrapper;
        new_params = Array.to_list fields;
        new_projections = field_projections;
        wrap_body = (fun expr -> expr);
      }
    in
    Some how_to_unbox
  in
  How_to_unbox.merge_option for_discriminant for_fields

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
