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

module Tag_and_int = struct
  include Identifiable.Make (struct
    type t = Tag.t * int

    let compare ((tag1, i1) : t) (tag2, i2) =
      let c = Tag.compare tag1 tag2 in
      if c <> 0 then c
      else Pervasives.compare i1 i2

    let hash (tag, i) = Hashtbl.hash (Tag.hash tag, i)

    let output _ _ = Misc.fatal_error "Not implemented"
    let print _ _ = Misc.fatal_error "Not implemented"
  end)
end

include Identifiable.Make (struct
  type t = {
    has_constant_ctors : bool;
    tags_and_sizes : Tag_and_int.Set.t;
  }

  let compare t1 t2 =
    let c = Pervasives.compare t1.has_constant_ctors t2.has_constant_ctors in
    if c <> 0 then c
    else Tag_and_int.Set.compare t1.tags_and_sizes t2.tags_and_sizes

  let hash t =
    Hashtbl.hash (t.has_constant_ctors, Tag_and_int.Set.hash t.tags_and_sizes)

  let print ppf t =
    Format.fprintf ppf "@[((has_constant_ctors %b)@ (tags_and_sizes %a)}@]"
      t.has_constant_ctors
      Tag_and_int.Set.print t.tags_and_sizes

  let output _ _ = Misc.fatal_error "Not implemented"
end)

let create (approx : A.t) =
  match A.descr approx with
  | Float _ | Boxed_int _ | Set_of_closures _ | Closure _ | String _
  | Float_array _ | Unknown _ | Bottom | Extern _ | Symbol _
  | Unresolved _ -> None
  | Union approx_set ->
    A.Unionable.Set.fold (fun (approx : A.Unionable.t) t : t option ->
        match t with
        | None ->
          begin match approx with
          | Block (tag, fields) ->
            let size = Array.length fields in
            Some {
              has_constant_ctors = false;
              tags_and_sizes = Tag_and_int.Set.singleton (tag, size);
            }
          | Int _ | Char _ | Constptr _ ->
            Some {
              has_constant_ctors = true;
              tags_and_sizes = Tag_and_int.Set.empty;
            }
          end
        | Some t ->
          begin match approx with
          | Block (tag, fields) ->
            let size = Array.length fields in
            let tags_and_sizes =
              Tag_and_int.Set.add (tag, size) t.tags_and_sizes
            in
            Some { t with tags_and_sizes; }
          | Int _ | Char _ | Constptr _ ->
            Some { t with has_constant_ctors = true; }
          end)
      approx_set
      None

type how_to_unbox = {
  add_bindings_in_wrapper : Flambda.expr -> Flambda.expr;
  new_arguments_for_call_in_wrapper : Variable.t list;
  new_params : Variable.t list;
  new_projections : Projection.t list;
  wrap_body : Flambda.expr -> Flambda.expr;
}

let merge_how_to_unbox (how1 : how_to_unbox option)
      (how2 : how_to_unbox option) : how_to_unbox option =
  match how1, how2 with
  | None, None -> None
  | Some how1, None -> Some how1
  | None, Some how2 -> Some how2
  | Some how1, Some how2 ->
    assert (Variable.equal how1.wrapper_param_being_unboxed
      how2.wrapper_param_being_unboxed);
    { wrapper_param_being_unboxed = how1.wrapper_param_being_unboxed;
      add_bindings_in_wrapper = (fun expr ->
        how2.add_bindings_in_wrapper (
          how1.add_bindings_in_wrapper expr));
      new_arguments_for_call_in_wrapper =
        how1.new_arguments_for_call_in_wrapper
          @ how2.new_arguments_for_call_in_wrapper;
      new_params = how1.new_params @ how2.new_params;
      new_projections = how1.new_projections @ how2.new_projections;
      wrap_body = (fun expr -> how2.wrap_body (how1.wrap_body expr));
    }

let how_to_unbox t ~being_unboxed =
  let dbg = Debuginfo.none in
  let wrapper_param_being_unboxed = Variable.rename being_unboxed in
  let for_discriminant : how_to_unbox option =
    (* See the [Switch] case in [Inline_and_simplify] for details of the
       encoding of the variant discriminant. *)
    if not t.has_constant_ctors then None
    else
      let max_tag = Obj.last_non_constant_constructor_tag in
      let discriminant = Variable.rename ~append:"_discr" being_unboxed in
      let discriminant_in_wrapper = Variable.rename discriminant in
      let is_constant_ctor =
        Variable.rename ~append:"_is_const" begin_unboxed
      in
      let isint_projection : Projection.t * Variable.t =
        Prim (Pisint, [being_unboxed]), is_constant_ctor
      in
      let switch_projection : Projection.t * Variable.t =
        Switch being_unboxed, discriminant
      in
      let add_bindings_in_wrapper expr =
        let max_tag_plus_one_var = Variable.create "max_tag" in
        let is_int_cont = Continuation.create () in
        let is_block_cont = Continuation.create () in
        let join_cont = Continuation.create () in
        let max_tag_var = Variable.create "max_tag" in
        let shifted_tag_var = Variable.create "shifted_tag" in
        let tag_var = Variable.create "tag" in
        let is_int_var = Variable.create "is_int" in
        let switch : Flambda.switch =
          { numconsts = Numbers.Int.Set.singleton 0;
            consts = [0, is_block_cont];
            numblocks = Numbers.Int.Set.empty;
            blocks = [];
            failaction = Some is_int_cont;
          }
        in
        Flambda.create_let max_tag_plus_one_var (Const (Int (max_tag + 1)))
          (Let_cont {
            body = Let_cont {
              body = Let_cont {
                body =
                  Flambda.create_let is_int_var
                    (Prim (Pisint, [wrapper_param_being_unboxed], dbg))
                    (Switch switch);
                handlers = Nonrecursive {
                  name = is_int_cont;
                  handler = {
                    params = [];
                    body =
                      Flambda.create_let shifted_tag_var
                        (Prim (Paddint,
                          [wrapper_param_being_unboxed; max_tag_plus_one_var],
                          dbg))
                        (Apply_cont (join_cont, None, [shifted_tag_var]));
                    stub = false;
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
                  body =
                    Flambda.create_let tag_var
                      (Prim (Pgettag, [wrapper_param_being_unboxed], dbg))
                      (Apply_cont (join_cont, None, [tag_var]));
                  stub = false;
                  specialised_args = Variable.Map.empty;
                };
              };
            };
            handlers = Nonrecursive {
              name = join_cont;
              handler = {
                params = [discriminant_in_wrapper];
                body = expr;
                stub = false;
                specialised_args = Variable.Map.empty;
              };
            }
          })
      in
      let wrap_body expr =
        let max_tag_var = Variable.create "max_tag" in
        Flambda.create_let max_tag (Const (Int max_tag))
          (Flambda.create_let is_constant_ctor
            (Prim (Pintcomp Cgt, [discriminant; max_tag], dbg))
            expr)
      in
      let how_to_unbox : how_to_unbox =
        { wrapper_param_being_unboxed;
          add_bindings_in_wrapper;
          new_arguments_for_call_in_wrapper = [discriminant_in_wrapper];
          new_params = [discriminant];
          new_projections = [isint_projection; switch_projection];
          wrap_body;
        }
      in
      Some how_to_unbox
  in
  let for_fields : how_to_unbox option =
    let max_size =
      Tag_and_int.Set.fold (fun (_tag, size) max_size -> max size max_size)
        t.tags_and_sizes 0
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
    let how_to_unbox : how_to_unbox =
      { wrapper_param_being_unboxed;
        add_bindings_in_wrapper;
        new_arguments_for_call_in_wrapper = fields_in_wrapper;
        new_params = Array.to_list fields;
        new_projections = field_projections;
        wrap_body = (fun expr -> expr);
      }
    in
    Some how_to_unbox
  in
  merge_how_to_unbox for_discriminant for_fields
