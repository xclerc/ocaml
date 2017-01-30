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
module CAV = Invariant_params.Continuations.Continuation_and_variable
module R = Inline_and_simplify_aux.Result

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

(* CR mshinwell: Once working, consider sharing code with
   [Unbox_specialised_args]. *)

module Unboxing : sig
  type t

  include Identifiable with type t := t

  val create : A.t -> t option

  type how_to_unbox = {
    wrapper_param_being_unboxed : Variable.t;
    bindings_in_wrapper : Flambda.expr Variable.Map.t;
    new_arguments_for_call_in_wrapper : Variable.t list;
    new_params : Variable.t list;
    new_projections : Projection.t list;
    wrap_body : Flambda.expr -> Flambda.expr;
  }

  val how_to_unbox : t -> being_unboxed:Variable.t -> how_to_unbox
end = struct
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
          let max_tag_var = Variable.create "max_tag" in
          let is_int_cont = Continuation.create () in
          let is_block_cont = Continuation.create () in
          Let_cont {
            body = Let_cont {
              body =
                Flambda.create_let create_discriminant_in_wrapper
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
end

let for_continuations r ~body ~handlers ~original ~backend
      ~(recursive : Asttypes.rec_flag) =
  let definitions_with_uses = R.continuation_definitions_with_uses r in
  let unboxings_by_cont =
    Continuation.Map.filter_map handlers
      ~f:(fun cont (handler : Flambda.continuation_handler) ->
        if handler.stub then
          None
        else
          match handler.params with
          | [] -> None
          | params ->
            match Continuation.Map.find cont definitions_with_uses with
            | exception Not_found -> None
            | (uses, _approx, _env, _recursive) ->
              let num_params = List.length params in
              let args_approxs =
                Inline_and_simplify_aux.Continuation_uses.meet_of_args_approxs
              in
              let params_to_approxs =
                Variable.Map.of_list (List.combine params args_approxs)
              in
              let unboxings =
                Variable.Map.filter_map params_to_approxs
                  ~f:(fun _param approx -> Unboxing.create approx)
              in
              if Variable.Map.is_empty unboxings then None
              else Some unboxings)
  in
  if Continuation.Map.is_empty unboxings_by_cont then begin
    original
  end else begin
    Format.eprintf "Unboxings:\n@;%a\n"
      (Continuation.Map.print Unboxing.Set.print) unboxings_by_cont;
    let invariant_params_flow =
      Invariant_params.Continuations.invariant_param_sources handlers ~backend
    in
(*
Format.eprintf "Invariant params:\n@;%a\n"
  (Variable.Map.print
    Invariant_params.Continuations.Continuation_and_variable.Set.print)
    invariant_params_flow;
*)


    let projections_by_cont' =
      Continuation.Map.fold (fun cont projections projections_by_cont' ->
          Projection.Set.fold (fun projection projections_by_cont' ->
              let projecting_from = Projection.projecting_from projection in
              match Variable.Map.find projecting_from invariant_params_flow with
              | exception Not_found -> projections_by_cont'
              | flow ->
                CAV.Set.fold (fun (target_cont, target_arg)
                          projections_by_cont' ->
                    if Continuation.equal cont target_cont then
                      projections_by_cont'
                    else
                      let projection =
                        Projection.map_projecting_from projection
                          ~f:(fun var ->
                            assert (Variable.equal var projecting_from);
                            target_arg)
                      in
                      let new_args =
                        match
                          Continuation.Map.find target_cont projections_by_cont'
                        with
                        | exception Not_found -> Projection.Set.empty
                        | new_args -> new_args
                      in
                      let new_args =
                        Projection.Set.add projection new_args
                      in
                      Continuation.Map.add target_cont new_args
                        projections_by_cont')
                  flow
                  projections_by_cont')
            projections
            projections_by_cont')
        projections_by_cont
        Continuation.Map.empty
    in
    let projections_by_cont =
      Continuation.Map.union (fun _cont projs1 projs2 ->
          Some (Projection.Set.union projs1 projs2))
        projections_by_cont projections_by_cont'
    in


    let with_wrappers =
      Continuation.Map.fold (fun cont projections new_handlers ->
          let handler : Flambda.continuation_handler =
            match Continuation.Map.find cont handlers with
            | exception Not_found -> assert false
            | handler -> handler
          in
          let new_cont = Continuation.create () in
          let unboxings, specialised_args =
            Projection.Set.fold (fun projection
                      (unboxings, specialised_args) ->
                let param = Projection.projecting_from projection in
                let spec_to : Flambda.specialised_to =
                  { var = None;
                    projection = Some projection;
                  }
                in
                let new_param = Variable.rename ~append:"_unboxed" param in
                let unboxings = (new_param, projection)::unboxings in
                let specialised_args =
                  Variable.Map.add new_param spec_to specialised_args
                in
                unboxings, specialised_args)
              projections
              ([], handler.specialised_args)
          in
          let unboxing_params =
            List.map (fun (param, _projection) -> param) unboxings
          in
          let new_params = handler.params @ unboxing_params in
          let params_freshening =
            List.map (fun param -> param, Variable.rename param) new_params
          in
          let params_freshening = Variable.Map.of_list params_freshening in
          let freshen_param param =
            match Variable.Map.find param params_freshening with
            | exception Not_found -> assert false
            | param -> param
          in
          let wrapper_params =
            List.map (fun param -> freshen_param param) handler.params
          in
          let original_params = Variable.Set.of_list handler.params in
          let wrapper_specialised_args =
            Variable.Map.fold (fun param (spec_to : Flambda.specialised_to)
                    wrapper_specialised_args ->
                if not (Variable.Set.mem param original_params) then
                  wrapper_specialised_args
                else
                  let param = freshen_param param in
                  let projection =
                    match spec_to.projection with
                    | None -> None
                    | Some projection ->
                      Some (Projection.map_projecting_from projection
                        ~f:(fun param -> freshen_param param))
                  in
                  let spec_to : Flambda.specialised_to =
                    { var = Misc.Stdlib.Option.map freshen_param spec_to.var;
                      projection;
                    }
                  in
                  Variable.Map.add param spec_to wrapper_specialised_args)
              specialised_args
              Variable.Map.empty
          in
          let wrapper_unboxings =
            List.map (fun (unboxing, projection) ->
                freshen_param unboxing, projection)
              unboxings
          in
          let wrapper_body =
            let initial_body : Flambda.t =
              let wrapper_unboxings =
                List.map (fun (unboxing, _projection) -> unboxing)
                  wrapper_unboxings
              in
              Apply_cont (new_cont, None, wrapper_params @ wrapper_unboxings)
            in
            List.fold_left (fun wrapper_body (unboxing, projection) ->
                let projection =
                  Projection.map_projecting_from projection
                    ~f:(fun param -> freshen_param param)
                in
                let named = Flambda_utils.projection_to_named projection in
                Flambda.create_let unboxing named wrapper_body)
              initial_body
              wrapper_unboxings
          in
          let wrapper_handler : Flambda.continuation_handler =
            { params = wrapper_params;
              stub = true;
              is_exn_handler = false;
              handler = wrapper_body;
              specialised_args = wrapper_specialised_args;
            }
          in
          assert (not handler.is_exn_handler);
          let new_handler : Flambda.continuation_handler =
            { params = new_params;
              stub = handler.stub;
              is_exn_handler = false;
              handler = handler.handler;
              specialised_args;
            }
          in
          let with_wrapper : Flambda_utils.with_wrapper =
            With_wrapper {
              new_cont;
              new_handler;
              wrapper_handler;
            }
          in
          Continuation.Map.add cont with_wrapper new_handlers)
        projections_by_cont
        Continuation.Map.empty
    in
    let output =
      Flambda_utils.build_let_cont_with_wrappers ~body ~recursive
        ~with_wrappers
    in
    Format.eprintf "After unboxing:\n@;%a\n%!" Flambda.print output;
    output
  end

let run r expr ~backend =
Format.eprintf "Ready to unbox:\n@;%a\n%!" Flambda.print expr;
  Flambda_iterators.map_expr (fun (expr : Flambda.expr) ->
      match expr with
      | Let_cont { body = _; handlers = Nonrecursive { name = _; handler = {
          is_exn_handler = true; _ }; }; } -> expr
      | Let_cont { body; handlers = Nonrecursive { name; handler; } } ->
        let handlers =
          Continuation.Map.add name handler Continuation.Map.empty
        in
        for_continuations r ~body ~handlers ~original:expr ~backend
          ~recursive:Asttypes.Nonrecursive
      | Let_cont { body; handlers = Recursive handlers; } ->
        for_continuations r ~body ~handlers ~original:expr ~backend
          ~recursive:Asttypes.Recursive
      | Let_cont { handlers = Alias _; _ }
      | Let _ | Let_mutable _ | Apply _ | Apply_cont _ | Switch _
      | Proved_unreachable -> expr)
    expr
