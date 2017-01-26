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
module R = Inline_and_simplify_aux.Result
module U = R.Continuation_uses

let wrapper_returning_boxed_result ~params ~new_fun_var
      ~(return_arity : Flambda.unboxed_return_arity) =
  match return_arity with
  | Block_like { tag; size; } ->
    let stub_return_cont = Continuation.create () in
    let stub_params = List.map (fun param -> Variable.rename param) params in
    let new_closure_id = ... in
    let return_cont = Continuation.create () in
    let unboxed_results =
      Array.to_list (Array.init size (fun index ->
        Variable.create (Printf.sprintf "unboxed_result%d" index)))
    in
    let dbg = Debuginfo.none in
    let box_results =
      let boxed_result = Variable.create "boxed_result" in
      Flambda.create_let boxed_result
        (Prim (Pmakeblock (tag, Immutable, None), unboxed_results,
          Debuginfo.none))
        (Apply {
          kind = Function;
          func = new_fun_var;
          continuation = stub_return_cont;
          args = [boxed_result];
          call_kind = Direct { closure_id = ...; return_arity = Singleton; };
          dbg;
          inline = Lambda.Default_inline;
          specialise = Lambda.Default_specialise;
        })
    in
    let body : Flambda.expr =
      Let_cont {
        body = Apply {
          kind = Function;
          func = ...;
          continuation = return_cont;
          args = stub_params;
          call_kind = Direct { closure_id = new_closure_id; return_arity; };
          dbg;
          inline = Lambda.Default_inline;
          specialise = Lambda.Default_specialise;
        };
        handler = Nonrecursive {
          name = return_cont;
          handler = {
            params = unboxed_results;
            stub = false;
            is_exn_handler = false;
            handler = box_results;
            specialised_args = Variable.Map.empty;
          };
        }
      }
    in
    let function_decl =
      Flambda.create_function_declaration ~params:stub_params
        ~continuation_param:stub_return_cont
        ~return_arity:Singleton
        ~body
        ~stub:true
        ~dbg
        ~inline:Lambda.Default_inline
        ~specialise:Lambda.Default_specialise
        ~is_a_functor:false
    in
    Some function_decl
  | Variant_like { has_constant_ctors = _; tags_and_sizes = _; } ->
    Misc.fatal_error "Not yet implemented"

type return_approx =
  | Top
  | Bottom
  | Int
  | Block_like of { tag : Tag.t; size : int; }
  | Variant_like of {
      has_constant_ctors : bool;
      tags_and_sizes : (Tag.t * int) list;
    }

let merge_in_block_return_approx (approx : return_approx) ~tag ~size
      return_approx =
  match approx with
  | Top -> Block_like { tag; size; }
  | Bottom -> Bottom
  | Int ->
    Variant_like {
      has_constant_ctors = true;
      tags_and_sizes = [
        tag, size;
      ];
    }
  | Block_like { tag = existing_tag; size = existing_size; } ->
    if Tag.equal tag existing_tag && size = existing_size then
      approx
    else
      Variant_like {
        has_constant_ctors = false;
        tags_and_sizes = [
          existing_tag, existing_size;
          tag, size;
        ];
      }
  | Variant_like { has_constant_ctors; tags_and_sizes; } ->
    Variant_like {
      has_constant_ctors;
      tags_and_sizes = (tag, size) :: tags_and_sizes;
    }

let merge_in_int_return_approx (approx : return_approx) _i =
  | Top -> Int
  | Bottom -> Bottom
  | Int -> Int
  | Some (Block_like { tag = existing_tag; size = existing_size; }) ->
    Some (Variant_like {
      has_constant_ctors = true;
      tags_and_sizes = [
        existing_tag, existing_size;
      ];
    })
  | Some (Variant_like { has_constant_ctors = _; tags_and_sizes; }) ->
    Some (Variant_like {
      has_constant_ctors = true;
      tags_and_sizes = (tag, size) :: tags_and_sizes;
    })

let how_to_unbox r ~backend ~function_decl =
  let definitions_with_uses = R.continuation_definitions_with_uses r in
  match function_decl.return_arity function_decl with
  | Unboxed _ -> None
  | Singleton ->
    let return_cont = function_decl.continuation_param in
    match Continuation.Map.find return_cont definitions_with_uses with
    | exception Not_found -> None
    | (uses, _approx, _env, _recursive) ->
      if U.has_non_inlinable_uses uses then None
      else
        let uses = U.inlinable_application_points uses in
        let approx : return_approx option =
          List.fold_left (fun approx (use : Inline_and_simplify_aux.Use.t) ->
              match use.args with
              | [] | _::_::_ ->
                Misc.fatal_errorf "Continuation %a applied with the wrong \
                    number (%d) of arguments"
                  Continuation.print return_cont
                  (List.length use.args)
              | [arg, arg_approx] ->
                match A.check_approx_for_block with
                | Ok (tag, fields_approxs) ->
                  let size = Array.length fields_approxs in
                  merge_in_block_return_approx approx ~tag ~size
                | Wrong ->
                  match A.check_approx_for_int arg_approx with
                  | Some i when i >= 0 -> merge_in_int_return_approx approx i
                  | Some _ | None -> Bottom)
            None
            uses
        in
        match approx with
        | Bottom | Top -> None
        | Block_like { tag; size; } ->
          let arity : Flambda.return_arity =
            Unboxed (Block_like { tag; size; })
          in
          Some arity
        | Variant_like { has_constant_ctors; tags_and_sizes; } ->
          let arity : Flambda.return_arity =
            Unboxed (Variant_like { has_constant_ctors; tags_and_sizes; })
          in
          Some arity

let for_function_decl r ~backend ~fun_var ~function_decl =
  match how_to_unbox r ~backend ~function_decl with
  | None -> None
  | Some return_arity ->
    let new_fun_var = Variable.rename fun_var in
    let wrapper_decl =
      wrapper_returning_boxed_result ~params ~new_fun_var ~return_arity
    in

      let function_decls =
        Flambda.update_function_declarations set_of_closures.function_decls
          ~funs
      in

(* k must not escape *)
