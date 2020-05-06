(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

open! Flambda.Import

module DE = Simplify_env_and_result.Downwards_env

module Function_declaration_decision = struct
  type t =
    | Never_inline_attribute
    | Function_body_too_large
    | Stub
    | Inline

  let can_inline t =
    match t with
    | Never_inline_attribute
    | Function_body_too_large -> false
    | Stub
    | Inline -> true
end

let make_decision_for_function_declaration denv function_decl
      : Function_declaration_decision.t =
  (* At present, we follow Closure, taking inlining decisions without
     first examining call sites. *)
  match Function_declaration.inline function_decl with
  | Never_inline -> Never_inline_attribute
  | Always_inline | Default_inline | Unroll _ ->
    if Function_declaration.stub function_decl then Stub
    else
      let code_id = Function_declaration.code_id function_decl in
      let params_and_body = DE.find_code denv code_id in
      Function_params_and_body.pattern_match params_and_body
        ~f:(fun ~return_continuation:_ _exn_continuation _params ~body
                ~my_closure:_ : Function_declaration_decision.t ->
          let inlining_threshold : Inlining_cost.Threshold.t =
            let round = DE.round denv in
            let unscaled =
              Clflags.Float_arg_helper.get ~key:round !Clflags.inline_threshold
            in
            (* CR-soon pchambart: Add a warning if this is too big
               mshinwell: later *)
            Can_inline_if_no_larger_than
              (int_of_float
                (unscaled *.
                  (float_of_int Inlining_cost.scale_inline_threshold_by)))
          in
          if Inlining_cost.can_inline denv body inlining_threshold ~bonus:0
          then Inline
          else Function_body_too_large)

module Call_site_decision = struct
  type attribute_causing_inlining =
    | Unroll
    | Always

  let print_attribute_causing_inlining ppf attr =
    match attr with
    | Unroll -> Format.fprintf ppf "Unroll"
    | Always -> Format.fprintf ppf "Always"

  type t =
    | Environment_says_never_inline
    | Unrolling_depth_exceeded
    | Max_inlining_depth_exceeded
    | Recursion_depth_exceeded
    | Never_inline_attribute
    | Inline of {
        attribute : attribute_causing_inlining option;
        unroll_to : int option;
      }

  let print ppf t =
    match t with
    | Environment_says_never_inline ->
      Format.fprintf ppf "Environment_says_never_inline"
    | Unrolling_depth_exceeded ->
      Format.fprintf ppf "Unrolling_depth_exceeded"
    | Max_inlining_depth_exceeded ->
      Format.fprintf ppf "Max_inlining_depth_exceeded"
    | Recursion_depth_exceeded ->
      Format.fprintf ppf "Recursion_depth_exceeded"
    | Never_inline_attribute ->
      Format.fprintf ppf "Never_inline_attribute"
    | Inline { attribute; unroll_to; } ->
      Format.fprintf ppf "@[<hov 1>(\
          @[<hov 1>(attribute@ %a)@]@ \
          @[<hov 1>(unroll_to@ %a)@]\
          )@]"
        (Misc.Stdlib.Option.print print_attribute_causing_inlining) attribute
        (Misc.Stdlib.Option.print Numbers.Int.print) unroll_to

  type can_inline =
    | Do_not_inline
    | Inline of { unroll_to : int option; }

  let can_inline (t : t) : can_inline =
    match t with
    | Environment_says_never_inline
    | Unrolling_depth_exceeded
    | Max_inlining_depth_exceeded
    | Recursion_depth_exceeded
    | Never_inline_attribute -> Do_not_inline
    | Inline { attribute = _; unroll_to; } -> Inline { unroll_to; }
end

(* CR mshinwell: These parameters need to be configurable *)
let max_inlining_depth = 1
let max_rec_depth = 1

let rec int_of_depth = function
  | Reg_width_things.Depth_expr.Zero -> 0
  | Reg_width_things.Depth_expr.Succ x -> succ (int_of_depth x)
  | Reg_width_things.Depth_expr.Variable _ -> 0 (*XXX*)

let make_decision_for_call_site denv ~function_decl_coercion
      ~apply_inlining_depth (inline : Inline_attribute.t)
      : Call_site_decision.t =
  if (not (DE.can_inline denv)) then
    Environment_says_never_inline
  else
    let { Reg_width_things.Coercion.change_depth; change_unroll_to; } =
      Reg_width_things.Coercion.descr function_decl_coercion in
    match change_unroll_to with
    | Some { Reg_width_things.Coercion.from = _; to_ = Some unroll_to; } ->
      begin match change_depth with
      | Some { Reg_width_things.Coercion.from = _; to_ = depth; }
        when int_of_depth depth < int_of_depth unroll_to ->
        Inline { attribute = None; unroll_to = None; }
      | Some _ | None ->
        Unrolling_depth_exceeded
      end
    | Some _ | None ->
      if apply_inlining_depth >= max_inlining_depth then
        Max_inlining_depth_exceeded
      else
        match inline with
        | Never_inline -> Never_inline_attribute
        | Default_inline ->
          begin match change_depth with
          | Some { Reg_width_things.Coercion.from = _; to_ = depth; }
            when int_of_depth depth < max_rec_depth ->
            Inline { attribute = None; unroll_to = None; }
          | Some _ | None ->
            Recursion_depth_exceeded
          end
        | Unroll unroll_to ->
          let unroll_to =
            match change_depth with
            | Some { Reg_width_things.Coercion.from = _; to_ = depth; } ->
              (int_of_depth depth) + unroll_to
            | None -> unroll_to in
          Inline { attribute = Some Unroll; unroll_to = Some unroll_to; }
        | Always_inline ->
          Inline { attribute = Some Always; unroll_to = None; }
