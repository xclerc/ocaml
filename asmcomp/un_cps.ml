(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2016 OCamlPro SAS                                          *)
(*   Copyright 2016 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module N = Num_continuation_uses

let zero_uses = Numbers.Int.Map.empty

let combine_uses uses1 uses2 =
  Numbers.Int.Map.union
    (fun _cont count1 count2 -> Some (N.(+) count1 count2))
    uses1 uses2

let rec count_uses (ulam : Clambda.ulambda) =
  let (+) = combine_uses in
  (* CR mshinwell: use explicit ignore functions *)
  (* CR mshinwell: short-circuit once we get to [Many] *)
  match ulam with
  | Uvar _ | Uconst _ | Uunreachable -> zero_uses
  | Udirect_apply (_, args, _) -> count_uses_list args
  | Ugeneric_apply (func, args, _) -> count_uses func + count_uses_list args
  | Uclosure (funcs, vars) ->
    count_uses_list
      (List.map (fun (func : Clambda.ufunction) -> func.body) funcs)
      + count_uses_list vars
  | Uoffset (closure, _) -> count_uses closure
  | Ulet (_, _, _, defining_expr, body) ->
    count_uses defining_expr + count_uses body
  | Uletrec (bindings, ulam) ->
    count_uses_list (List.map snd bindings) + count_uses ulam
  | Uprim (_, args, _) -> count_uses_list args
  | Uswitch (scrutinee, switch) ->
    count_uses scrutinee + count_uses_array switch.us_actions_consts
      + count_uses_array switch.us_actions_blocks
  | Ustringswitch (scrutinee, cases, default) ->
    count_uses scrutinee + count_uses_list (List.map snd cases)
      + count_uses_option default
  | Ustaticfail (cont, args) ->
    (Numbers.Int.Map.add cont N.One Numbers.Int.Map.empty)
      + count_uses_list args
  | Ucatch (_, _, body, handler)
  | Utrywith (body, _, handler) -> count_uses body + count_uses handler
  | Uifthenelse (cond, ifso, ifnot) ->
    count_uses cond + count_uses ifso + count_uses ifnot
  | Usequence (ulam1, ulam2) -> count_uses ulam1 + count_uses ulam2
  | Uwhile (cond, body) -> count_uses cond + count_uses body
  | Ufor (_, start, stop, _, body) ->
    count_uses start + count_uses stop + count_uses body
  | Uassign (_, ulam) -> count_uses ulam
  | Usend (_, meth, obj, args, _) ->
    count_uses meth + count_uses obj + count_uses_list args

and count_uses_list (ulams : Clambda.ulambda list) =
  let (+) = combine_uses in
  match ulams with
  | [] -> zero_uses
  | ulam::ulams -> count_uses ulam + count_uses_list ulams

and count_uses_array ulams = count_uses_list (Array.to_list ulams)

and count_uses_option = function
  | None -> zero_uses
  | Some ulam -> count_uses ulam

let inline ulam ~(uses : N.t Numbers.Int.Map.t) =
  let rec inline env (ulam : Clambda.ulambda) : Clambda.ulambda =
    match ulam with
    | Uvar _ | Uconst _ | Uunreachable -> ulam
    | Udirect_apply (func_label, args, dbg) ->
      Udirect_apply (func_label, inline_list env args, dbg)
    | Ugeneric_apply (func, args, dbg) ->
      Ugeneric_apply (inline env func, inline_list env args, dbg)
    | Uclosure (funcs, vars) ->
      let funcs =
        List.map (fun (func : Clambda.ufunction) ->
            { func with body = inline env func.body; })
          funcs
      in
      Uclosure (funcs, inline_list env vars)
    | Uoffset (closure, offset) -> Uoffset (inline env closure, offset)
    | Ulet (mut, kind, id, defining_expr, body) ->
      Ulet (mut, kind, id, inline env defining_expr, inline env body)
    | Uletrec (bindings, ulam) ->
      let bindings =
        List.map (fun (id, ulam) -> id, inline env ulam) bindings
      in
      Uletrec (bindings, inline env ulam)
    | Uprim (prim, args, dbg) ->
      Uprim (prim, inline_list env args, dbg)
    | Uswitch (scrutinee, switch) ->
      let switch =
        { switch with
          us_actions_consts = inline_array env switch.us_actions_consts;
          us_actions_blocks = inline_array env switch.us_actions_blocks;
        }
      in
      Uswitch (inline env scrutinee, switch)
    | Ustringswitch (scrutinee, cases, default) ->
      let cases =
        List.map (fun (str, case) -> str, inline env case) cases
      in
      Ustringswitch (inline env scrutinee, cases, inline_option env default)
    | Ustaticfail (cont, args) ->
      begin match Numbers.Int.Map.find cont env with
      | exception Not_found -> Ustaticfail (cont, inline_list env args)
      | (params, handler) ->
        if List.length params <> List.length args then begin
          Misc.fatal_errorf "Ustaticfail %d has the wrong number of \
              arguments"
            cont
        end else begin
          List.fold_right (fun (param, arg) ulam : Clambda.ulambda ->
              Ulet (Immutable, Pgenval, param, arg, ulam))
            (List.combine params (inline_list env args))
            (inline env handler)
        end
      end
    | Ucatch (cont, params, body, handler) ->
      begin match Numbers.Int.Map.find cont uses with
      | exception Not_found -> inline env body
      | One ->
        let env = Numbers.Int.Map.add cont (params, handler) env in
        inline env body
      | Many ->
        Ucatch (cont, params, inline env body, inline env handler)
      | Zero -> assert false
      end
    | Utrywith (body, id, handler) ->
      Utrywith (inline env body, id, inline env handler)
    | Uifthenelse (cond, ifso, ifnot) ->
      Uifthenelse (inline env cond, inline env ifso, inline env ifnot)
    | Usequence (ulam1, ulam2) -> Usequence (inline env ulam1, inline env ulam2)
    | Uwhile (cond, body) -> Uwhile (inline env cond, inline env body)
    | Ufor (id, start, stop, dir, body) ->
      Ufor (id, inline env start, inline env stop, dir, inline env body)
    | Uassign (id, ulam) -> Uassign (id, inline env ulam)
    | Usend (kind, meth, obj, args, dbg) ->
      Usend (kind, inline env meth, inline env obj, inline_list env args, dbg)
  and inline_option env ulam =
    match ulam with
    | None -> None
    | Some ulam -> Some (inline env ulam)
  and inline_list env ulams =
    List.map (fun ulam -> inline env ulam) ulams
  and inline_array env ulams =
    Array.map (fun ulam -> inline env ulam) ulams
  in
  inline Numbers.Int.Map.empty ulam

let run ulam =
  let uses = count_uses ulam in
  inline ulam ~uses
