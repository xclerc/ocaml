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

let zero_uses = Numbers.Int.Map.empty, false

let combine_uses (uses1, contains_returns1) (uses2, contains_returns2) =
  let uses =
    Numbers.Int.Map.union
      (fun _cont count1 count2 -> Some (N.(+) count1 count2))
      uses1 uses2
  in
  let contains_returns = contains_returns1 || contains_returns2 in
  uses, contains_returns

(* CR mshinwell: Remove mutable state once we've settled on what we need
   from this pass. *)

let used_within_catch_bodies = ref Numbers.Int.Map.empty

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
  | Uprim (Preturn, [arg], _) ->
    let uses, _contains_return = count_uses arg in
    let contains_return =
      match arg with
      | Ustaticfail _ -> false
      | _ -> true
    in
    uses, contains_return
  | Uprim (Preturn, _, _) ->
    Misc.fatal_errorf "Preturn takes exactly one argument"
  | Uprim (_, args, _) -> count_uses_list args
  | Uswitch (scrutinee, switch) ->
    count_uses scrutinee + count_uses_array switch.us_actions_consts
      + count_uses_array switch.us_actions_blocks
  | Ustringswitch (scrutinee, cases, default) ->
    count_uses scrutinee + count_uses_list (List.map snd cases)
      + count_uses_option default
  | Ustaticfail (cont, args) ->
    (Numbers.Int.Map.add cont N.One Numbers.Int.Map.empty, false)
      + count_uses_list args
  | Ucatch (cont, _, _, body, handler) ->
    let body_uses = count_uses body in
    if Numbers.Int.Map.mem cont !used_within_catch_bodies then begin
      Misc.fatal_errorf "Duplicate definition of Ucatch %d" cont
    end;
    used_within_catch_bodies :=
      Numbers.Int.Map.add cont body_uses !used_within_catch_bodies;
    body_uses + count_uses handler
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
  | Upushtrap cont | Upoptrap cont ->
    (Numbers.Int.Map.add cont N.One Numbers.Int.Map.empty, false)

and count_uses_list (ulams : Clambda.ulambda list) =
  let (+) = combine_uses in
  match ulams with
  | [] -> zero_uses
  | ulam::ulams -> count_uses ulam + count_uses_list ulams

and count_uses_array ulams = count_uses_list (Array.to_list ulams)

and count_uses_option = function
  | None -> zero_uses
  | Some ulam -> count_uses ulam

module Env : sig
  type t

  type action_at_apply_cont =
    | Unchanged
    | Return
    | Let_bind_args_and_substitute of Ident.t list * Clambda.ulambda

  val create : unit -> t

  val linearly_used_continuation
     : t
    -> cont:int
    -> params:Ident.t list
    -> handler:Clambda.ulambda
    -> t

  val continuation_will_turn_into_sequence : t -> cont:int -> t
  val continuation_will_turn_into_let : t -> cont:int -> t

  val action_at_apply_cont : t -> cont:int -> action_at_apply_cont
end = struct
  type action_at_apply_cont =
    | Unchanged
    | Return
    | Let_bind_args_and_substitute of Ident.t list * Clambda.ulambda

  type t = {
    actions : action_at_apply_cont Numbers.Int.Map.t;
  }

  let create () =
    { actions = Numbers.Int.Map.empty;
    }

  let linearly_used_continuation t ~cont ~params ~handler =
    if Numbers.Int.Map.mem cont t.actions then begin
      Misc.fatal_errorf "Continuation %d already in Un_cps environment"
        cont
    end else begin
      let action = Let_bind_args_and_substitute (params, handler) in
      { actions = Numbers.Int.Map.add cont action t.actions;
      }
    end

  let continuation_will_turn_into_sequence t ~cont =
    if Numbers.Int.Map.mem cont t.actions then begin
      Misc.fatal_errorf "Continuation %d already in Un_cps environment"
        cont
    end else begin
      (* CR mshinwell: add Return_unit *)
      let action = Let_bind_args_and_substitute ([], Uconst (Uconst_int 0)) in
      { actions = Numbers.Int.Map.add cont action t.actions;
      }
    end

  let continuation_will_turn_into_let t ~cont =
    if Numbers.Int.Map.mem cont t.actions then begin
      Misc.fatal_errorf "Continuation %d already in Un_cps environment"
        cont
    end else begin
      { actions = Numbers.Int.Map.add cont Return t.actions;
      }
    end

  let action_at_apply_cont t ~cont =
    match Numbers.Int.Map.find cont t.actions with
    | exception Not_found -> Unchanged
    | action -> action
end

type can_turn_into_let_or_sequence =
  | Nothing
  | Sequence
  | Let of Ident.t

let inline ulam ~(uses : N.t Numbers.Int.Map.t) ~used_within_catch_bodies =
  let module E = Env in
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
      begin match E.action_at_apply_cont env ~cont with
      | Unchanged -> Ustaticfail (cont, inline_list env args)
      | Return ->
        begin match args with
        | [arg] -> arg
        | _ ->
          Misc.fatal_errorf "Ustaticfail %d has the wrong number of \
              arguments"
            cont
        end
      | Let_bind_args_and_substitute (params, handler) ->
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
    | Ucatch (cont, kind, params, body, handler) ->
      let module Action = struct
        type t =
          | Unused
          | Linear_inlining
          | Normal
      end in
      let action : Action.t =
        match Numbers.Int.Map.find cont uses with
        | exception Not_found ->
          begin match kind with
          | Normal _ -> Unused
          | Exn_handler -> Normal
          end
        | One ->
          assert (kind <> Clambda.Exn_handler);
          Linear_inlining
        | Many ->
          assert (kind <> Clambda.Exn_handler);
          Normal
        | Zero -> assert false
      in
      begin match action with
      | Unused -> inline env body
      | Linear_inlining ->
        let env = E.linearly_used_continuation env ~cont ~params ~handler in
        inline env body
      | Normal ->
        begin match Numbers.Int.Map.find cont used_within_catch_bodies with
        | exception Not_found ->
          Misc.fatal_errorf "No record of used continuations within \
              Ucatch body %d"
            cont
        | (used, contains_returns) ->
          (* If, after inlining linearly-used continuations in the body, the
             only occurrences of continuation variables in such body all refer
             to the "nearest" continuation variable binding (i.e. [cont]),
             then turn the [Ucatch] into either a let-binding or a sequence.
          *)
          let used =
            Numbers.Int.Map.filter (fun _cont (uses : N.t) ->
                match uses with
                | Zero | One -> false
                | Many -> true)
              used
          in
          let can_turn_into_let_or_sequence =
            match Numbers.Int.Map.bindings used with
            | [cont', _] when cont = cont' ->
              if contains_returns then begin
                Nothing
              end else begin
                match params with
                | [param] -> Let param
                | [] -> Sequence
                | _ -> Nothing
              end
            | _ -> Nothing
          in
          match can_turn_into_let_or_sequence with
          | Nothing ->
            Ucatch (cont, kind, params, inline env body, inline env handler)
          | Sequence ->
            assert (kind <> Clambda.Exn_handler);
            let env = E.continuation_will_turn_into_sequence env ~cont in
            Usequence (inline env body, inline env handler)
          | Let param ->
            assert (kind <> Clambda.Exn_handler);
            let env = E.continuation_will_turn_into_let env ~cont in
            Ulet (Immutable, Pgenval, param, inline env body,
              inline env handler)
        end
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
    | Upushtrap _ | Upoptrap _ -> ulam
  and inline_option env ulam =
    match ulam with
    | None -> None
    | Some ulam -> Some (inline env ulam)
  and inline_list env ulams =
    List.map (fun ulam -> inline env ulam) ulams
  and inline_array env ulams =
    Array.map (fun ulam -> inline env ulam) ulams
  in
  inline (E.create ()) ulam

let run ulam =
  used_within_catch_bodies := Numbers.Int.Map.empty;
  let uses, _contains_returns =
    count_uses ulam
  in
  inline ulam ~uses ~used_within_catch_bodies:!used_within_catch_bodies
