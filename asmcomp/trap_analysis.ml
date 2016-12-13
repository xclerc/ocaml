
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

module Int = Numbers.Int

(* The following invariant is relied upon (and checked to a reasonable
   extent): all applications of a given continuation must be at the same
   trap depth.
*)

let rec trap_stacks (insn : Mach.instruction) ~stack ~stacks_at_exit
      : int list Int.Map.t =
  let insn = Mach.update_trap_stack insn ~trap_stack:stack in
  let add_stack ~cont ~stack ~stacks_at_exit =
    match Int.Map.find cont stacks_at_exit with
    | exception Not_found ->
      Int.Map.add cont stack stacks_at_exit
    | stack' ->
      let print_stack ppf stack =
        Format.fprintf ppf "%a"
          (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ")
            (fun ppf cont -> Format.fprintf ppf "%d" cont))
          stack
      in
      if stack <> stack' then begin
        Misc.fatal_errorf "Iexit points for continuation %d disagree on \
            the trap stack: existing = %a new = %a"
          cont
          print_stack stack'
          print_stack stack
      end;
      stacks_at_exit
  in
  match insn.Mach.desc with
  | Iend ->
    insn, stacks_at_exit
  | Ireturn ->
    begin match stack with
    | [] -> stacks_at_exit
    | _ -> Misc.fatal_error "Trap depth at Ireturn is non-zero"
    end;
    insn, stacks_at_exit
  | Iop op ->
    let stack, stacks_at_exit =
      match op with
      | Ipushtrap cont ->
        let stacks_at_exit = add_stack ~cont ~stack ~stacks_at_exit in
        cont :: stack, stacks_at_exit
      | Ipoptrap cont ->
        begin match stack with
        | [] ->
          Misc.fatal_errorf "Tried to poptrap %d but trap stack is empty" cont
        | cont' :: stack ->
          if cont = cont' then
            stack, stacks_at_exit
          else
            Misc.fatal_errorf "Tried to poptrap %d but trap stack has %d \
                at the top"
              cont cont'
        end
      | _ -> stack, stacks_at_exit
    in
    let next, stacks_at_exit =
      trap_stacks insn.Mach.next ~stack ~stacks_at_exit
    in
    { insn with next; }, stacks_at_exit
  | Iraise _ ->
    let next, stacks_at_exit =
      trap_stacks insn.Mach.next ~stack ~stacks_at_exit
    in
    { insn with next; }, stacks_at_exit
  | Iifthenelse (cond, ifso, ifnot) ->
    let ifso, stacks_at_exit = trap_stacks ifso ~stack in
    let ifnot, stacks_at_exit = trap_stacks ifnot ~stack in
    let next, stacks_at_exit = trap_stacks insn.Mach.next ~stack in
    { insn with
      desc = Iifthenelse (cond, ifso, ifnot);
      next;
    }, stacks_at_exit
  | Iswitch (cases, insns) ->
    let stacks_at_exit = ref stacks_at_exit in
    let new_insns = Array.copy insns in
    for case = 0 to Array.length cases - 1 do
      let new_insn, new_stacks_at_exit =
        trap_stacks insns.(case) ~stack ~stacks_at_exit:!stacks_at_exit
      in
      insns_output.(case) <- new_insn;
      stacks_at_exit := new_stacks_at_exit
    done;
    let next, stacks_at_exit =
      trap_stacks insn.Mach.next ~stack ~stacks_at_exit:!stacks_at_exit
    in
    { insn with
      desc = Iswitch (cases, new_insns);
      next;
    }, stacks_at_exit
  | Iloop body ->
    let body, stacks_at_exit = trap_stacks body ~stack ~stacks_at_exit in
    { insn with
      desc = Iloop body;
      next;
    }, stacks_at_exit
  | Icatch (rec_flag, is_exn_handler, handlers, body) ->
    let body, stacks_at_exit = trap_stacks body ~stack ~stacks_at_exit in



    let handlers = Int.Map.of_list handlers in
    let handlers_with_uses, handlers_without_uses =
      Int.Map.partition (fun cont _handler ->
          Int.Map.mem cont stacks_at_exit)
        handlers
    in
    let rec process_handlers ~stacks_at_exit ~handlers_with_uses
          ~handlers_without_uses =
      (* By the invariant above, there is no need to compute a fixpoint. *)
      if Int.Map.is_empty handlers_with_uses then begin
        stacks_at_exit
      end else
        let cont, handler = Int.Map.min_binding handlers_with_uses in
        let handlers_with_uses = Int.Map.remove cont handlers_with_uses in
        match Int.Map.find cont stacks_at_exit with
        | exception Not_found -> assert false
        | stack ->
          let stacks_at_exit = trap_stacks handler ~stack ~stacks_at_exit in
          let new_handlers_with_uses, handlers_without_uses =
            Int.Map.partition (fun cont _handler ->
                Int.Map.mem cont stacks_at_exit)
              handlers_without_uses
          in
          let handlers_with_uses =
            Int.Map.disjoint_union handlers_with_uses new_handlers_with_uses
          in
          process_handlers ~stacks_at_exit ~handlers_with_uses
            ~handlers_without_uses
    in
    let handlers, stacks_at_exit =
      process_handlers ~stacks_at_exit ~handlers_with_uses
        ~handlers_without_uses
    in
    let next, stacks_at_exit = trap_stacks insn.Mach.next ~stack in
    { insn with
      desc = Icatch (rec_flag, is_exn_handler, handlers, body);
      next;
    }, stacks_at_exit
  | Iexit cont ->
    let stacks_at_exit = add_stack ~cont ~stack ~stacks_at_exit in
    let next, stacks_at_exit =
      trap_stacks insn.Mach.next ~stack ~stacks_at_exit
    in
    insn, stacks_at_exit

let run (fundecl : Mach.fundecl) =
  let stacks_at_exit =
    trap_stacks fundecl.fun_body ~stack:[] ~stacks_at_exit:Int.Map.empty
  in
  { fundecl with
    fun_trap_stacks_at_handlers = stacks_at_exit;
  }
