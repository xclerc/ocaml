(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* XXX mshinwell: To be done using Pierre and Vincent's new analysis *)

(*
[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module BF = Flambda_static.Constant_defining_value_block_field

let constant_expr (expr : Flambda.Expr.t) cont =
  match expr with
  | Let { var; defining_expr = Const (Tagged_immediate imm);
        body = Apply_cont (cont', None, [var']); _ }
      when Continuation.equal cont cont' ->
    (* CR mshinwell: This needs a more complicated analysis to cope with
       the case where the continuation has multiple arguments. *)
    assert (Variable.equal var var');
    (* This must be true since var is the only variable in scope *)
    Some [BF.Tagged_immediate imm]
  | Let { var; defining_expr = Symbol s;
        body = Apply_cont (cont', None, [var']); _ }
      when Continuation.equal cont cont' ->
    assert (Variable.equal var var');
    Some [BF.Symbol s]
  | _ ->
    None

let rec loop (program : Flambda_static.Program_body.t)
      : Flambda_static.Program_body.t =
  match program with
  | Initialize_symbol (symbol, descr, program) ->
    begin match constant_expr descr.expr descr.return_cont with
    | None ->
      Initialize_symbol (symbol, descr, loop program)
    | Some fields ->
      Let_symbol (symbol, Block (descr.tag, fields), loop program)
    end
  | Let_symbol (symbol, const, program) ->
    Let_symbol (symbol, const, loop program)
  | Let_rec_symbol (defs, program) ->
    Let_rec_symbol (defs, loop program)
  | Effect (expr, cont, program) ->
    Effect (expr, cont, loop program)
  | End symbol ->
    End symbol

let run (program : Flambda_static.Program.t) =
  { program with
    program_body = loop program.program_body;
  }

*)

let run (program : Flambda_static.Program.t) = program
