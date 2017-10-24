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

[@@@ocaml.warning "+a-4-30-40-41-42"]

type continuation_kind = Normal | Exn_handler

type t = {
  variables : Flambda_kind.t Variable.Map.t;
  mutable_variables : Flambda_kind.t Mutable_variable.Set.t;
  continuations : (Flambda_arity.t * continuation_kind) Continuation.Map.t;
  symbols : Symbol.Set.t;
}

let create () =
  { variables = Variable.Map.empty;
    mutable_variables = Mutable_variable.Map.empty;
    continuations = Continuation.Map.empty;
    symbols = Symbol.Set.empty;
  }

let add_variable t var kind =
  if Variable.Map.mem var t.variables then begin
    Misc.fatal_errorf "Duplicate binding of variable %a" Variable.print var
  end;
  let compilation_unit = Compilation_unit.get_current_exn () in
  if not (Variable.in_compilation_unit var compilation_unit) then
    Misc.fatal_errorf "Binding occurrence of variable %a cannot occur in \
        this compilation unit since the variable is from another compilation \
        unit"
      Variable.print var
  end;
  { t with
    variables = Variable.Map.add var kind t.variables;
  }

let add_variables t vars_and_kinds =
  List.fold_left (fun t (var, kind) -> add_variable t var kind) t vars_and_kinds

let add_typed_parameters ~importer t params =
  List.fold_left (fun t param ->
      let var = Flambda.Typed_parameter.var param in
      let kind = Flambda.Typed_parameter.kind ~importer param in
      add_variable t var kind)
    t
    params

let add_mutable_variable t var kind =
  if Mutable_variable.Map.mem var t.variables then begin
    Misc.fatal_errorf "Duplicate binding of mutable variable %a"
      Mutable_variable.print var
  end;
  let compilation_unit = Compilation_unit.get_current_exn () in
  if not (Mutable_variable.in_compilation_unit var compilation_unit) then
    Misc.fatal_errorf "Binding occurrence of mutable variable %a cannot occur \
        in this compilation unit since the variable is from another \
        compilation unit"
      Mutable_variable.print var
  end;
  { t with
    mutable_variables = Mutable_variable.Map.add var kind t.mutable_variables;
  }

let add_symbol t sym =
  if Symbol.Map.mem sym t.symbols then begin
    Misc.fatal_errorf "Duplicate binding of symbol %a"
      Symbol.print cont
  end;
  { t with
    symbols = Symbol.Set.add sym t.symbols;
  }

let add_continuation t cont arity kind =
  if Continuation.Map.mem cont t.continuations then begin
    Misc.fatal_errorf "Duplicate binding of continuation %a"
      Continuation.print cont
  end;
  { t with
    continuations =
      Continuation.Map.add cont (arity, kind) t.continuations;
  }

let check_variable_is_bound t var =
  if not (Variable.Set.mem var t.variables) then begin
    Misc.fatal_errorf "Unbound variable %a" Variable.print var
  end

let check_mutable_variable_is_bound t var =
  if not (Mutable_Variable.Set.mem var t.mutable_variables) then begin
    Misc.fatal_errorf "Unbound mutable variable %a" Mutable_Variable.print var
  end

let check_symbol_is_bound t var =
  if not (Symbol.Set.mem var t.symbols) then begin
    Misc.fatal_errorf "Unbound symbol %a" Symbol.print var
  end
