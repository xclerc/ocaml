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

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

type t =
  | Var of Variable.t
  | Symbol of Symbol.t

let var v = Var v
let symbol s = Symbol s

let map_var t ~f =
  match t with
  | Var var ->
    let var' = f var in
    if var == var' then t
    else Var var'
  | Symbol _ -> t

include Identifiable.Make (struct
  type nonrec t = t

  let print ppf t =
    match t with
    | Var var -> Variable.print ppf var
    | Symbol sym -> Symbol.print ppf sym

  let hash t =
    match t with
    | Var var -> Hashtbl.hash (0, Variable.hash var)
    | Symbol sym -> Hashtbl.hash (1, Symbol.hash sym)

  let compare t1 t2 =
    match t1, t2 with
    | Var var1, Var var2 -> Variable.compare var1 var2
    | Symbol sym1, Symbol sym2 -> Symbol.compare sym1 sym2
    | Var _, Symbol _ -> -1
    | Var _, Const _ -> -1
    | Symbol _, Var _ -> 1
end)