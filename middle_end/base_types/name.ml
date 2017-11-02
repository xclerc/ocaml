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

module Const = struct
  type t =
    | Untagged_immediate of Immediate.t
    | Tagged_immediate of Immediate.t
    | Naked_float of float
    | Naked_int32 of Int32.t
    | Naked_int64 of Int64.t
    | Naked_nativeint of Targetint.t

  include Identifiable.Make (struct
    type nonrec t = t

    let compare t1 t2 =
      match t1, t2 with
      | Untagged_immediate i1, Untagged_immediate i2 ->
        Immediate.compare i1 i2
      | Tagged_immediate i1, Tagged_immediate i2 ->
        Immediate.compare i1 i2
      | Naked_float f1, Naked_float f2 ->
        Pervasives.compare f1 f2
      | Naked_int32 n1, Naked_int32 n2 ->
        Int32.compare n1 n2
      | Naked_int64 n1, Naked_int64 n2 ->
        Int64.compare n1 n2
      | Naked_nativeint n1, Naked_nativeint n2 ->
        Targetint.compare n1 n2
      | Untagged_immediate _, _ -> -1
      | _, Untagged_immediate _ -> 1
      | Tagged_immediate _, _ -> -1
      | _, Tagged_immediate _ -> 1
      | Naked_float _, _ -> -1
      | _, Naked_float _ -> 1
      | Naked_int32 _, _ -> -1
      | _, Naked_int32 _ -> 1
      | Naked_int64 _, _ -> -1
      | _, Naked_int64 _ -> 1

    let equal t1 t2 = (compare t1 t2 = 0)

    let hash t =
      match t with
      | Untagged_immediate n -> Immediate.hash n
      | Tagged_immediate n -> Immediate.hash n
      | Naked_float n -> Hashtbl.hash n
      | Naked_int32 n -> Hashtbl.hash n
      | Naked_int64 n -> Hashtbl.hash n
      | Naked_nativeint n -> Targetint.hash n

    let print ppf (t : t) =
      match t with
      | Untagged_immediate i -> Format.fprintf ppf "%a!" Immediate.print i
      | Tagged_immediate i -> Format.fprintf ppf "%a" Immediate.print i
      | Naked_float f -> Format.fprintf ppf "%f!" f
      | Naked_int32 n -> Format.fprintf ppf "%ld!" n
      | Naked_int64 n -> Format.fprintf ppf "%Ld!" n
      | Naked_nativeint n -> Format.fprintf ppf "%a!" Targetint.print n
  end)
end

type t =
  | Var of Variable.t
  | Symbol of Symbol.t
  | Const of Const.t

let var v = Var v
let symbol s = Symbol s
let const c = Const c

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
    | Const c -> Const.print ppf c

  let hash t =
    match t with
    | Var var -> Hashtbl.hash (0, Variable.hash var)
    | Symbol sym -> Hashtbl.hash (1, Symbol.hash sym)
    | Const c -> Hashtbl.hash (2, Const.hash c)

  let compare t1 t2 =
    match t1, t2 with
    | Var var1, Var var2 -> Variable.compare var1 var2
    | Symbol sym1, Symbol sym2 -> Symbol.compare sym1 sym2
    | Const c1, Const c2 -> Const.compare c1 c2
    | Var _, Symbol _ -> -1
    | Var _, Const _ -> -1
    | Symbol _, Var _ -> 1
    | Symbol _, Const _ -> -1
    | Const _, Var _ -> 1
    | Const _, Symbol _ -> 1
end)
