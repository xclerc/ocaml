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

type 'a or_wrong =
  | Ok of 'a
  | Wrong

type t = {
  value : Targetint.t;
  print_as_char : bool;
}

let print ppf t =
  let print_as_char =
    t.print_as_char
      && Targetint.compare t Targetint.zero >= 0
      && Targetint.compare t (Targetint.of_int 0xff) <= 0
  in
  if print_as_char then
    Format.fprintf ppf "(immediate '%c')"
      (Char.chr (Targetint.to_int t.value))
  else
    Format.fprintf ppf "(immediate %a)"
      Targetint.print t.value

let join t1 t2 : t or_wrong =
  if not (Targetint.equal t1.value t2.value) then
    Wrong
  else
    let print_as_char = t1.print_as_char && t2.print_as_char in
    Ok {
      value = t1.value;
      print_as_char;
    }
