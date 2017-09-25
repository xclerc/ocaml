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

include Identifiable.Make (struct
  type nonrec t = t

  let compare t1 t2 = Targetint.compare t1.value t2.value

  let equal t1 t2 = Targetint.equal t1.value t2.value

  let hash t = Targetint.hash t.value

  let print ppf t =
    let print_as_char =
      t.print_as_char
        && Targetint.compare t.value Targetint.zero >= 0
        && Targetint.compare t.value (Targetint.of_int 0xff) <= 0
    in
    if print_as_char then
      Format.fprintf ppf "(immediate '%c')"
        (Char.chr (Targetint.to_int t.value))
    else
      Format.fprintf ppf "(immediate %a)"
        Targetint.print t.value
end)

let join t1 t2 : t or_wrong =
  if not (Targetint.equal t1.value t2.value) then
    Wrong
  else
    let print_as_char = t1.print_as_char && t2.print_as_char in
    Ok {
      value = t1.value;
      print_as_char;
    }

let join_set t1s t2s =
  let only_in_t2s = Set.diff t2s t1s in
  let join =
    Set.fold (fun t1 result ->
        match Set.find t1 t2s with
        | exception Not_found -> Set.add t1 result
        | t2 ->
          match join t1 t2 with
          | Wrong -> result
          | Ok t -> Set.add t result)
      t1s
      Set.empty
  in
  Set.union join only_in_t2s

let bool_true = {
  value = Targetint.of_int 1;
  print_as_char = false;
}

let bool_false = {
  value = Targetint.of_int 0;
  print_as_char = false;
}
