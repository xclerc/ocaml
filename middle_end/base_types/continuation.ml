(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

include Numbers.Int

(* Imported from Lambda *)
let raise_count = ref 0

let next_raise_count () =
Format.eprintf "Creation of continuation %d:\n%s\n%!"
  (!raise_count + 1)
  (Printexc.raw_backtrace_to_string (Printexc.get_callstack 10));
  incr raise_count ;
  !raise_count

let reset () =
  raise_count := 0
(* </> Imported from Lambda *)

let create () = next_raise_count ()
let to_int t = t

let print ppf t = Format.fprintf ppf "k%d" t
