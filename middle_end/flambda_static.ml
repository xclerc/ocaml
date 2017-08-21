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

module rec Constant_defining_value : sig
  type t =
    | Allocated_const of Allocated_const.t
    | Block of Tag.t * Constant_defining_value_block_field.t list
    | Set_of_closures of set_of_closures  (* [free_vars] must be empty *)
    | Project_closure of Symbol.t * Closure_id.t

  include Identifiable.S with type t := t
end = struct
  include Constant_defining_value

  include Identifiable.Make (struct
    type nonrec t = t

    let compare (t1 : t) (t2 : t) =
      match t1, t2 with
      | Allocated_const c1, Allocated_const c2 ->
        Allocated_const.compare c1 c2
      | Block (tag1, fields1), Block (tag2, fields2) ->
        let c = Tag.compare tag1 tag2 in
        if c <> 0 then c
        else
          Misc.Stdlib.List.compare compare_constant_defining_value_block_field
            fields1 fields2
      | Set_of_closures set1, Set_of_closures set2 ->
        Set_of_closures_id.compare set1.function_decls.set_of_closures_id
          set2.function_decls.set_of_closures_id
      | Project_closure (set1, closure_id1),
          Project_closure (set2, closure_id2) ->
        let c = Symbol.compare set1 set2 in
        if c <> 0 then c
        else Closure_id.compare closure_id1 closure_id2
      | Allocated_const _, Block _ -> -1
      | Allocated_const _, Set_of_closures _ -> -1
      | Allocated_const _, Project_closure _ -> -1
      | Block _, Allocated_const _ -> 1
      | Block _, Set_of_closures _ -> -1
      | Block _, Project_closure _ -> -1
      | Set_of_closures _, Allocated_const _ -> 1
      | Set_of_closures _, Block _ -> 1
      | Set_of_closures _, Project_closure _ -> -1
      | Project_closure _, Allocated_const _ -> 1
      | Project_closure _, Block _ -> 1
      | Project_closure _, Set_of_closures _ -> 1

    let equal t1 t2 =
      t1 == t2 || compare t1 t2 = 0

    let hash = Hashtbl.hash

    let print ppf (t : t) =
      match t with
      | Allocated_const const ->
        fprintf ppf "(Allocated_const %a)" Allocated_const.print const
      | Block (tag, []) ->
        fprintf ppf "(Empty block (tag %a))" (Tag.print tag)
      | Block (tag, fields) ->
        fprintf ppf "(Block (tag %d, %a))" (Tag.to_int tag)
          (Format.pp_print_list ~sep:pp_print_space
            Constant_defining_value_block_field.print) fields
      | Set_of_closures set_of_closures ->
        fprintf ppf "@[<2>(Set_of_closures (@ %a))@]"
          Set_of_closures.print set_of_closures
      | Project_closure (set_of_closures, closure_id) ->
        fprintf ppf "(Project_closure (%a, %a))"
          Symbol.print set_of_closures
          Closure_id.print closure_id

    let output o v =
      output_string o (Format.asprintf "%a" print v)
  end)

  let free_symbols_helper symbols (const : t) =
    match const with
    | Allocated_const _ -> ()
    | Block (_, fields) ->
      List.iter
        (function
          | (Symbol s : constant_defining_value_block_field) ->
            symbols := Symbol.Set.add s !symbols
          | (Const _ : constant_defining_value_block_field) -> ())
        fields
    | Set_of_closures set_of_closures ->
      symbols := Symbol.Set.union !symbols
        (free_symbols_named (Set_of_closures set_of_closures))
    | Project_closure (s, _) ->
      symbols := Symbol.Set.add s !symbols
end and Constant_defining_value_block_field : sig
  type t =
    | Symbol of Symbol.t
    | Const of const

  include Identifiable.S with type t := t
end = struct
  include Constant_defining_value_block_field

  let compare (t1 : t) (t2 : t) =
    match t1, t2 with
    | Symbol s1, Symbol s2 -> Symbol.compare s1 s2
    | Const t1, Const t2 -> Const.compare t1 t2
    | Symbol _, Const _ -> -1
    | Const _, Symbol _ -> 1

  let print ppf (field : t) =
    match field with
    | Symbol symbol -> Symbol.print ppf symbol
    | Const const -> Const.print ppf const
end

type program_body =
  | Let_symbol of Symbol.t * constant_defining_value * program_body
  | Let_rec_symbol of (Symbol.t * constant_defining_value) list * program_body
  | Initialize_symbol of Symbol.t * Tag.t * (t * Continuation.t) list
      * program_body
  | Effect of t * Continuation.t * program_body
  | End of Symbol.t

module Program : sig
  type t = {
    imported_symbols : Symbol.Set.t;
    program_body : program_body;
  }
end = struct
  include Program

  let free_symbols (program : t) =
    let symbols = ref Symbol.Set.empty in
    let rec loop (program : program_body) =
      match program with
      | Let_symbol (_, const, program) ->
        free_symbols_allocated_constant_helper symbols const;
        loop program
      | Let_rec_symbol (defs, program) ->
        List.iter (fun (_, const) ->
            free_symbols_allocated_constant_helper symbols const)
          defs;
        loop program
      | Initialize_symbol (_, _, fields, program) ->
        List.iter (fun (field, _cont) ->
            symbols := Symbol.Set.union !symbols (free_symbols field))
          fields;
        loop program
      | Effect (expr, _cont, program) ->
        symbols := Symbol.Set.union !symbols (free_symbols expr);
        loop program
      | End symbol -> symbols := Symbol.Set.add symbol !symbols
    in
    (* Note that there is no need to count the [imported_symbols]. *)
    loop program.program_body;
    !symbols
end
