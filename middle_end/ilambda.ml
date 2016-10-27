(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Eo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2016 OCamlPro SAS                                          *)
(*   Copyright 2016 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Esser General Public Icense version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42-49"]

module L = Lambda

type switch_block_pattern =
  | Tag of int
  | String of string

type t =
  | Let of L.let_kind * L.value_kind * Ident.t * named * t
  | Let_rec of (Ident.t * function_declaration) list * t
  | Let_cont of Continuation.t * Ident.t list * t (* <-- code of cont'n *) * t
  | Apply of apply
  | Apply_cont of Continuation.t * Ident.t list
  | Switch of Ident.t * switch
  | Send of L.meth_kind * t * t * t list * Location.t
  | Event of t * L.lambda_event

and named =
  | Var of Ident.t
  | Const of L.structured_constant
  | Function of function_declaration
  | Prim of L.primitive * Ident.t list * Location.t

and function_declaration =
  { kind : L.function_kind;
    continuation_param : Continuation.t;
    params : Ident.t list;
    body : t;
    attr : L.function_attribute;
    loc : Location.t;
    free_idents_of_body : L.IdentSet.t;
  }

and apply =
  { func : Ident.t;
    args : Ident.t list;
    continuation : Continuation.t;
    loc : Location.t;
    should_be_tailcall : bool;
    inlined : L.inline_attribute;
    specialised : L.specialise_attribute;
  }

and switch =
  { numconsts : int;
    consts : (int * t) list;
    numblocks : int;
    blocks : (switch_block_pattern * t) list;
    failaction : t option;
  }

let rec lam ppf (t : t) =
  let fprintf = Format.fprintf in
  match t with
  | Var id ->
      Ident.print ppf id
  | Const cst ->
      Printlambda.structured_constant ppf cst
  | Apply ap ->
      let lams ppf largs =
        List.iter (fun l -> fprintf ppf "@ %a" lam l) largs in
      fprintf ppf "@[<2>(apply@ %a%a%a%a%a)@]" lam ap.func lams ap.args
        Printlambda.apply_tailcall_attribute ap.should_be_tailcall
        Printlambda.apply_inlined_attribute ap.inlined
        Printlambda.apply_specialised_attribute ap.specialised
  | Function{kind; params; body; attr} ->
      let pr_params ppf params =
        match kind with
        | Curried ->
            List.iter (fun param -> fprintf ppf "@ %a" Ident.print param) params
        | Tupled ->
            fprintf ppf " (";
            let first = ref true in
            List.iter
              (fun param ->
                if !first then first := false else fprintf ppf ",@ ";
                Ident.print ppf param)
              params;
            fprintf ppf ")" in
      fprintf ppf "@[<2>(function%a@ %a%a)@]" pr_params params
        Printlambda.function_attribute attr lam body
  | Let(str, k, id, arg, body) ->
      let kind (kind : Lambda.let_kind) =
        match kind with
        | Alias -> "a" | Strict -> "" | StrictOpt -> "o" | Variable -> "v"
      in
      let rec letbody = function
        | Let(str, k, id, arg, body) ->
            fprintf ppf "@ @[<2>%a =%s%s@ %a@]"
              Ident.print id (kind str) (Printlambda.value_kind k) lam arg;
            letbody body
        | expr -> expr in
      fprintf ppf "@[<2>(let@ @[<hv 1>(@[<2>%a =%s%s@ %a@]"
        Ident.print id (kind str) (Printlambda.value_kind k) lam arg;
      let expr = letbody body in
      fprintf ppf ")@]@ %a)@]" lam expr
  | Let_rec(id_arg_list, body) ->
      let bindings ppf id_arg_list =
        let spc = ref false in
        List.iter
          (fun (id, l) ->
            if !spc then fprintf ppf "@ " else spc := true;
            fprintf ppf "@[<2>%a@ %a@]" Ident.print id lam l)
          id_arg_list in
      fprintf ppf
        "@[<2>(letrec@ (@[<hv 1>%a@])@ %a)@]" bindings id_arg_list lam body
  | Prim(prim, largs, _) ->
      let lams ppf largs =
        List.iter (fun l -> fprintf ppf "@ %a" lam l) largs in
      fprintf ppf "@[<2>(%a%a)@]" Printlambda.primitive prim lams largs
  | Switch(larg, sw) ->
      let switch ppf sw =
        let spc = ref false in
        List.iter
         (fun (n, l) ->
           if !spc then fprintf ppf "@ " else spc := true;
           fprintf ppf "@[<hv 1>case int %i:@ %a@]" n lam l)
         sw.consts;
        List.iter
          (fun (n, l) ->
            if !spc then fprintf ppf "@ " else spc := true;
            fprintf ppf "@[<hv 1>case tag %i:@ %a@]" n lam l)
          sw.blocks ;
        begin match sw.failaction with
        | None  -> ()
        | Some l ->
            if !spc then fprintf ppf "@ " else spc := true;
            fprintf ppf "@[<hv 1>default:@ %a@]" lam l
        end in
      fprintf ppf
       "@[<1>(%s %a@ @[<v 0>%a@])@]"
       (match sw.failaction with None -> "switch*" | _ -> "switch")
       lam larg switch sw
  | String_switch(arg, cases, default, _) ->
      let switch ppf cases =
        let spc = ref false in
        List.iter
         (fun (s, l) ->
           if !spc then fprintf ppf "@ " else spc := true;
           fprintf ppf "@[<hv 1>case \"%s\":@ %a@]" (String.escaped s) lam l)
          cases;
        begin match default with
        | Some default ->
            if !spc then fprintf ppf "@ " else spc := true;
            fprintf ppf "@[<hv 1>default:@ %a@]" lam default
        | None -> ()
        end in
      fprintf ppf
       "@[<1>(stringswitch %a@ @[<v 0>%a@])@]" lam arg switch cases
  | Apply_cont (i, ls)  ->
      let lams ppf largs =
        List.iter (fun l -> fprintf ppf "@ %a" lam l) largs in
      fprintf ppf "@[<2>(apply_cont@ %d%a)@]" i lams ls;
  | Let_cont (lbody, i, vars, lhandler) ->
      fprintf ppf "@[<2>(let_cont@ %a@;<1 -1>where (%d%a)@ %a)@]"
        lam lbody i
        (fun ppf vars -> match vars with
          | [] -> ()
          | _ ->
              List.iter
                (fun x -> fprintf ppf " %a" Ident.print x)
                vars)
        vars
        lam lhandler
  | Try_with(lbody, param, lhandler) ->
      fprintf ppf "@[<2>(try@ %a@;<1 -1>with %a@ %a)@]"
        lam lbody Ident.print param lam lhandler
  | If_then_else(lcond, lif, lelse) ->
      fprintf ppf "@[<2>(if@ %a@ %a@ %a)@]" lam lcond lam lif lam lelse
  | Send (k, met, obj, largs, _) ->
      let args ppf largs =
        List.iter (fun l -> fprintf ppf "@ %a" lam l) largs in
      let kind =
        match k with
        | Self -> "self"
        | Cached -> "cache"
        | _ -> ""
      in
      fprintf ppf "@[<2>(send%s@ %a@ %a%a)@]" kind lam obj lam met args largs
  | Event(expr, ev) ->
      let kind =
       match ev.lev_kind with
       | Lev_before -> "before"
       | Lev_after _  -> "after"
       | Lev_function -> "funct-body"
       | Lev_pseudo -> "pseudo"
      in
      fprintf ppf "@[<2>(%s %s(%i)%s:%i-%i@ %a)@]" kind
              ev.lev_loc.Location.loc_start.Lexing.pos_fname
              ev.lev_loc.Location.loc_start.Lexing.pos_lnum
              (if ev.lev_loc.Location.loc_ghost then "<ghost>" else "")
              ev.lev_loc.Location.loc_start.Lexing.pos_cnum
              ev.lev_loc.Location.loc_end.Lexing.pos_cnum
              lam expr

let print = lam
