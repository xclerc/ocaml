
module Return_arity = struct
  let print ppf t =
    Format.fprintf ppf "@(%a@)"
      (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ")
        Flambda_kind.print)
      t
end

module Const = struct
  type t = Flambda0.Const.t

  let print ppf (t : t) =
    match t with
    | Int n -> Format.fprintf ppf "%i" n
    | Char c -> Format.fprintf ppf "%C" c
    | Const_pointer n -> Format.fprintf ppf "%ia" n
    | Unboxed_float f -> Format.fprintf ppf "%f" f
    | Unboxed_int32 n -> Format.fprintf ppf "%ld" n
    | Unboxed_int64 n -> Format.fprintf ppf "%Ld" n
    | Unboxed_nativeint n -> Format.fprintf ppf "%nd" n
end

module Free_var = struct
  type t = Flambda0.Free_var.t

  let print ppf (t : t) =
    match t.projection with
    | None ->
      fprintf ppf "%a" Variable.print t.var
    | Some projection ->
      fprintf ppf "%a(= %a)"
        Variable.print t.var
        Projection.print projection
end

module Free_vars = struct
  let print ppf free_vars =
    Variable.Map.iter (fun inner_var outer_var ->
        fprintf ppf "@ %a -rename-> %a"
          Variable.print inner_var
          Free_var.print outer_var)
      free_vars
end

module Trap_action = struct
  let print ppf t =
    match t with
    | None -> ()
    | Some (Push { id; exn_handler; }) ->
      fprintf ppf "push %a %a then "
        Trap_id.print id
        Continuation.print exn_handler
    | Some (Pop { id; exn_handler; }) ->
      fprintf ppf "pop %a %a then "
        Trap_id.print id
        Continuation.print exn_handler
end

module Switch = struct
  let print ppf (t : t) =
    let spc = ref false in
    List.iter (fun (n, l) ->
        if !spc then fprintf ppf "@ " else spc := true;
        fprintf ppf "@[<hv 1>| %i ->@ goto %a@]" n Continuation.print l)
      t.consts;
    begin match t.failaction with
    | None  -> ()
    | Some l ->
      if !spc then fprintf ppf "@ " else spc := true;
      let module Int = Int in
      fprintf ppf "@[<hv 1>| _ ->@ goto %a@]" Continuation.print l
    end
end

module rec Expr : sig
  type t = Flambda0.Expr.t

  val print : Format.formatter -> t -> unit
end = struct
  include Expr

  let rec print ppf (t : t) =
    match t with
    | Apply ({ kind; func; continuation; args; call_kind; inline; dbg; }) ->
      let print_func_and_kind ppf func =
        match kind with
        | Function -> Variable.print ppf func
        | Method { kind; obj; } ->
          Format.fprintf ppf "send%a %a#%a"
            Printlambda.meth_kind kind
            Variable.print obj
            Variable.print func
      in
      let direct ppf () =
        match call_kind with
        | Indirect -> ()
        | Direct { closure_id; _ } ->
          fprintf ppf "*[%a]" Closure_id.print closure_id
      in
      let inline ppf () =
        match inline with
        | Always_inline -> fprintf ppf "<always>"
        | Never_inline -> fprintf ppf "<never>"
        | Unroll i -> fprintf ppf "<unroll %i>" i
        | Default_inline -> ()
      in
      fprintf ppf "@[<2>(apply%a%a<%s>%a@ <%a> %a %a)@]"
        direct ()
        inline ()
        (Debuginfo.to_string dbg)
        Return_arity.print (Call_kind.return_arity call_kind)
        Continuation.print continuation
        print_func_and_kind func
        Variable.print_list args
    | Let { var = id; defining_expr = arg; body; _ } ->
        let rec letbody (ul : t) =
          match ul with
          | Let { var = id; defining_expr = arg; body; _ } ->
              fprintf ppf "@ @[<2>%a@ %a@]" Variable.print id Named.print arg;
              letbody body
          | _ -> ul
        in
        fprintf ppf "@[<2>(let@ @[<hv 1>(@[<2>%a@ %a@]"
          Variable.print id Named.print arg;
        let expr = letbody body in
        fprintf ppf ")@]@ %a)@]" print expr
    | Let_mutable { var = mut_var; initial_value = var; body; contents_kind } ->
      fprintf ppf "@[<2>(let_mutable%a@ @[<2>%a@ %a@]@ %a)@]"
        Flambda_kind.print contents_kind
        Mutable_variable.print mut_var
        Variable.print var
        print body
    | Switch (scrutinee, sw) ->
      fprintf ppf
        "@[<v 1>(switch %a@ @[<v 0>%a@])@]"
        Variable.print scrutinee Switch.print sw
    | Apply_cont (i, trap_action, []) ->
      fprintf ppf "@[<2>(%agoto@ %a)@]"
        Trap_action.print trap_action
        Continuation.print i
    | Apply_cont (i, trap_action, ls) ->
      fprintf ppf "@[<2>(%aapply_cont@ %a@ %a)@]"
        Trap_action.print trap_action
        Continuation.print i
        Variable.print_list ls
    | Let_cont { body; handlers; } ->
      (* Printing the same way as for [Let] is easier when debugging lifting
         passes. *)
      if !Clflags.dump_let_cont then begin
        let rec let_cont_body (ul : t) =
          match ul with
          | Let_cont { body; handlers; } ->
            fprintf ppf "@ @[<2>%a@]" Let_cont_handlers.print handlers;
            let_cont_body body
          | _ -> ul
        in
        fprintf ppf "@[<2>(let_cont@ @[<hv 1>(@[<2>%a@]"
          Let_cont_handlers.print handlers;
        let expr = let_cont_body body in
        fprintf ppf ")@]@ %a)@]" print expr
      end else begin
        (* CR mshinwell: Share code with ilambda.ml *)
        let rec gather_let_conts let_conts (t : t) =
          match t with
          | Let_cont let_cont ->
            gather_let_conts (let_cont.handlers :: let_conts) let_cont.body
          | body -> let_conts, body
        in
        let let_conts, body = gather_let_conts [] t in
        let pp_sep ppf () = fprintf ppf "@ " in
        fprintf ppf "@[<2>(@[<v 0>%a@;@[<v 0>%a@]@])@]"
          Expr.print body
          (Format.pp_print_list ~pp_sep
            Let_cont_handlers.print_using_where) let_conts
      end
    | Proved_unreachable -> fprintf ppf "unreachable"

  let print ppf t =
    fprintf ppf "%a@." print t
end and Named : sig
  type t = Flambda0.Named.t

  val print : Format.formatter -> t -> unit
end = struct
  type t = Flambda0.Named.t

  let print ppf (t : t) =
    match t with
    | Var var -> Variable.print ppf var
    | Symbol symbol -> Symbol.print ppf symbol
    | Const cst -> fprintf ppf "Const(%a)" Const.print cst
    | Allocated_const cst -> fprintf ppf "Aconst(%a)" Allocated_const.print cst
    | Read_mutable mut_var ->
      fprintf ppf "Read_mut(%a)" Mutable_variable.print mut_var
    | Assign { being_assigned; new_value; } ->
      fprintf ppf "@[<2>(assign@ %a@ %a)@]"
        Mutable_variable.print being_assigned
        Variable.print new_value
    | Read_symbol_field (symbol, field) ->
      fprintf ppf "%a.(%d)" Symbol.print symbol field
    | Project_closure project_closure ->
      Projection.Project_closure.print ppf project_closure
    | Project_var project_var ->
      Projection.Project_var.print ppf project_var
    | Move_within_set_of_closures move_within_set_of_closures ->
      Projection.Move_within_set_of_closures.print ppf
        move_within_set_of_closures
    | Set_of_closures set_of_closures ->
      Set_of_closures.print ppf set_of_closures
    | Prim (prim, args, dbg) ->
      fprintf ppf "@[<2>(%a@ <%s>@ %a)@]"
        Printlambda.primitive prim
        (Debuginfo.to_string dbg)
        Variable.print_list args
end

module Function_declaration = struct
  type t = Flambda0.Function_declaration

  let print var ppf (f : t) =
    let stub =
      if f.stub then
        " *stub*"
      else
        ""
    in
    let is_a_functor =
      if f.is_a_functor then
        " *functor*"
      else
        ""
    in
    let inline =
      match f.inline with
      | Always_inline -> " *inline*"
      | Never_inline -> " *never_inline*"
      | Unroll _ -> " *unroll*"
      | Default_inline -> ""
    in
    let specialise =
      match f.specialise with
      | Always_specialise -> " *specialise*"
      | Never_specialise -> " *never_specialise*"
      | Default_specialise -> ""
    in
    fprintf ppf
      "@[<2>(%a%s( return arity %a)%s%s%s(origin %a)@ =@ \
        fun@[<2> <%a>%a@] ->@ @[<2>%a@])@]@ "
      Variable.print var
      stub
      Return_arity.print f.return_arity
      is_a_functor inline specialise
      Closure_origin.print f.closure_origin
      Continuation.print f.continuation_param
      Typed_parameter.List.print f.params
      Expr.print f.body
end
