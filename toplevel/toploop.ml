(***********************************************************************)
(*                                                                     *)
(*                         Caml Special Light                          *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1995 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(* The interactive toplevel loop *)

open Lexing
open Format
open Config
open Misc
open Parsetree
open Typedtree
open Printval

type directive_fun =
    Directive_none of (unit -> unit)
  | Directive_string of (string -> unit)
  | Directive_int of (int -> unit)
  | Directive_ident of (Longident.t -> unit)

(* Load in-core and execute a lambda term *)

type evaluation_outcome = Result of Obj.t | Exception of exn

let load_lambda lam =
  if !Clflags.dump_rawlambda then begin
    Printlambda.lambda lam; print_newline()
  end;
  let slam = Simplif.simplify_lambda lam in
  if !Clflags.dump_lambda then begin
    Printlambda.lambda slam; print_newline()
  end;
  let (init_code, fun_code) = Bytegen.compile_phrase slam in
  if !Clflags.dump_instr then begin
    Printinstr.instrlist init_code;
    Printinstr.instrlist fun_code;
    print_newline()
  end;
  let (code, code_size, reloc) = Emitcode.to_memory init_code fun_code in
  let can_free = (fun_code = []) in
  let initial_symtable = Symtable.current_state() in
  Symtable.patch_object code reloc;
  Symtable.update_global_table();
  try
    let retval = Meta.execute_bytecode code code_size in
    if can_free then Meta.static_free code;
    Result retval
  with x ->
    if can_free then Meta.static_free code;
    Symtable.restore_state initial_symtable;
    Exception x

(* Print the outcome of an evaluation *)

let print_item env = function
    Tsig_value(id, decl) ->
      open_hovbox 2;
      begin match decl.val_prim with
        None ->
          print_string "val "; Printtyp.ident id;
          print_string " :"; print_space();
          Printtyp.type_scheme decl.val_type;
          print_string " ="; print_space();
          print_value env (Symtable.get_global_value id) decl.val_type
      | Some p ->
          print_string "external "; Printtyp.ident id;
          print_string " :"; print_space();
          Printtyp.type_scheme decl.val_type; print_space();
          print_string "= "; Primitive.print_description p
      end;
      close_box()
  | Tsig_type(id, decl) ->
      Printtyp.type_declaration id decl
  | Tsig_exception(id, decl) ->
      Printtyp.exception_declaration id decl
  | Tsig_module(id, mty) ->
      open_hovbox 2; print_string "module "; Printtyp.ident id;
      print_string " :"; print_space(); Printtyp.modtype mty; close_box()
  | Tsig_modtype(id, decl) ->
      Printtyp.modtype_declaration id decl

(* Print an exception produced by an evaluation *)

let print_exception_outcome = function
    Sys.Break ->
      print_string "Interrupted."; print_newline()
  | Out_of_memory ->
      Gc.full_major();
      print_string "Out of memory during evaluation";
      print_newline()
  | exn ->
      open_hovbox 0;
      print_string "Uncaught exception: ";
      print_exception (Obj.repr exn);
      print_newline()

(* The table of toplevel directives. 
   Filled by functions from module topdirs. *)

let directive_table = (Hashtbl.new 13 : (string, directive_fun) Hashtbl.t)

(* Execute a toplevel phrase *)

let toplevel_env = ref Env.empty

let execute_phrase phr =
  Location.reset();
  match phr with
    Ptop_def sstr ->
      let (str, sg, newenv) = Typemod.type_structure !toplevel_env sstr in
      let lam = Translmod.transl_toplevel_definition str in
      let res = load_lambda lam in
      begin match res with
        Result v ->
          begin match str with
            [Tstr_eval exp] ->
              open_hovbox 0;
              print_string "- : ";
              Printtyp.type_scheme exp.exp_type;
              print_space(); print_string "="; print_space();
              print_value newenv v exp.exp_type;
              close_box();
              print_newline()
          | _ ->
              open_vbox 0;
              List.iter (fun item -> print_item newenv item; print_space()) sg;
              close_box();
              print_flush()
          end;
          toplevel_env := newenv;
          true
      | Exception exn ->
          print_exception_outcome exn;
          false
      end
  | Ptop_dir(dir_name, dir_arg) ->
      try
        match (Hashtbl.find directive_table dir_name, dir_arg) with
          (Directive_none f, Pdir_none) -> f (); true
        | (Directive_string f, Pdir_string s) -> f s; true
        | (Directive_int f, Pdir_int n) -> f n; true
        | (Directive_ident f, Pdir_ident lid) -> f lid; true
        | (_, _) ->
            print_string "Wrong type of argument for directive `";
            print_string dir_name; print_string "'"; print_newline();
            false
      with Not_found ->
        print_string "Unknown directive `"; print_string dir_name;
        print_string "'"; print_newline();
        false

(* Reading function *)

external input_scan_line : in_channel -> int = "input_scan_line"

let refill_lexbuf buffer len =
  output_char stdout '#'; flush stdout;
  let n = min len (abs(input_scan_line stdin)) in
  input stdin buffer 0 n

(* Discard everything already in a lexer buffer *)

let empty_lexbuf lb =
  let l = String.length lb.lex_buffer in
  lb.lex_abs_pos <- (-l);
  lb.lex_curr_pos <- l

(* Toplevel initialization. Performed here instead of at the
   beginning of loop() so that user code linked in with cslmktop
   can call directives from Topdirs. *)

let _ =
  Symtable.init_toplevel();
  Compile.init_path();
  Sys.interactive := true

(* The loop *)

let loop() =
  print_string "\tCaml Special Light version ";
  print_string Config.version;
  print_newline(); print_newline();
  (* Add whatever -I options have been specified on the command line,
     but keep the directories that user code linked in with cslmktop
     may have added to load_path. *)
  load_path := "" :: (List.rev !Clflags.include_dirs @ !load_path);
  toplevel_env := Compile.initial_env();
  let lb = Lexing.from_function refill_lexbuf in
  Location.input_name := "";
  Location.input_lexbuf := Some lb;
  Sys.catch_break true;
  while true do
    try
      empty_lexbuf lb;
      execute_phrase (Parse.toplevel_phrase lb); ()
    with
      End_of_file ->
        print_newline(); exit 0
    | Sys.Break ->
        print_string "Interrupted."; print_newline()
    | x ->
        Errors.report_error x
  done
