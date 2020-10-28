(* TEST
   include ocamlcommon
   include ocamlmiddleend
   * bytecode
*)

let () = Clflags.flambda_invariant_checks := true

let () =
  let dummy = "compilation_unit" in
  Compilation_unit.set_current
    (Compilation_unit.create
       (Ident.create_persistent dummy)
       (Linkage_name.create dummy))

module Coercion : sig
  include Aliases.Coercion
  val make : char -> t
end = struct
  type t = string
  let make c = String.make 1 c
  let equal = String.equal
  let change_case ch =
    if Char.equal ch (Char.lowercase_ascii ch) then
      Char.uppercase_ascii ch
    else
      Char.lowercase_ascii ch
  let simplify s =
    let len = String.length s in
    let buff = Buffer.create len in
    let i = ref 0 in
    while !i < len do
      if succ !i < len && Char.equal s.[!i] (change_case s.[succ !i]) then begin
        incr i;
        incr i;
      end else begin
        Buffer.add_char buff s.[!i];
        incr i;
      end
    done;
    Buffer.contents buff
  let inverse c =
    let len = String.length c in
    let res = String.init len (fun i -> change_case c.[len - i - 1]) in
    simplify res
  let id = ""
  let is_id c = equal id c
  let compose c ~newer = simplify (c ^ newer)
  let print ppf c = Format.fprintf ppf "coercion:%S" c
end

module Element : sig
  include Aliases.Element
  val make : string -> t
end = struct
  type t = string
  let make x = x
  let name n =
    Name.pattern_match
      n
      ~var:(fun v -> Variable.name v)
      ~symbol:(fun _ -> assert false)
  let without_coercion e = e
  let pattern_match _ ~name:_ ~const:_ = assert false
  let print ppf e = Format.fprintf ppf "element:%S" e
  include Identifiable.Make (struct
      type nonrec t = t
      let compare = String.compare
      let equal = String.equal
      let hash = Hashtbl.hash
      let output _ _ = assert false
      let print = print
    end)
end

module Export : sig
  include Aliases.Export with type e = Element.t
end = struct
  type e = Element.t
  type t = unit
  let add _ _ = assert false
  let empty = ()
  let to_ids_for_export _ = assert false
  module Import_map = struct
    type t
    let of_import_map _ = assert false
    let simple _ _ = assert false
  end
end

module Aliases = Aliases.Make (Coercion) (Element) (Export)

let next_time : unit -> Binding_time.With_name_mode.t =
  let next = ref Binding_time.earliest_var in
  fun () ->
    let time = !next in
    next := Binding_time.succ time;
    Binding_time.With_name_mode.create time Name_mode.normal

let add_alias
      ppf
      aliases
      ~element1
      ~binding_time_and_mode1
      ~coerce_from_element2_to_element1
      ~element2
      ~binding_time_and_mode2 =
  let { Aliases.t; canonical_element; alias_of; coerce_alias_of_to_canonical_element; } =
    Aliases.add
      aliases
      ~element1
      ~binding_time_and_mode1
      ~coerce_from_element2_to_element1
      ~element2
      ~binding_time_and_mode2
  in
  Format.fprintf ppf "[added] %a <--[%a]-- %a@."
    Element.print canonical_element
    Coercion.print coerce_alias_of_to_canonical_element
    Element.print alias_of;
  t

(* CR xclerc for xclerc: remove the `expect` parameter.
   (It currently allows one to use this module without relying upon ocamltest.) *)
let test msg ~f ~expect =
  let buff = Buffer.create 1024 in
  let ppf = Format.formatter_of_buffer buff in
  print_string "*** ";
  print_endline msg;
  f ppf;
  Format.pp_print_flush ppf ();
  let got = Buffer.contents buff in
  if String.equal got expect then begin
    print_endline got;
    print_newline ();
  end else begin
    prerr_endline "*** error, expected:";
    prerr_endline expect;
    prerr_endline "*** but got:";
    prerr_endline got;
    assert false
  end

let () = test "empty" ~f:(fun ppf ->
  let aliases = Aliases.empty in
  Aliases.print ppf aliases)
  ~expect:{|((canonical_elements {}) (aliases_of_canonical_elements {})
 (binding_times_and_modes {}))|}

let () = test "single alias" ~f:(fun ppf ->
  let aliases = Aliases.empty in
  let t_x = next_time () in
  let t_y = next_time () in
  let x = Element.make "x" in
  let y = Element.make "y" in
  (* x <--[f]-- y *)
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:x
      ~binding_time_and_mode1:t_x
      ~coerce_from_element2_to_element1:(Coercion.make 'f')
      ~element2:y
      ~binding_time_and_mode2:t_y
  in
  Aliases.print ppf aliases)
  ~expect:{|[added] element:"x" <--[coercion:"f"]-- element:"y"
((canonical_elements {(element:"y" element:"x" (coercion:"f"))})
 (aliases_of_canonical_elements
  {(element:"x" {(Normal {(element:"y" coercion:"f")})})})
 (binding_times_and_modes
  {(element:"x" (bound at time 3 Normal))
   (element:"y" (bound at time 4 Normal))}))|}

let () = test "single alias (inverse)" ~f:(fun ppf ->
  let aliases = Aliases.empty in
  let t_y = next_time () in
  let t_x = next_time () in
  let x = Element.make "x" in
  let y = Element.make "y" in
  (* x <--[f]-- y
     ~>
     y <--[F]-- x *)
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:x
      ~binding_time_and_mode1:t_x
      ~coerce_from_element2_to_element1:(Coercion.make 'f')
      ~element2:y
      ~binding_time_and_mode2:t_y
  in
  Aliases.print ppf aliases)
  ~expect:{|[added] element:"y" <--[coercion:"F"]-- element:"x"
((canonical_elements {(element:"x" element:"y" (coercion:"F"))})
 (aliases_of_canonical_elements
  {(element:"y" {(Normal {(element:"x" coercion:"F")})})})
 (binding_times_and_modes
  {(element:"x" (bound at time 6 Normal))
   (element:"y" (bound at time 5 Normal))}))|}

let () = test "two aliases (independent)" ~f:(fun ppf ->
  let aliases = Aliases.empty in
  let t_x = next_time () in
  let t_y = next_time () in
  let t_z = next_time () in
  let x = Element.make "x" in
  let y = Element.make "y" in
  let z = Element.make "z" in
  (* x <--[f]-- y
     +
     x <--[g]-- z
     ~>
     x <--[f]-- y
     ^--[g]-- z *)
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:x
      ~binding_time_and_mode1:t_x
      ~coerce_from_element2_to_element1:(Coercion.make 'f')
      ~element2:y
      ~binding_time_and_mode2:t_y
  in
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:x
      ~binding_time_and_mode1:t_x
      ~coerce_from_element2_to_element1:(Coercion.make 'g')
      ~element2:z
      ~binding_time_and_mode2:t_z
  in
  Aliases.print ppf aliases)
  ~expect:{|[added] element:"x" <--[coercion:"f"]-- element:"y"
[added] element:"x" <--[coercion:"g"]-- element:"z"
((canonical_elements
  {(element:"y" element:"x" (coercion:"f"))
   (element:"z" element:"x" (coercion:"g"))})
 (aliases_of_canonical_elements
  {(element:"x"
    {(Normal {(element:"y" coercion:"f") (element:"z" coercion:"g")})})})
 (binding_times_and_modes
  {(element:"x" (bound at time 7 Normal))
   (element:"y" (bound at time 8 Normal))
   (element:"z" (bound at time 9 Normal))}))|}

let () = test "two aliases (simple chain)" ~f:(fun ppf ->
  let aliases = Aliases.empty in
  let t_x = next_time () in
  let t_y = next_time () in
  let t_z = next_time () in
  let x = Element.make "x" in
  let y = Element.make "y" in
  let z = Element.make "z" in
  (* x <--[f]-- y
     +
     y <--[g]-- z
     ~>
     x <--[f]-- y
     ^--[gf]-- z *)
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:x
      ~binding_time_and_mode1:t_x
      ~coerce_from_element2_to_element1:(Coercion.make 'f')
      ~element2:y
      ~binding_time_and_mode2:t_y
  in
   let aliases =
    add_alias
      ppf
      aliases
      ~element1:y
      ~binding_time_and_mode1:t_y
      ~coerce_from_element2_to_element1:(Coercion.make 'g')
      ~element2:z
      ~binding_time_and_mode2:t_z
  in
  Aliases.print ppf aliases)
  ~expect:{|[added] element:"x" <--[coercion:"f"]-- element:"y"
[added] element:"x" <--[coercion:"gf"]-- element:"z"
((canonical_elements
  {(element:"y" element:"x" (coercion:"f"))
   (element:"z" element:"x" (coercion:"gf"))})
 (aliases_of_canonical_elements
  {(element:"x"
    {(Normal {(element:"y" coercion:"f") (element:"z" coercion:"gf")})})})
 (binding_times_and_modes
  {(element:"x" (bound at time 10 Normal))
   (element:"y" (bound at time 11 Normal))
   (element:"z" (bound at time 12 Normal))}))|}

let () = test "two aliases (two inverses)" ~f:(fun ppf ->
  let aliases = Aliases.empty in
  let t_z = next_time () in
  let t_x = next_time () in
  let t_y = next_time () in
  let x = Element.make "x" in
  let y = Element.make "y" in
  let z = Element.make "z" in
  (* x <--[f]-- y
     +
     y <--[g]-- z
     ~>
     z <--[FG]-- x
     ^--[G]-- y *)
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:x
      ~binding_time_and_mode1:t_x
      ~coerce_from_element2_to_element1:(Coercion.make 'f')
      ~element2:y
      ~binding_time_and_mode2:t_y
  in
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:y
      ~binding_time_and_mode1:t_y
      ~coerce_from_element2_to_element1:(Coercion.make 'g')
      ~element2:z
      ~binding_time_and_mode2:t_z
  in
  Aliases.print ppf aliases)
  ~expect:{|[added] element:"x" <--[coercion:"f"]-- element:"y"
[added] element:"z" <--[coercion:"FG"]-- element:"x"
((canonical_elements
  {(element:"x" element:"z" (coercion:"FG"))
   (element:"y" element:"z" (coercion:"G"))})
 (aliases_of_canonical_elements
  {(element:"z"
    {(Normal {(element:"x" coercion:"FG") (element:"y" coercion:"G")})})})
 (binding_times_and_modes
  {(element:"x" (bound at time 14 Normal))
   (element:"y" (bound at time 15 Normal))
   (element:"z" (bound at time 13 Normal))}))|}

let () = test "two aliases (one inverse)" ~f:(fun ppf ->
  let aliases = Aliases.empty in
  let t_z = next_time () in
  let t_x = next_time () in
  let t_y = next_time () in
  let x = Element.make "x" in
  let y = Element.make "y" in
  let z = Element.make "z" in
  (* x <--[f]-- y
     +
     z <--[g]-- y
     ~>
     z <--[Fg]-- x
     ^--[g]-- y *)
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:x
      ~binding_time_and_mode1:t_x
      ~coerce_from_element2_to_element1:(Coercion.make 'f')
      ~element2:y
      ~binding_time_and_mode2:t_y
  in
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:z
      ~binding_time_and_mode1:t_z
      ~coerce_from_element2_to_element1:(Coercion.make 'g')
      ~element2:y
      ~binding_time_and_mode2:t_y
  in
  Aliases.print ppf aliases)
  ~expect:{|[added] element:"x" <--[coercion:"f"]-- element:"y"
[added] element:"z" <--[coercion:"Fg"]-- element:"x"
((canonical_elements
  {(element:"x" element:"z" (coercion:"Fg"))
   (element:"y" element:"z" (coercion:"g"))})
 (aliases_of_canonical_elements
  {(element:"z"
    {(Normal {(element:"x" coercion:"Fg") (element:"y" coercion:"g")})})})
 (binding_times_and_modes
  {(element:"x" (bound at time 17 Normal))
   (element:"y" (bound at time 18 Normal))
   (element:"z" (bound at time 16 Normal))}))|}

let () = test "two aliases (one inverse)" ~f:(fun ppf ->
  let aliases = Aliases.empty in
  let t_x = next_time () in
  let t_y = next_time () in
  let t_z = next_time () in
  let x = Element.make "x" in
  let y = Element.make "y" in
  let z = Element.make "z" in
  (* x <--[f]-- y
     +
     z <--[g]-- y
     ~>
     x <--[f]-- y
     ^--[Gf]-- z *)
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:x
      ~binding_time_and_mode1:t_x
      ~coerce_from_element2_to_element1:(Coercion.make 'f')
      ~element2:y
      ~binding_time_and_mode2:t_y
  in
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:z
      ~binding_time_and_mode1:t_z
      ~coerce_from_element2_to_element1:(Coercion.make 'g')
      ~element2:y
      ~binding_time_and_mode2:t_y
  in
  Aliases.print ppf aliases)
  ~expect:{|[added] element:"x" <--[coercion:"f"]-- element:"y"
[added] element:"x" <--[coercion:"Gf"]-- element:"z"
((canonical_elements
  {(element:"y" element:"x" (coercion:"f"))
   (element:"z" element:"x" (coercion:"Gf"))})
 (aliases_of_canonical_elements
  {(element:"x"
    {(Normal {(element:"y" coercion:"f") (element:"z" coercion:"Gf")})})})
 (binding_times_and_modes
  {(element:"x" (bound at time 19 Normal))
   (element:"y" (bound at time 20 Normal))
   (element:"z" (bound at time 21 Normal))}))|}

let () = test "three aliases (one inverse)" ~f:(fun ppf ->
  let aliases = Aliases.empty in
  let t_x = next_time () in
  let t_y = next_time () in
  let t_z = next_time () in
  let t_t = next_time () in
  let x = Element.make "x" in
  let y = Element.make "y" in
  let z = Element.make "z" in
  let t = Element.make "t" in
  (* x <--[f]-- y
     +
     z <--[g]-- t
     +
     y <--[h]-- t
     ~>
     x <--[f]-- y
     ^^--[Ghf]-- z
      \--[hf]-- t *)
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:x
      ~binding_time_and_mode1:t_x
      ~coerce_from_element2_to_element1:(Coercion.make 'f')
      ~element2:y
      ~binding_time_and_mode2:t_y
  in
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:z
      ~binding_time_and_mode1:t_z
      ~coerce_from_element2_to_element1:(Coercion.make 'g')
      ~element2:t
      ~binding_time_and_mode2:t_t
  in
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:y
      ~binding_time_and_mode1:t_y
      ~coerce_from_element2_to_element1:(Coercion.make 'h')
      ~element2:t
      ~binding_time_and_mode2:t_t
  in
  Aliases.print ppf aliases)
  ~expect:{|[added] element:"x" <--[coercion:"f"]-- element:"y"
[added] element:"z" <--[coercion:"g"]-- element:"t"
[added] element:"x" <--[coercion:"Ghf"]-- element:"z"
((canonical_elements
  {(element:"t" element:"x" (coercion:"hf"))
   (element:"y" element:"x" (coercion:"f"))
   (element:"z" element:"x" (coercion:"Ghf"))})
 (aliases_of_canonical_elements
  {(element:"x"
    {(Normal
      {(element:"t" coercion:"hf") (element:"y" coercion:"f")
       (element:"z" coercion:"Ghf")})})})
 (binding_times_and_modes
  {(element:"t" (bound at time 25 Normal))
   (element:"x" (bound at time 22 Normal))
   (element:"y" (bound at time 23 Normal))
   (element:"z" (bound at time 24 Normal))}))|}

let () = test "three aliases (two inverses)" ~f:(fun ppf ->
  let aliases = Aliases.empty in
  let t_z = next_time () in
  let t_x = next_time () in
  let t_y = next_time () in
  let t_t = next_time () in
  let x = Element.make "x" in
  let y = Element.make "y" in
  let z = Element.make "z" in
  let t = Element.make "t" in
  (* x <--[f]-- y
     +
     z <--[g]-- t
     +
     y <--[h]-- t
     ~>
     z <--[FHg]-- x
     ^^--[Hg]-- y
     \--[g]-- t *)
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:x
      ~binding_time_and_mode1:t_x
      ~coerce_from_element2_to_element1:(Coercion.make 'f')
      ~element2:y
      ~binding_time_and_mode2:t_y
  in
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:z
      ~binding_time_and_mode1:t_z
      ~coerce_from_element2_to_element1:(Coercion.make 'g')
      ~element2:t
      ~binding_time_and_mode2:t_t
  in
  let aliases =
    add_alias
      ppf
      aliases
      ~element1:y
      ~binding_time_and_mode1:t_y
      ~coerce_from_element2_to_element1:(Coercion.make 'h')
      ~element2:t
      ~binding_time_and_mode2:t_t
  in
  Aliases.print ppf aliases)
  ~expect:{|[added] element:"x" <--[coercion:"f"]-- element:"y"
[added] element:"z" <--[coercion:"g"]-- element:"t"
[added] element:"z" <--[coercion:"FHg"]-- element:"x"
((canonical_elements
  {(element:"t" element:"z" (coercion:"g"))
   (element:"x" element:"z" (coercion:"FHg"))
   (element:"y" element:"z" (coercion:"Hg"))})
 (aliases_of_canonical_elements
  {(element:"z"
    {(Normal
      {(element:"t" coercion:"g") (element:"x" coercion:"FHg")
       (element:"y" coercion:"Hg")})})})
 (binding_times_and_modes
  {(element:"t" (bound at time 29 Normal))
   (element:"x" (bound at time 27 Normal))
   (element:"y" (bound at time 28 Normal))
   (element:"z" (bound at time 26 Normal))}))|}

let () = print_endline "OK."
