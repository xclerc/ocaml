let rec f =
  let r = ref 33 in
  incr r;
  let b = (g, !r) in
  print_endline "f";
  let rec u =
    let ru = !r in
    (fun x -> ru, v x)
  and v =
    incr r;
    let rv = !r in
    (fun x -> ignore b; rv, g x)
  and w = [1;2;3]
  in
  (u, v, w)
and g =
  print_endline "g";
  (fun x -> ignore f; x + 1)

let () =
  let (u, v, w) = f in
  let a, (b, c) = u 3 in
  print_int a;
  print_newline ();
  print_int b;
  print_newline ();
  print_int c;
  print_newline ();
  print_int (List.length w);
  print_newline ()
