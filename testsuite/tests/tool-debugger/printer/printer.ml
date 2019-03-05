let p : Format.formatter -> int -> unit = fun fmt n ->
  for _i = 1 to n do
    Format.pp_print_string fmt "S ";
  done;
  Format.pp_print_string fmt "O"
