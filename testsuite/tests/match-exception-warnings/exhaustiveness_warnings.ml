(** Test exhaustiveness.

    match clauses should continue to give warnings about inexhaustive
    value-matching clauses when there is an exception-matching clause
 *)

let test_match_exhaustiveness f =
    match f None with
    | exception e -> ()
    | Some false -> ()
    | None -> ()
;;
