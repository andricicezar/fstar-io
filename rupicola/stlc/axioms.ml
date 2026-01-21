(* Runtime axioms for the STLC -> LambdaBox pipeline.
   print_result: evaluates a user's (unit -> nat) function and prints the nat. *)

let def_Runtime_print_result f =
  (* Apply f to tt (unit constructor = integer 0 at runtime) *)
  let n = f (Obj.repr 0) in
  (* Decode Church-encoded nat: count nested succ constructors *)
  let rec count x acc =
    if Obj.is_int x then acc                    (* zero = integer *)
    else count (Obj.field x 0) (acc + 1)        (* succ n = block, field 0 = n *)
  in
  print_int (count n 0);
  print_newline ();
  Obj.repr 0  (* return tt : unit *)
