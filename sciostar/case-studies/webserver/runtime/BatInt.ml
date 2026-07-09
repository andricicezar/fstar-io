(* Minimal stand-in for batteries' BatInt (not available in this
   environment): F*'s app runtime only uses pow. *)

let pow base exp =
  if exp < 0 then invalid_arg "pow";
  let rec aux acc b e =
    if e = 0 then acc
    else if e land 1 = 1 then aux (acc * b) (b * b) (e asr 1)
    else aux acc (b * b) (e asr 1)
  in
  aux 1 base exp
