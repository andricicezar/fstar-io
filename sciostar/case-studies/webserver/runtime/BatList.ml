(* Minimal stand-in for batteries' BatList (not available in this
   environment), implementing just what F*'s app runtime uses, on top of
   the OCaml stdlib. *)

include List

let split_at n l =
  let rec aux acc n l =
    match n, l with
    | 0, l -> List.rev acc, l
    | _, [] -> invalid_arg "split_at"
    | n, x :: xs -> aux (x :: acc) (n - 1) xs
  in
  aux [] n l

let subset cmp l1 l2 =
  List.for_all (fun x -> List.exists (fun y -> cmp x y = 0) l2) l1
