open Examples_Guess
open Z

let rec player l r f =
  print_string ("player " ^ string_of_int (Z.to_int l) ^ " " ^ string_of_int (Z.to_int r) ^ "\n");
  if l > r then failwith "no";
  let mid = (l+r) / Z.of_int 2 in
  match f mid with
  | EQ -> mid
  | LT -> player (mid + Z.of_int 1) r f
  | GT -> player l (mid - Z.of_int 1) f

let () =
  let (res, guesses) =
    play_guess
    (Prims.parse_int "0")
    (Prims.parse_int "1")
    (Prims.parse_int "100")
    player
  in
  print_string ("res = " ^ string_of_bool res ^ "\n");
  print_string ("guesses = " ^ string_of_int (Z.to_int guesses) ^ "\n");
  ()
