open Examples_Intro

let _ =
  let r = whole_triv () in
  print_string ("triv returned " ^ string_of_int (Z.to_int r) ^ "\n")

let _ =
  let r = whole_adv () in
  print_string ("adv returned " ^ string_of_int (Z.to_int r) ^ "\n")
