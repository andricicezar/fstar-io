let () =
  let r = Examples_Autograder.test1 () in
  match r with
  | None -> print_string "None\n"
  | Some i -> print_string ("Some " ^ string_of_int (Z.to_int i) ^ "\n")
