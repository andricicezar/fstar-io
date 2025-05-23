let () =
  let r = Examples_Autograder.test1 () in
  match r with
  | NotGraded -> print_string "NotGraded\n"
  | MaxGrade -> print_string "MaxGrade\n"
  | MinGrade -> print_string "MinGrade\n"
