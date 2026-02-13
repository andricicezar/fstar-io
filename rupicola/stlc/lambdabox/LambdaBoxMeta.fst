module LambdaBoxMeta

open FStar.Tactics.V2

let write_file (filename : string) (content : string) : Tac unit =
  let _ = launch_process "sh" ["-c"; "cat > '" ^ filename ^ "'"] content in
  ()

let write_term_to_file (filename : string) (t : term) : Tac unit =
  let g = top_env () in
  let t' = norm_term_env g [delta; iota; zeta_full; primops; unascribe] t in
  match inspect t' with
  | Tv_Const (C_String s) -> write_file filename s
  | _ -> fail "write_term_to_file: term did not reduce to a string constant"
