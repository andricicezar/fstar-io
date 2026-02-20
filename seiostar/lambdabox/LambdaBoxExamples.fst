module LambdaBoxExamples

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

open LambdaBox
open STLC
open STLCToLambdaBox
open RunningExample

let my_modpath : modpath = MPfile ["IO"]

let io_program (main : exp) (agent : exp) : program =
  compile_io_program my_modpath [("main", main); ("agent", agent)] "main" "agent"

// here we link together our main wrapper and the agent
// other agents available: lazy_agent, write_twice_agent, write_mixedup_agent, indirect_agent
let _ =
  assert True
    by (write_term_to_file "io_program.ast" (`(string_of_prog (io_program pt_main write_agent))); trivial ())
