module LambdaBoxExamples

open FStar.Tactics.V2
open STLC
open LambdaBox
open STLCToLambdaBox
open LambdaBoxToSexp
open LambdaBoxMeta
open Metaprogram
open ExamplesIO
open RunningExample

let my_modpath : modpath = MPfile ["IO"]

let io_program (main : exp) (agent : exp) : program =
  compile_io_program my_modpath
    [("main", main); ("agent", agent)]
    "main" "agent"

// here we link together our main wrapper and the agent
// other agents available: lazy_agent, write_twice_agent, write_mixedup_agent, indirect_agent
let _ =
  assert True
    by (write_term_to_file "io_program.ast" (`(red_prog (io_program pt_main write_agent))); trivial ())
