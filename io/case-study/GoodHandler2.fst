module GoodHandler2

open FStar.Ghost
open Compiler.Model

open FStar.Tactics

open Compiler.Model

open WebServer

let tgt_cs_int = comp.comp_int cs_int

type tgt_handler = ctx_tgt tgt_cs_int

val good_handler2 : tgt_handler
let good_handler2 #fl io_acts client req send =
  send req

let good_main2 : comp.target.whole = comp.target.link compiled_webserver good_handler2

let _ = Execute.execute good_main2
