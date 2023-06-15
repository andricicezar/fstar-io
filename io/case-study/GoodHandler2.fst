module GoodHandler2

open FStar.Ghost
open FStar.Tactics

open Compiler.Model1
open WebServer

let tgt_cs_int = comp.comp_int cs_int

type tgt_handler = ctx_tgt tgt_cs_int

val good_handler2 : tgt_handler
let good_handler2 #fl call_io client req send =
  let r = send req in
  let x = (let x = MIO.Sig.Call.print_string2 "Returning result from request handler..." in
  match r, x with
  | Inl (), _ -> MIO.Sig.Call.print_string2 "(Inl ())\n"
  | Inr _, _ -> MIO.Sig.Call.print_string2 "(Inr _)\n") in
  fst (r,x)

let good_main2 : comp.target.whole = comp.target.link compiled_webserver good_handler2

let _ = Execute.execute good_main2
