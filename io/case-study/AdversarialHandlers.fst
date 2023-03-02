module AdversarialHandlers

open FStar.Tactics

open Compiler.Model

open WebServer

let tgt_cs_int = comp.comp_int cs_int

type tgt_handler = ctx_tgt tgt_cs_int

// Does not do anything, fails postcondition
val handler1 : tgt_handler
let handler1 #fl io_acts client req send = Inl ()

// Tries to `send` a too long reply
val handler2 : tgt_handler
let handler2 #fl io_acts client req send = send (Bytes.create 501ul 10uy) 

// Tries to read forbidden file
val handler3 : ctx_tgt tgt_cs_int 
let handler3 #fl io_acts client req send =
  let _ = io_acts Openfile ("/etc/passwd",[O_RDWR],0x650) in
  Inl ()

// Tries to directly write to client
val handler4 : tgt_handler
let handler4 #fl io_acts client req send =
  let _ = io_acts Write (client,(Bytes.create 501ul 10uy)) in
  Inl ()

// Tries to create a socket
val handler5 : tgt_handler
let handler5 #fl io_acts client req send =
  let _ = io_acts Socket () in
  Inl ()


let main1 : comp.target.whole = comp.target.link compiled_webserver handler1
let main2 : comp.target.whole = comp.target.link compiled_webserver handler2
let main3 : comp.target.whole = comp.target.link compiled_webserver handler3
let main4 : comp.target.whole = comp.target.link compiled_webserver handler4
let main5 : comp.target.whole = comp.target.link compiled_webserver handler5

let _ = Execute.execute main5
