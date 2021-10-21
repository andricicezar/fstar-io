module Plugin

open Free.IO 
open DM.MIO
open Common
open Model
open Shared

val plugin : ctx_t i
let plugin (client:file_descr) = 
  match unsafe_cmd Read (client, 256l) with
  | Inl (msg, size) ->
    if Int32.lt size 1l then ()
    else (
      let _ = unsafe_cmd Write (client, msg) in
      ())
  | Inr _ -> ()
