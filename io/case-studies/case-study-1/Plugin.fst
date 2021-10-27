module Plugin

open Free.IO 
open DM.MIO
open Common
open Model
open Shared

val plugin : ctx_t i
let plugin (client:file_descr) = 
  match unsafe_cmd Read (client, 250uy) with
  | Inl (msg, size) ->
    if UInt8.lt size 1uy then ()
    else (
      let _ = unsafe_cmd Write (client, msg) in
      ())
  | Inr _ -> ()
