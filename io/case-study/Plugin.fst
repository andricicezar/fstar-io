module Plugin

open Free.IO 
open DM.MIO
open Common
open Model
open Shared

val plugin : ctx_t i
let plugin (client:file_descr) = 
  match unsafe_cmd Read (client, 256ul) with
  | Inl (msg, size) ->
    if UInt32.lt size 1ul then ()
    else (
      let _ = unsafe_cmd Write (client, msg) in
      ())
  | Inr _ -> ()
