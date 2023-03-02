module Monitor

open FStar.ST
open MIO.Sig

private
val h : ref trace
let h = ST.alloc []

let get_trace () : St trace = !h

let update_trace (caller:bool) (cmd:io_cmds) (argz:io_sig.args cmd) (rez:io_sig.res cmd argz) : St unit =
  h := (convert_call_to_event caller cmd argz rez) :: !h
