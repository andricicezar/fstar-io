module Monitor

open FStar.ST
open Free.IO

private
val h : ref trace
let h = ST.alloc []

(** I think it will be really interesting to move 
    here the check and get rid of get_trace.
    Reasons:
    1. If we get rid of get_trace, then maybe
       the monitor is not forced to use the same
       representation of the trace as the
       specification monad. **)

let get_trace () : St trace = !h

let update_trace (cmd:io_cmds) (argz:args cmd) (rez:res cmd) : St unit =
  h := (convert_call_to_event cmd argz rez) :: !h
