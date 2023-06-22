module Monitor

open FStar.ST
open MIO.Sig
open Utils

private
val monitor_state : ref mymst.cst
let monitor_state = ST.alloc my_init_cst

let get_state () : St mymst.cst = !monitor_state

let update_state caller (cmd:io_cmds) (argz:io_sig.args cmd) (rez:io_sig.res cmd argz) : St unit =
  let s0 = get_state () in
  let e = convert_call_to_event caller cmd argz rez in
  let s1 = my_update_cst s0 e in
  monitor_state := s1
