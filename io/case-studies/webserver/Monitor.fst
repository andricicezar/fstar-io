module Monitor

open FStar.ST
open MIO.Sig
open Utils

private
val monitor_state : ref mymst.typ
let monitor_state = ST.alloc my_init_cst

let get_state () : St mymst.typ = !monitor_state

let update_state (c:caller) (op:io_ops) (argz:io_sig.args op) (rez:io_sig.res op argz) : St unit =
  let s0 = get_state () in
  let e = convert_call_to_event c op argz rez in
  let s1 = my_update_cst s0 e in
  monitor_state := s1
