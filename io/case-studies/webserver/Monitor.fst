module Monitor

open FStar.ST
open MIO.Sig

(* This module is essentially parametric over these, but we must fix them here
in order to allocate the reference at module initialization time. An alternative
would be to parametrize the functions by it and pass the reference around. *)

let mst = MonitorParam.mymst
let mi = MonitorParam.mymst_impl

private
val monitor_state : ref mst.typ
let monitor_state = ST.alloc mi.init

let get_state () : St mst.typ = !monitor_state

(* This function is verified to keep the monitor state related to the trace. The
(single) caller to this function comes from OCaml code, since it must actually
have access to the syscalls, and hence the precondition to this function is not
actually enforced. However, it is easy to see that that function (io_call in
MIO_Sig_Call.ml) is correct in that it will always update the state after a
syscall. *)

let update_state
  (c:caller) (op:io_ops) (argz:io_sig.args op) (rez:io_sig.res op argz)
  (h : Ghost.erased trace)
: ST unit
    (requires fun heap0 -> mst.abstracts (Heap.sel heap0 monitor_state) h)
    (ensures fun _ _ heap1 -> mst.abstracts (Heap.sel heap1 monitor_state) (convert_call_to_event c op argz rez :: h))
=
  let s0 = !monitor_state in
  let e = convert_call_to_event c op argz rez in
  let s1 = mi.update s0 e h in
  monitor_state := s1
