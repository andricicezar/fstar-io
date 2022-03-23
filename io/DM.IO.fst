module DM.IO

open FStar.Tactics
open ExtraTactics

open Common
open DMFree
open IO.Sig
open IO.Sig.Call

(** The postcondition for an io computation is defined over the
result (type: a) and local trace (type: trace).
The local trace represents the events that happend during the
computation. Local trace is in chronological order.

We also have the history (type: trace) which represents the
events that happend until the beggining of the io computation.
The history is  in reverse chronology order.

At the end of an io computation, the local trace is appended
in reverse order to the history. **)

unfold let io_wps (cmd:io_cmds) (arg:io_sig.args cmd) : hist (io_sig.res cmd arg) =
  iio_wps cmd arg

let dm_io_theta #a = theta #a #io_cmds #io_sig #event io_wps
  
let dm_io = dm io_cmds io_sig event io_wps
let dm_io_return = dm_return io_cmds io_sig event io_wps
let dm_io_bind = dm_bind io_cmds io_sig event io_wps
let dm_io_subcomp = dm_subcomp io_cmds io_sig event io_wps
let dm_io_if_then_else = dm_if_then_else io_cmds io_sig event io_wps
let lift_pure_dm_io = lift_pure_dm io_cmds io_sig event io_wps

total
reifiable
reflectable
effect {
  IOwp (a:Type) (wp : hist a) 
  with {
       repr       = dm_io
     ; return     = dm_io_return
     ; bind       = dm_io_bind 
     ; subcomp    = dm_io_subcomp
     ; if_then_else = dm_io_if_then_else
     }
}

sub_effect PURE ~> IOwp = lift_pure_dm_io

effect IO
  (a:Type)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  IOwp a 
    (fun (p:hist_post a) (h:trace) -> pre h /\ (forall lt (r:a). post h r lt ==> p lt r)) 

let static_cmd
  (cmd : io_cmds)
  (arg : io_sig.args cmd) :
  IO (io_resm cmd)
    (requires (fun h -> io_pre cmd arg h))
    (ensures (fun h (r:io_sig.res cmd arg) lt ->
        lt == [convert_call_to_event cmd arg r])) =
  IOwp?.reflect (io_call cmd arg)
