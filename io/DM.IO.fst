module DM.IO

open FStar.Tactics
open ExtraTactics

open Common
open Free
open DMFree
open Hist
open Free.IO.Sig
open Free.IO.Call

(** The postcondition for an io computation is defined over the
result (type: a) and local trace (type: trace).
The local trace represents the events that happend during the
computation. Local trace is in chronological order.

We also have the history (type: trace) which represents the
events that happend until the beggining of the io computation.
The history is  in reverse chronology order.

At the end of an io computation, the local trace is appended
in reverse order to the history. **)

unfold let iio_wps (cmd:iio_cmds) (arg:iio_sig.args cmd) : hist #event (iio_sig.res cmd arg) = fun p h ->
  match cmd with
  | GetTrace -> p [] h
  | _ -> io_pre cmd arg h /\ (forall (r:iio_sig.res cmd arg). p [convert_call_to_event cmd arg r] r)

unfold let io_wps (cmd:io_cmds) (arg:io_sig.args cmd) : hist #event (io_sig.res cmd arg) =
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
  IOwp (a:Type) (wp : hist #event a) 
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

effect IOPi
  (a:Type)
  (pi : monitorable_prop)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  IO a
    (requires pre)
    (ensures (fun h r lt -> 
      enforced_locally pi h lt /\
      post h r lt))

let static_cmd
  (cmd : io_cmds)
  (pi : monitorable_prop)
  (arg : io_sig.args cmd) :
  IOPi (io_sig.res cmd arg) pi
    (requires (fun h -> io_pre cmd arg h /\ pi h (| cmd, arg |)))
    (ensures (fun h r lt ->
        lt == [convert_call_to_event cmd arg r])) =
  IOwp?.reflect (io_call cmd arg)
