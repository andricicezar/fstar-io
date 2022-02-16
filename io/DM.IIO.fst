module DM.IIO

open FStar.Tactics
open ExtraTactics
open FStar.Calc

open Common
open Free
open DMFree
open Free.IO.Sig
open Free.IO.Call
open Hist

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

let theta #a = theta #a #iio_cmds #iio_sig #event iio_wps
  
let dm_iio = dm iio_cmds iio_sig event iio_wps
let dm_iio_return = dm_return iio_cmds iio_sig event iio_wps
let dm_iio_bind = dm_bind iio_cmds iio_sig event iio_wps
let dm_iio_subcomp = dm_subcomp iio_cmds iio_sig event iio_wps
let dm_iio_if_then_else = dm_if_then_else iio_cmds iio_sig event iio_wps
let lift_pure_dm_iio = lift_pure_dm iio_cmds iio_sig event iio_wps

total
reifiable
reflectable
effect {
  IIOwp (a:Type) (wp : hist #event a) 
  with {
       repr       = dm_iio
     ; return     = dm_iio_return
     ; bind       = dm_iio_bind 
     ; subcomp    = dm_iio_subcomp
     ; if_then_else = dm_iio_if_then_else
     }
}

sub_effect PURE ~> IIOwp = lift_pure_dm_iio

(** This is a identity function, and we need it because
F* does not have depth subtyping on inductives. **)
let rec cast_io_iio #a (x:io a) : iio a =
  match x with
  | Return z -> Return z
  | Call (cmd:io_cmds) args fnc ->
     Call cmd args (fun res ->
       cast_io_iio (fnc res))
  | PartialCall pre fnc ->
     PartialCall pre (fun res ->
       cast_io_iio (fnc res))

(**
let lift_iowp_iiowp (a:Type) (wp:hist a) (f:DM.IO.dm_io a wp) :
  Tot (dm_iio a wp) =
   // io_interp_to_iio_interp (f h p) h p;
  cast_io_iio f

sub_effect IOwp ~> IIOwp = lift_iowp_iiowp
**)

let get_trace () : IIOwp trace
  (fun p h -> forall lt. lt == [] ==>  p lt h) =
  IIOwp?.reflect (iio_call GetTrace ())

let iio_post
  (#a:Type)
  (pi : monitorable_prop)
  (h:trace)
  (result:a)
  (local_trace:trace) :
  Tot bool =
  enforced_locally pi h local_trace

effect IIOpi
  (a:Type)
  (pi : monitorable_prop)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  IIOwp a
    (fun p h ->
      pre h /\
      (forall r lt. (iio_post pi h r lt /\ post h r lt) ==> p lt r))
