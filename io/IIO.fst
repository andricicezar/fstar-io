module IIO

open FStar.Tactics
open ExtraTactics
open FStar.Calc

open IO.Sig
open IO.Sig.Call
open DMFree

(** The postcondition for an io computation is defined over the
result (type: a) and local trace (type: trace).
The local trace represents the events that happend during the
computation. Local trace is in chronological order.

We also have the history (type: trace) which represents the
events that happend until the beggining of the io computation.
The history is  in reverse chronology order.

At the end of an io computation, the local trace is appended
in reverse order to the history. **)
let dm_iio_theta #a = theta #a #iio_cmds #iio_sig #event iio_wps
  
type dm_iio = dm iio_cmds iio_sig event iio_wps
let dm_iio_return (a:Type) (x:a) : dm_iio a (hist_return x) =
  dm_return iio_cmds iio_sig event iio_wps a x

val dm_iio_bind  : 
  a: Type ->
  b: Type ->
  wp_v: hist a ->
  wp_f: (_: a -> hist b) ->
  v: dm_iio a wp_v ->
  f: (x: a -> dm_iio b (wp_f x)) ->
  Tot (dm_iio b (hist_bind wp_v wp_f))
let dm_iio_bind a b wp_v wp_f v f = dm_bind iio_cmds iio_sig event iio_wps a b wp_v wp_f v f

val dm_iio_subcomp : 
  a: Type ->
  wp1: hist a ->
  wp2: hist a ->
  f: dm_iio a wp1 ->
  Pure (dm_iio a wp2) (hist_ord wp2 wp1) (fun _ -> True)
let dm_iio_subcomp a wp1 wp2 f = dm_subcomp iio_cmds iio_sig event iio_wps a wp1 wp2 f

let dm_iio_if_then_else a wp1 wp2 f g b = dm_if_then_else iio_cmds iio_sig event iio_wps a wp1 wp2 f g b

#set-options "--print_universes"

val lift_pure_dm_iio :
  a: Type ->
  w: pure_wp a ->
  f: (eqtype_as_type unit -> PURE a w) ->
  Tot (dm_iio a (wp_lift_pure_hist w))
let lift_pure_dm_iio = lift_pure_dm iio_cmds iio_sig event iio_wps


[@@allow_informative_binders]
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

effect IIO
  (a:Type)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  IIOwp a (to_hist pre post) 

let static_cmd
  (cmd : io_cmds)
  (arg : io_sig.args cmd) :
  IIO (io_resm cmd)
    (requires (fun h -> io_pre cmd arg h))
    (ensures (fun h (r:io_sig.res cmd arg) lt ->
        lt == [convert_call_to_event cmd arg r])) =
  IIOwp?.reflect (iio_call cmd arg)

let get_trace () : IIOwp trace (fun p h -> forall lt. lt == [] ==> p lt h) =
  IIOwp?.reflect (iio_call GetTrace ())
