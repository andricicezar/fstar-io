module IO

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
let dm_io_return (a:Type) (x:a) : dm_io a (hist_return x) =
  dm_return io_cmds io_sig event io_wps a x

val dm_io_bind  : 
  a: Type u#a ->
  b: Type u#b ->
  wp_v: Hist.hist a ->
  wp_f: (_: a -> Prims.Tot (Hist.hist b)) ->
  v: dm_io a wp_v ->
  f: (x: a -> Prims.Tot (dm_io b (wp_f x))) ->
  Tot (dm_io b (hist_bind wp_v wp_f))
let dm_io_bind a b wp_v wp_f v f = dm_bind io_cmds io_sig event io_wps a b wp_v wp_f v f

val dm_io_subcomp : 
  a: Type ->
  wp1: hist a ->
  wp2: hist a ->
  f: dm_io a wp1 ->
  Pure (dm_io a wp2) (hist_ord wp2 wp1) (fun _ -> True)
let dm_io_subcomp a wp1 wp2 f = dm_subcomp io_cmds io_sig event io_wps a wp1 wp2 f

let dm_io_if_then_else a wp1 wp2 f g b = dm_if_then_else io_cmds io_sig event io_wps a wp1 wp2 f g b

val lift_pure_dm_io :
  a: Type u#a ->
  w: pure_wp a ->
  f: (_: eqtype_as_type unit -> Prims.PURE a w) ->
  Tot (dm_io a (wp_lift_pure_hist w))
let lift_pure_dm_io a w f = lift_pure_dm io_cmds io_sig event io_wps a w f

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
  IOwp a (to_hist pre post)

let static_cmd
  (cmd : io_cmds)
  (arg : io_sig.args cmd) :
  IO (io_resm cmd)
    (requires (fun h -> io_pre cmd arg h))
    (ensures (fun h (r:io_sig.res cmd arg) lt ->
        lt == [convert_call_to_event cmd arg r])) =
  IOwp?.reflect (io_call cmd arg)
