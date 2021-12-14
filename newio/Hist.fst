module Hist

open FStar.List.Tot.Base

(** The postcondition for an io computation is defined over the
result (type: a) and local trace (type: trace).
The local trace represents the events that happend during the
computation. Local trace is in chronological order.

We also have the history (type: trace) that represents the
events that happend until the beginning of the io computation.
The history is in reverse chronology order.

At the end of an io computation, the trace will be
(reverse of local trace) appended to the history. **)

let trace = Free.IO.trace

let hist_post a = r:a -> lt:trace -> Type0
let hist_pre a = h:trace -> Type0

let hist a = hist_post a -> hist_pre a 

unfold
let hist_return (x:'a) : hist 'a =
  fun p _ -> p x []

unfold 
let hist_shift_post (p:hist_post 'a) (lt:trace) : hist_post 'a =
  fun r lt' -> p r (lt @ lt')

unfold
let trace_append (h lt:trace) = List.rev lt @ h

unfold
let hist_post_bind
  (h:trace)
  (kw : 'a -> hist 'b)
  (p:hist_post 'b) :
  Tot (hist_post 'a) =
  fun r lt ->
    kw r (hist_shift_post p lt) (trace_append h lt)

unfold
let hist_bind (w : hist 'a) (kw : 'a -> hist 'b) : hist 'b =
  fun p h -> w (hist_post_bind h kw p) h

unfold
let wp_lift_pure_hist (w : pure_wp 'a) : hist 'a =
  fun p _ -> w (fun x -> p x [])

unfold
val hist_ord (#a : Type) : hist a -> hist a -> Type0
let hist_ord wp1 wp2 = forall h p. wp1 p h ==> wp2 p h

unfold
let hist_if_then_else (wp1 wp2:hist 'a) (b:bool) : hist 'a =
  fun p h -> (b ==> wp1 p h) /\ ((~b) ==> wp2 p h)
