module Hist

open FStar.List.Tot.Base
open Common

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
let hist_post_bind
  (h:trace)
  (kw : 'a -> hist 'b)
  (p:hist_post 'b) :
  Tot (hist_post 'a) =
  fun r lt ->
    kw r (hist_shift_post p lt) ((List.rev lt) @ h)

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
