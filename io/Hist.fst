module Hist

open FStar.List.Tot.Base
open Common
open Free.IO

// local_trace (from old to new)
let hist_post a = a -> lt:trace -> Type0

// past_events (from new to old; reversed compared with local_trace)
let hist a = h:trace -> hist_post a -> Type0

unfold
let hist_return (a:Type) (x:a) : hist a =
  fun _ p -> p x []

unfold
let compute_post
  (a b:Type)
  (h:trace)
  (kw : a -> hist b)
  (p:hist_post b) :
  Tot (hist_post a) =
  (fun result local_trace ->
      kw result
       ((List.rev local_trace) @ h)
       (fun result' local_trace' ->
         p result' (local_trace @ local_trace')))

unfold
let hist_bind
  (a:Type)
  (b:Type)
  (w : hist a)
  (kw : a -> hist b) :
  Tot (hist b) =
  fun h p ->
    w h (compute_post a b h kw p)

let gen_post #a (post:hist_post a) (cmd:io_cmds) arg res =
  fun r local_trace ->
    post r (convert_call_to_event cmd arg res :: local_trace)

unfold
val hist_ord (#a : Type) : hist a -> hist a -> Type0
let hist_ord wp1 wp2 = forall h p. wp1 h p ==> wp2 h p

unfold
let hist_if_then_else (#a:Type) (wp1 wp2:hist a) (b:bool) : hist a =
  fun h p -> (b ==> wp1 h p) /\ ((~b) ==> wp2 h p)
