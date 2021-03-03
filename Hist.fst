module Hist

open Common
open IO.Free

// local_trace (from old to new)
let hist_post a = maybe a -> lt:trace -> Type0

// past_events (from new to old; reversed compared with local_trace)
let hist a = h:trace -> hist_post a -> Type0

unfold
let hist_return (a:Type) (x:a) : hist a =
  fun _ p -> p (Inl x) []

unfold
let compute_post (a b:Type) (h:trace) (kw : a -> hist b) (p:hist_post b)
  : hist_post a =
      (fun result local_trace ->
        match result with
        | Inl result -> (
            kw result
            ((List.rev local_trace) @ h)
            (fun result' local_trace' ->
                p result' (local_trace @ local_trace')))
        | Inr err -> p (Inr err) local_trace)

unfold
let hist_bind
  (a:Type)
  (b:Type)
  (w : hist a)
  (kw : a -> hist b) :
  Tot (hist b) =
  fun h p ->
    w h (compute_post a b h kw p)

let gen_post #a (post:hist_post a) (cmd:io_cmds) args res =
  fun x local_trace ->
    post x (convert_call_to_event cmd args res :: local_trace)

unfold
val hist_ord (#a : Type) : hist a -> hist a -> Type0
let hist_ord wp1 wp2 = forall h p. wp1 h p ==> wp2 h p

unfold
let hist_if_then_else (#a:Type) (wp1 wp2:hist a) (b:bool) : hist a =
  fun h p -> (b ==> wp1 h p) /\ ((~b) ==> wp2 h p)
