module Exnhist

open Common
open Free.IO

// local_trace (from old to new)
let exnhist_post a = maybe a -> lt:trace -> Type0

// past_events (from new to old; reversed compared with local_trace)
let exnhist a = h:trace -> exnhist_post a -> Type0

unfold
let exnhist_return (a:Type) (x:a) : exnhist a =
  fun _ p -> p (Inl x) []

unfold
let compute_post
  (a b:Type)
  (h:trace)
  (kw : a -> exnhist b)
  (p:exnhist_post b) :
  Tot (exnhist_post a) =
  (fun result local_trace ->
    match result with
    | Inl result -> (
      kw result
       ((List.rev local_trace) @ h)
       (fun result' local_trace' ->
         p result' (local_trace @ local_trace')))
    | Inr err -> p (Inr err) local_trace)

unfold
let exnhist_bind
  (a:Type)
  (b:Type)
  (w : exnhist a)
  (kw : a -> exnhist b) :
  Tot (exnhist b) =
  fun h p ->
    w h (compute_post a b h kw p)

let gen_post #a (post:exnhist_post a) (cmd:io_cmds) args res =
  fun x local_trace ->
    post x (convert_call_to_event cmd args res :: local_trace)

unfold
val exnhist_ord (#a : Type) : exnhist a -> exnhist a -> Type0
let exnhist_ord wp1 wp2 = forall h p. wp1 h p ==> wp2 h p

unfold
let exnhist_if_then_else (#a:Type) (wp1 wp2:exnhist a) (b:bool) : exnhist a =
  fun h p -> (b ==> wp1 h p) /\ ((~b) ==> wp2 h p)
