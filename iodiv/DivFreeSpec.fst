(** Specification of IO + Div *)

module DivFreeSpec

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics // Also defines forall_intro so place before Classical
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc
open FStar.FunctionalExtensionality

open Util
open Stream
open IIOSig

(** Potentially infinite trace *)
noeq
type strace =
| Fintrace : trace -> strace
| Inftrace : stream event -> strace

let strace_prepend (tr : trace) (st : strace) : strace =
  match st with
  | Fintrace tr' -> Fintrace (tr @ tr')
  | Inftrace s -> Inftrace (stream_prepend tr s)

(** Converging or diverging run *)
noeq
type run a =
| Cv : trace -> a -> run a
| Dv : strace -> run a

(** Specification monad *)

let w_pre = history -> Type0
let w_post a = run a -> Type0

let w_pre_le (p q : w_pre) =
  forall hist. p hist ==> q hist

let w_post_le #a (p q : w_post a) =
  forall r. p r ==> q r

let wp' a = w_post a -> w_pre

let wp_monotonic #a (w : wp' a) =
  forall p q. p `w_post_le` q ==> w p `w_pre_le` w q

let wp a =
  w : wp' a { wp_monotonic w }

let wle #a (w w' : wp a) =
  forall p. w' p `w_pre_le` w p

let as_wp #a (w : wp' a) : Pure (wp a) (requires wp_monotonic w) (ensures fun r -> r == w) =
  w

let w_ret #a (x : a) : wp a =
  as_wp (fun post hist -> post (Cv [] x))

let shift_post #a (tr : trace) (post : w_post a) : w_post a =
  fun r ->
    match r with
    | Cv tr' x -> post (Cv (tr @ tr') x)
    | Dv st -> post (Dv (strace_prepend tr st))

let shift_post_mono a tr :
  Lemma (forall (p q : w_post a). p `w_post_le` q ==> shift_post tr p `w_post_le` shift_post tr q)
= ()

let w_bind_post #a #b (wf : a -> wp b) (post : w_post b) hist : w_post a =
  fun r ->
    match r with
    | Cv tr x -> wf x (shift_post tr post) (rev_acc tr hist)
    | Dv st -> post (Dv st)

let w_bind_post_mono #a #b (wf : a -> wp b) p q hist :
  Lemma
    (requires p `w_post_le` q)
    (ensures w_bind_post wf p hist `w_post_le` w_bind_post wf q hist)
= introduce forall r. w_bind_post wf p hist r ==> w_bind_post wf q hist r
  with begin
    match r with
    | Cv tr x ->
      shift_post_mono b tr ;
      assert (shift_post tr p `w_post_le` shift_post tr q) ;
      assert (wf x (shift_post tr p) (rev_acc tr hist) ==> wf x (shift_post tr q) (rev_acc tr hist))
    | Dv st -> ()
  end

let w_bind #a #b (w : wp a) (wf : a -> wp b) : wp b =
  introduce forall p q hist. p `w_post_le` q ==> w_bind_post wf p hist `w_post_le` w_bind_post wf q hist
  with begin
    move_requires (w_bind_post_mono wf p q) hist
  end ;
  as_wp (fun post hist ->
    w (w_bind_post wf post hist) hist
  )
