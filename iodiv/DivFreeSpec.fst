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

let ttrunc (trs : stream trace) (n : nat) : trace =
  flatten (stream_trunc trs n)

let strace_refine (st : strace) (trs : stream trace) =
  match st with
  | Fintrace tr -> exists (n : nat). forall (m : nat). n <= m ==> tr == ttrunc trs n
  | Inftrace s -> forall (n : nat). ttrunc trs n == stream_trunc s (length (ttrunc trs n))

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

let w_req (pre : pure_pre) : wp (squash pre) =
  as_wp (fun post hist -> pre /\ post (Cv [] (Squash.get_proof pre)))

let w_open (s : string) : wp file_descr =
  as_wp (fun post hist -> forall fd. post (Cv [ EOpenFile s fd ] fd))

let w_read (fd : file_descr) : wp string =
  as_wp (fun post hist -> is_open fd hist /\ (forall s. post (Cv [ ERead fd s ] s)))

let w_close (fd : file_descr) : wp unit =
  as_wp (fun post hist -> is_open fd hist /\ post (Cv [ EClose fd ] ()))

let w_get_trace : wp history =
  as_wp (fun post hist -> post (Cv [] hist))

let rec w_iter_n (#index : Type0) (#b : Type0) (n : nat) (w : index -> wp (liftType u#a (either index b))) (i : index) : wp (liftType u#a (either index b)) =
  if n = 0
  then w i
  else w_bind (w i) (fun r ->
    match r with
    | LiftTy (Inl j) -> w_iter_n (n-1) w j
    | LiftTy (Inr x) -> w_ret (LiftTy (Inr x))
  )

let w_iter (#index : Type0) (#b : Type0) (w : index -> wp (liftType u#a (either index b))) (i : index) : wp b =
  as_wp (fun post hist ->
    // Finite iteration
    begin
      forall n tr x.
        w_iter_n n w i (fun r -> r == Cv tr (LiftTy (Inr x))) hist ==>
        post (Cv tr x)
    end /\
    // Finite iteration with final branch diverging
    begin
      forall n st.
        w_iter_n n w i (fun r -> r == Dv st) hist ==>
        post (Dv st)
    end /\
    // Infinite iteration
    begin
      forall (js : stream index) (trs : stream trace) s.
        w i (fun r -> r == Cv (trs 0) (LiftTy (Inl (js 0)))) hist ==>
        (forall (n : nat). w (js n) (fun r -> r == Cv (trs (n+1)) (LiftTy (Inl (js (n+1))))) (rev_acc (ttrunc trs n) hist)) ==>
        s `strace_refine` trs ==>
        post (Dv s)
    end
  )