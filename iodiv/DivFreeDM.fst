(** Partial Dijkstra monad definition on top of DivFree *)

module DivFreeDM

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
open DivFree
open DivFreeSpec

type action_wp (sg : signature) =
  ac : sg.act -> x : sg.arg ac -> wp (sg.res x)

let rec theta (#a : Type u#a) #sg (w_act : action_wp sg) (c : m sg a) : wp a =
  match c with
  | Ret x -> w_ret x
  | Req pre k -> w_bind (w_req pre) (fun x -> theta w_act (k x))
  | Iter index b f i k -> w_bind (w_iter u#a (fun j -> theta w_act (f j)) i) (fun x -> theta w_act (k x))
  | Call ac x k -> w_bind (w_act ac x) (fun x -> theta w_act (k x))

let theta_ret #a #sg (w_act : action_wp sg) (x : a) :
  Lemma (theta w_act (m_ret x) `wle` w_ret x)
= ()

// TODO MOVE
let strace_prepend_nil s :
  Lemma (strace_prepend [] s == s)
= match s with
  | Fintrace t -> assert (([] @ t) == t)
  | Inftrace t -> forall_intro (stream_ext t)

// TODO MOVE
let shift_post_nil #a (post : w_post a) :
  Lemma (shift_post [] post `w_post_le` post)
= introduce forall r. shift_post [] post r ==> post r
  with begin
    match r with
    | Cv tr x -> ()
    | Dv s -> strace_prepend_nil s
  end

// TODO MOVE
let shift_post_nil_imp #a (post : w_post a) :
  Lemma (post `w_post_le` shift_post [] post)
= introduce forall r. post r ==> shift_post [] post r
  with begin
    match r with
    | Cv tr x -> ()
    | Dv s -> strace_prepend_nil s
  end

// TODO MOVE
let shift_post_mono #a tr (p q : w_post a) :
  Lemma (p `w_post_le` q ==> shift_post tr p `w_post_le` shift_post tr q)
= ()

let rec theta_bind #a #b #sg (w_act : action_wp sg) (c : m sg a) (f : a -> m sg b) :
  Lemma (theta w_act (m_bind c f) `wle` w_bind (theta w_act c) (fun x -> theta w_act (f x)))
= match c with
  | Ret x -> forall_intro (shift_post_nil #b)
  | Req pre k ->
    // Slow proof, should try to provide more explicit instances?
    forall_intro (shift_post_nil #a) ;
    forall_intro (shift_post_nil_imp #b) ;
    // forall_intro_3 (shift_post_mono #b) ;
    introduce forall x. theta w_act (m_bind (k x) f) `wle` w_bind (theta w_act (k x)) (fun y -> theta w_act (f y))
    with begin
      theta_bind w_act (k x) f
    end
  | Iter index c g i k -> admit ()
  | Call ac x k -> admit ()
