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

let rec theta_reType #sg (#d : Type0) (w_act : action_wp sg) (c : m u#a sg (liftType d)) :
  Lemma (ensures theta w_act c `weq` theta w_act (m_reType c)) (decreases c)
= match c with
  | Ret x -> ()

  | Req pre k ->

    introduce forall x. theta w_act (k x) `weq` theta w_act (m_reType (k x))
    with begin
      theta_reType w_act (k x)
    end

  | Iter index ct g i k ->

    calc (==) {
      m_reType (Iter index ct g i k) ;
      == { _ by (compute ()) }
      Iter index ct (fun j -> m_reType (g j)) i (fun y -> m_reType (k y)) ;
    } ;

    introduce forall x. theta w_act (k x) `weq` theta w_act (m_reType (k x))
    with begin
      theta_reType w_act (k x)
    end ;

    introduce forall j. theta w_act (g j) `weq` theta w_act (m_reType (g j))
    with begin
      theta_reType w_act (g j)
    end ;

    calc (weq) {
      w_iter (fun j -> theta w_act (m_reType (g j))) i ;
      `weq` { w_iter_cong (fun j -> theta w_act (m_reType (g j))) (fun j -> theta w_act (g j)) i }
      w_iter (fun j -> theta w_act (g j)) i ;
    } ;
    assert (w_iter (fun j -> theta w_act (g j)) i `weq` w_iter (fun j -> theta w_act (m_reType (g j))) i) ;

    calc (weq) {
      theta w_act c ;
      == {}
      theta w_act (Iter index ct g i k) ;
      == { _ by (compute ()) }
      w_bind (w_iter (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (k x)) ;
      `weq` { w_bind_cong (w_iter (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (k x)) (fun x -> theta w_act (m_reType (k x))) }
      w_bind (w_iter (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (m_reType (k x))) ;
      `weq` {}
      w_bind (w_iter (fun j -> theta w_act (m_reType (g j))) i) (fun x -> theta w_act (m_reType (k x))) ;
      == { _ by (compute ()) }
      theta w_act (Iter index ct (fun j -> m_reType (g j)) i (fun y -> m_reType (k y))) ;
      == {}
      theta w_act (m_reType (Iter index ct g i k)) ;
      == {}
      theta w_act (m_reType c) ;
    }

  | Call ac x k ->

    calc (==) {
      m_reType (Call ac x k) ;
      == { _ by (compute ()) }
      Call ac x (fun y -> m_reType (k y)) ;
    } ;

    introduce forall x. theta w_act (k x) `weq` theta w_act (m_reType (k x))
    with begin
      theta_reType w_act (k x)
    end ;

    calc (weq) {
      theta w_act c ;
      == {}
      theta w_act (Call ac x k) ;
      == { _ by (compute ()) }
      w_bind (w_act ac x) (fun x -> theta w_act (k x)) ;
      `weq` { w_bind_cong (w_act ac x) (fun x -> theta w_act (k x)) (fun x -> theta w_act (m_reType (k x))) }
      w_bind (w_act ac x) (fun x -> theta w_act (m_reType (k x))) ;
      == { _ by (compute ()) }
      theta w_act (Call ac x (fun y -> m_reType (k y))) ;
      == {}
      theta w_act (m_reType (Call ac x k)) ;
      == {}
      theta w_act (m_reType c) ;
    }

let rec theta_bind (#a : Type u#a) (#b : Type u#b) #sg (w_act : action_wp sg) (c : m sg a) (f : a -> m sg b) :
  Lemma (theta w_act (m_bind c f) `wle` w_bind (theta w_act c) (fun x -> theta w_act (f x)))
= match c with
  | Ret x -> forall_intro (shift_post_nil #b)

  | Req pre k ->

    calc (==) {
      m_bind (Req pre k) f ;
      == { _ by (compute ()) }
      Req pre (fun _ -> m_bind (k ()) f) ;
    } ;

    calc (==) {
      theta w_act (Req pre k) ;
      == { _ by (compute ()) }
      w_bind (w_req pre) (fun x -> theta w_act (k x)) ;
    } ;

    calc (==) {
      theta w_act (Req pre (fun y -> m_bind (k y) f)) ;
      == { _ by (compute ()) }
      w_bind (w_req pre) (fun x -> theta w_act (m_bind (k x) f)) ;
    } ;

    w_bind_assoc (w_req pre) (fun x -> theta w_act (k x)) (fun x -> theta w_act (f x)) ;

    introduce forall x. theta w_act (m_bind (k x) f) `wle` w_bind (theta w_act (k x)) (fun y -> theta w_act (f y))
    with begin
      theta_bind w_act (k x) f
    end ;
    w_bind_mono (w_req pre) (fun x -> theta w_act (m_bind (k x) f)) (fun x -> w_bind (theta w_act (k x)) (fun x -> theta w_act (f x))) ;

    wle_trans (theta w_act (m_bind c f)) (w_bind (w_req pre) (fun x -> w_bind (theta w_act (k x)) (fun x -> theta w_act (f x)))) (w_bind (theta w_act c) (fun x -> theta w_act (f x)))

  | Iter index ct g i k ->

    introduce forall x. theta w_act (m_bind (k x) f) `wle` w_bind (theta w_act (k x)) (fun y -> theta w_act (f y))
    with begin
      theta_bind w_act (k x) f
    end ;

    forall_intro (fun j -> theta_reType w_act (g j))  ;
    assert (forall j. theta w_act (g j) `wle` theta w_act (m_reType (g j))) ;

    calc (wle) {
      w_iter (fun j -> theta w_act (m_reType (g j))) i ;
      `wle` { w_iter_mono (fun j -> theta w_act (m_reType (g j))) (fun j -> theta w_act (g j)) i }
      w_iter (fun j -> theta w_act (g j)) i ;
    } ;

    calc (wle) {
      theta w_act (m_bind c f) ;
      == {}
      theta w_act (m_bind (Iter index ct g i k) f) ;
      == { _ by (compute ()) }
      theta w_act (Iter index ct (fun j -> m_reType (g j)) i (fun y -> m_bind (k y) f)) ;
      == { _ by (compute ()) }
      w_bind (w_iter (fun j -> theta w_act (m_reType (g j))) i) (fun x -> theta w_act (m_bind (k x) f)) ;
      `wle` {} // If need be, can use w_bind_mono explicitly
      w_bind (w_iter (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (m_bind (k x) f)) ;
      `wle` {}
      w_bind (w_iter (fun j -> theta w_act (g j)) i) (fun x -> w_bind (theta w_act (k x)) (fun x -> theta w_act (f x))) ;
      `wle` { w_bind_assoc (w_iter (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (k x)) (fun x -> theta w_act (f x)) }
      w_bind (w_bind (w_iter (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (k x))) (fun x -> theta w_act (f x)) ;
      == { _ by (compute ()) }
      w_bind (theta w_act (Iter index ct g i k)) (fun x -> theta w_act (f x)) ;
      == {}
      w_bind (theta w_act c) (fun x -> theta w_act (f x)) ;
    }

  | Call ac x k ->

    calc (==) {
      m_bind (Call ac x k) f ;
      == { _ by (compute ()) }
      Call ac x (fun y -> m_bind (k y) f) ;
    } ;

    calc (==) {
      theta w_act (Call ac x k) ;
      == { _ by (compute ()) }
      w_bind (w_act ac x) (fun x -> theta w_act (k x)) ;
    } ;

    calc (==) {
      theta w_act (Call ac x (fun y -> m_bind (k y) f)) ;
      == { _ by (compute ()) }
      w_bind (w_act ac x) (fun x -> theta w_act (m_bind (k x) f)) ;
    } ;

    w_bind_assoc (w_act ac x) (fun x -> theta w_act (k x)) (fun x -> theta w_act (f x)) ;

    introduce forall x. theta w_act (m_bind (k x) f) `wle` w_bind (theta w_act (k x)) (fun y -> theta w_act (f y))
    with begin
      theta_bind w_act (k x) f
    end ;
    w_bind_mono (w_act ac x) (fun x -> theta w_act (m_bind (k x) f)) (fun x -> w_bind (theta w_act (k x)) (fun x -> theta w_act (f x))) ;

    wle_trans (theta w_act (m_bind c f)) (w_bind (w_act ac x) (fun x -> w_bind (theta w_act (k x)) (fun x -> theta w_act (f x)))) (w_bind (theta w_act c) (fun x -> theta w_act (f x)))

let theta_req #a #sg (w_act : action_wp sg) (pre : pure_pre) :
  Lemma (theta w_act (m_req pre) `wle` w_req pre)
= ()

(** Definition of the Dijkstra monad *)

let dm sg (w_act : action_wp sg) (a : Type) (w : wp a) =
  c : m sg a { theta w_act c `wle` w }

let dm_ret #sg #w_act #a (x : a) : dm sg w_act a (w_ret x) =
  m_ret x

let dm_bind #sg #w_act #a #b #w #wf (c : dm sg w_act a w) (f : (x : a) -> dm sg w_act b (wf x)) : dm sg w_act b (w_bind w wf) =
  calc (wle) {
    theta w_act (m_bind c f) ;
    `wle` { theta_bind w_act c f }
    w_bind (theta w_act c) (fun x -> theta w_act (f x)) ;
    `wle` { w_bind_mono (theta w_act c) (fun x -> theta w_act (f x)) wf }
    w_bind (theta w_act c) wf ;
    `wle` {}
    w_bind w wf ;
  } ;
  m_bind c f

let dm_subcomp #sg #w_act #a #w #w' (c : dm sg w_act a w) :
  Pure (dm sg w_act a w') (requires w `wle` w') (ensures fun r -> r == c)
= c

let dm_if_then_else #sg #w_act (a : Type) (w1 w2 : wp a) (f : dm sg w_act a w1) (g : dm sg w_act a w2) (b : bool) : Type =
  dm sg w_act a (wite w1 w2 b)

let dm_req #sg #w_act (pre : pure_pre) : dm sg w_act (squash pre) (w_req pre) =
  m_req pre

let dm_call #sg (#w_act : action_wp sg) (ac : sg.act) (x : sg.arg ac) : dm sg w_act (sg.res x) (w_act ac x) =
  calc (wle) {
    theta w_act (m_call ac x) ;
    == { _ by (compute ()) }
    w_bind (w_act ac x) (fun x -> theta w_act (m_ret x)) ;
    `wle` { w_bind_mono (w_act ac x) (fun x -> theta w_act (m_ret x)) w_ret }
    w_bind (w_act ac x) w_ret ;
    `wle` { w_bind_ret (w_act ac x) }
    w_act ac x ;
  } ;
  m_call ac x

let dm_iter #sg #w_act #index #b #w (f : (j : index) -> dm sg w_act (liftType (either index b)) (w j)) (i : index) : dm sg w_act b (w_iter w i) =
  calc (wle) {
    theta w_act (m_iter f i) ;
    == { _ by (compute ()) }
    w_bind (w_iter (fun j -> theta w_act (f j)) i) (fun x -> theta w_act (m_ret x)) ;
    `wle` { w_bind_mono (w_iter (fun j -> theta w_act (f j)) i) (fun x -> theta w_act (m_ret x)) w_ret }
    w_bind (w_iter (fun j -> theta w_act (f j)) i) w_ret ;
    `wle` { w_bind_ret (w_iter (fun j -> theta w_act (f j)) i) }
    w_iter (fun j -> theta w_act (f j)) i ;
    `wle` { admit () } // Here the fact that w_iter is contravariant bites us!
    // w_iter should probably be stated in a more positive way, but how?
    w_iter w i ;
  } ;
  m_iter f i

(** Lift from PURE *)

let w_lift_pure #a (w : pure_wp a) : wp a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall () ;
  fun post hist -> w (fun x -> post (Cv [] x))

let elim_pure #a #w (f : unit -> PURE a w) :
  Pure
    a
    (requires w (fun _ -> True))
    (ensures fun r -> forall post. w post ==> post r)
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall () ;
  f ()

let as_requires_w_lift_pure #a (w : pure_wp a) :
  Lemma (forall post hist. w_lift_pure w post hist ==> as_requires w)
= assert (forall post (x : a). post (Cv [] x) ==> True) ;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity w ;
  assert (forall post. w (fun x -> post (Cv [] x)) ==> w (fun _ -> True))

let dm_lift_pure #sg #w_act (a : Type) (w : pure_wp a) (f:(eqtype_as_type unit -> PURE a w)) : dm sg w_act a (w_lift_pure w) =
  as_requires_w_lift_pure w ;
  dm_bind #sg #w_act #_ #_ #(w_req (as_requires w)) #(fun _ -> w_lift_pure w) (dm_req (as_requires w)) (fun (_ : squash (as_requires w)) ->
    let r = elim_pure #a #w f in
    dm_ret #sg #w_act r
  )
