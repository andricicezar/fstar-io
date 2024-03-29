(** Partial Dijkstra monad definition on top of DivFree, using TauSpec *)

module DivFreeTauDM

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
open DivFreeTauSpec

type action_iwp (sg : signature) =
  ac : sg.act -> x : sg.arg ac -> iwp (sg.res x)

let i_unLift #a (w : iwp (liftType u#a a)) : iwp a =
  i_bind w (fun x -> i_ret (unLift x))

// i_iter but with the liftType
let i_iter_lift (#index : Type0) (#a : Type0) (w : index -> iwp (liftType u#a (either index a))) (i : index) : iwp a =
  i_iter (fun j -> i_unLift (w j)) i

let i_iter_lift_mono (#index : Type0) (#a : Type0) (w w' : index -> iwp (liftType u#a (either index a))) (i : index) :
  Lemma
    (requires forall j. w j `ile` w' j)
    (ensures i_iter_lift w i `ile` i_iter_lift w' i)
= // reveal_i_iter index a // Works too but slower and unnecessary
  i_iter_mono (fun j -> i_unLift (w j)) (fun j -> i_unLift (w' j)) i

let i_iter_lift_cong (#index : Type0) (#a : Type0) (w w' : index -> iwp (liftType u#a (either index a))) (i : index) :
  Lemma
    (requires forall j. w j `ieq` w' j)
    (ensures i_iter_lift w i `ieq` i_iter_lift w' i)
= i_iter_lift_mono w w' i ; i_iter_lift_mono w' w i

let rec theta (#a : Type u#a) #sg (w_act : action_iwp sg) (c : m sg a) : iwp a =
  match c with
  | Ret x -> i_ret x
  | Req pre k -> i_bind (i_req pre) (fun x -> theta w_act (k x))
  | Iter index b f i k -> i_bind (i_iter_lift u#a (fun j -> theta w_act (f j)) i) (fun x -> theta w_act (k x))
  | Call ac x k -> i_bind (w_act ac x) (fun x -> theta w_act (k x))

let theta_ret #a #sg (w_act : action_iwp sg) (x : a) :
  Lemma (theta w_act (m_ret x) `ile` i_ret x)
= ()

let rec theta_reType #sg (#d : Type0) (w_act : action_iwp sg) (c : m u#a sg (liftType d)) :
  Lemma (ensures theta w_act c `ieq` theta w_act (m_reType c)) (decreases c)
= match c with
  | Ret x -> ()

  | Req pre k ->

    introduce forall x. theta w_act (k x) `ieq` theta w_act (m_reType (k x))
    with begin
      theta_reType w_act (k x)
    end

  | Iter index ct g i k ->

    calc (==) {
      m_reType (Iter index ct g i k) ;
      == { _ by (compute ()) }
      Iter index ct (fun j -> m_reType (g j)) i (fun y -> m_reType (k y)) ;
    } ;

    introduce forall x. theta w_act (k x) `ieq` theta w_act (m_reType (k x))
    with begin
      theta_reType w_act (k x)
    end ;

    introduce forall j. theta w_act (g j) `ieq` theta w_act (m_reType (g j))
    with begin
      theta_reType w_act (g j)
    end ;

    calc (ieq) {
      i_iter_lift (fun j -> theta w_act (m_reType (g j))) i ;
      `ieq` { i_iter_lift_cong (fun j -> theta w_act (m_reType (g j))) (fun j -> theta w_act (g j)) i }
      i_iter_lift (fun j -> theta w_act (g j)) i ;
    } ;
    assert (i_iter_lift (fun j -> theta w_act (g j)) i `ieq` i_iter_lift (fun j -> theta w_act (m_reType (g j))) i) ;

    calc (ieq) {
      theta w_act c ;
      == {}
      theta w_act (Iter index ct g i k) ;
      == { _ by (compute ()) }
      i_bind (i_iter_lift (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (k x)) ;
      `ieq` { i_bind_cong (i_iter_lift (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (k x)) (fun x -> theta w_act (m_reType (k x))) }
      i_bind (i_iter_lift (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (m_reType (k x))) ;
      `ieq` {}
      i_bind (i_iter_lift (fun j -> theta w_act (m_reType (g j))) i) (fun x -> theta w_act (m_reType (k x))) ;
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

    introduce forall x. theta w_act (k x) `ieq` theta w_act (m_reType (k x))
    with begin
      theta_reType w_act (k x)
    end ;

    calc (ieq) {
      theta w_act c ;
      == {}
      theta w_act (Call ac x k) ;
      == { _ by (compute ()) }
      i_bind (w_act ac x) (fun x -> theta w_act (k x)) ;
      `ieq` { i_bind_cong (w_act ac x) (fun x -> theta w_act (k x)) (fun x -> theta w_act (m_reType (k x))) }
      i_bind (w_act ac x) (fun x -> theta w_act (m_reType (k x))) ;
      == { _ by (compute ()) }
      theta w_act (Call ac x (fun y -> m_reType (k y))) ;
      == {}
      theta w_act (m_reType (Call ac x k)) ;
      == {}
      theta w_act (m_reType c) ;
    }

let rec theta_bind (#a : Type u#a) (#b : Type u#b) #sg (w_act : action_iwp sg) (c : m sg a) (f : a -> m sg b) :
  Lemma (theta w_act (m_bind c f) `ile` i_bind (theta w_act c) (fun x -> theta w_act (f x)))
= match c with
  | Ret x -> forall_intro (ishift_post_nil #b)

  | Req pre k ->

    calc (==) {
      m_bind (Req pre k) f ;
      == { _ by (compute ()) }
      Req pre (fun _ -> m_bind (k ()) f) ;
    } ;

    calc (==) {
      theta w_act (Req pre k) ;
      == { _ by (compute ()) }
      i_bind (i_req pre) (fun x -> theta w_act (k x)) ;
    } ;

    calc (==) {
      theta w_act (Req pre (fun y -> m_bind (k y) f)) ;
      == { _ by (compute ()) }
      i_bind (i_req pre) (fun x -> theta w_act (m_bind (k x) f)) ;
    } ;

    i_bind_assoc (i_req pre) (fun x -> theta w_act (k x)) (fun x -> theta w_act (f x)) ;

    introduce forall x. theta w_act (m_bind (k x) f) `ile` i_bind (theta w_act (k x)) (fun y -> theta w_act (f y))
    with begin
      theta_bind w_act (k x) f
    end ;
    i_bind_mono (i_req pre) (fun x -> theta w_act (m_bind (k x) f)) (fun x -> i_bind (theta w_act (k x)) (fun x -> theta w_act (f x))) ;

    ile_trans (theta w_act (m_bind c f)) (i_bind (i_req pre) (fun x -> i_bind (theta w_act (k x)) (fun x -> theta w_act (f x)))) (i_bind (theta w_act c) (fun x -> theta w_act (f x)))

  | Iter index ct g i k ->

    introduce forall x. theta w_act (m_bind (k x) f) `ile` i_bind (theta w_act (k x)) (fun y -> theta w_act (f y))
    with begin
      theta_bind w_act (k x) f
    end ;

    forall_intro (fun j -> theta_reType w_act (g j))  ;
    assert (forall j. theta w_act (g j) `ile` theta w_act (m_reType (g j))) ;

    calc (ile) {
      i_iter_lift (fun j -> theta w_act (m_reType (g j))) i ;
      `ile` { i_iter_lift_mono (fun j -> theta w_act (m_reType (g j))) (fun j -> theta w_act (g j)) i }
      i_iter_lift (fun j -> theta w_act (g j)) i ;
    } ;

    calc (ile) {
      theta w_act (m_bind c f) ;
      == {}
      theta w_act (m_bind (Iter index ct g i k) f) ;
      == { _ by (compute ()) }
      theta w_act (Iter index ct (fun j -> m_reType (g j)) i (fun y -> m_bind (k y) f)) ;
      == { _ by (compute ()) }
      i_bind (i_iter_lift (fun j -> theta w_act (m_reType (g j))) i) (fun x -> theta w_act (m_bind (k x) f)) ;
      `ile` {} // If need be, can use w_bind_mono explicitly
      i_bind (i_iter_lift (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (m_bind (k x) f)) ;
      `ile` { i_bind_mono (i_iter_lift (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (m_bind (k x) f)) (fun x -> i_bind (theta w_act (k x)) (fun x -> theta w_act (f x))) }
      i_bind (i_iter_lift (fun j -> theta w_act (g j)) i) (fun x -> i_bind (theta w_act (k x)) (fun x -> theta w_act (f x))) ;
      `ile` { i_bind_assoc (i_iter_lift (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (k x)) (fun x -> theta w_act (f x)) }
      i_bind (i_bind (i_iter_lift (fun j -> theta w_act (g j)) i) (fun x -> theta w_act (k x))) (fun x -> theta w_act (f x)) ;
      == { _ by (compute ()) }
      i_bind (theta w_act (Iter index ct g i k)) (fun x -> theta w_act (f x)) ;
      == {}
      i_bind (theta w_act c) (fun x -> theta w_act (f x)) ;
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
      i_bind (w_act ac x) (fun x -> theta w_act (k x)) ;
    } ;

    calc (==) {
      theta w_act (Call ac x (fun y -> m_bind (k y) f)) ;
      == { _ by (compute ()) }
      i_bind (w_act ac x) (fun x -> theta w_act (m_bind (k x) f)) ;
    } ;

    i_bind_assoc (w_act ac x) (fun x -> theta w_act (k x)) (fun x -> theta w_act (f x)) ;

    introduce forall x. theta w_act (m_bind (k x) f) `ile` i_bind (theta w_act (k x)) (fun y -> theta w_act (f y))
    with begin
      theta_bind w_act (k x) f
    end ;
    i_bind_mono (w_act ac x) (fun x -> theta w_act (m_bind (k x) f)) (fun x -> i_bind (theta w_act (k x)) (fun x -> theta w_act (f x))) ;

    ile_trans (theta w_act (m_bind c f)) (i_bind (w_act ac x) (fun x -> i_bind (theta w_act (k x)) (fun x -> theta w_act (f x)))) (i_bind (theta w_act c) (fun x -> theta w_act (f x)))

let rec theta_map_as_bind #sg (w_act : action_iwp sg) (#a : Type u#a) (#b : Type u#b) (f : a -> b) (c : m sg a) :
  Lemma (theta w_act (m_map f c) `ieq` theta w_act (m_bind c (fun x -> m_ret (f x))))
= match c with
  | Ret x -> ()

  | Req pre k ->

    introduce forall x. theta w_act (m_map f (k x)) `ieq` theta w_act (m_bind (k x) (fun x -> m_ret (f x)))
    with begin
      theta_map_as_bind w_act f (k x)
    end

  | Iter index d g i k ->

    assert_norm (m_map f (Iter index d g i k) == Iter index d (fun j -> m_map reType (g j)) i (fun y -> m_map f (k y))) ;
    assert_norm (m_bind (Iter index d g i k) (fun x -> m_ret (f x)) == Iter index d (fun j -> m_map reType (g j)) i (fun y -> m_bind (k y) (fun x -> m_ret (f x)))) ;

    introduce forall x. theta w_act (m_map f (k x)) `ieq` theta w_act (m_bind (k x) (fun x -> m_ret (f x)))
    with begin
      theta_map_as_bind w_act f (k x)
    end ;

    calc (ieq) {
      theta w_act (m_map f c) ;
      == {}
      theta w_act (Iter index d (fun j -> m_map reType (g j)) i (fun y -> m_map f (k y))) ;
      == { _ by (compute ()) }
      i_bind (i_iter_lift (fun j -> theta w_act (m_map reType (g j))) i) (fun x -> theta w_act (m_map f (k x))) ;
      `ieq` { i_bind_cong (i_iter_lift (fun j -> theta w_act (m_map reType (g j))) i) (fun x -> theta w_act (m_map f (k x))) (fun x -> theta w_act (m_bind (k x) (fun x -> m_ret (f x)))) }
      i_bind (i_iter_lift (fun j -> theta w_act (m_map reType (g j))) i) (fun x -> theta w_act (m_bind (k x) (fun x -> m_ret (f x)))) ;
      == { _ by (compute ()) }
      theta w_act (Iter index d (fun j -> m_map reType (g j)) i (fun y -> m_bind (k y) (fun x -> m_ret (f x)))) ;
      == {}
      theta w_act (m_bind c (fun x -> m_ret (f x))) ;
    }

  | Call ac x k ->

    assert_norm (m_map f (Call ac x k) == Call ac x (fun y -> m_map f (k y))) ;
    assert_norm (m_bind (Call ac x k) (fun x -> m_ret (f x)) == Call ac x (fun y -> m_bind (k y) (fun x -> m_ret (f x)))) ;

    introduce forall x. theta w_act (m_map f (k x)) `ieq` theta w_act (m_bind (k x) (fun x -> m_ret (f x)))
    with begin
      theta_map_as_bind w_act f (k x)
    end ;

    calc (ieq) {
      theta w_act (m_map f c) ;
      == {}
      theta w_act (Call ac x (fun y -> m_map f (k y))) ;
      == { _ by (compute ()) }
      i_bind (w_act ac x) (fun x -> theta w_act (m_map f (k x))) ;
      `ieq` { i_bind_cong (w_act ac x) (fun x -> theta w_act (m_map f (k x))) (fun x -> theta w_act (m_bind (k x) (fun x -> m_ret (f x)))) }
      i_bind (w_act ac x) (fun x -> theta w_act (m_bind (k x) (fun x -> m_ret (f x)))) ;
      == { _ by (compute ()) }
      theta w_act (Call ac x (fun y -> m_bind (k y) (fun x -> m_ret (f x)))) ;
      == {}
      theta w_act (m_bind c (fun x -> m_ret (f x))) ;
    }

let theta_map (#a : Type u#a) (#b : Type u#b) #sg (w_act : action_iwp sg) (f : a -> b) (c : m sg a) :
  Lemma (theta w_act (m_map f c) `ile` i_bind (theta w_act c) (fun x -> i_ret (f x)))
= calc (ile) {
    theta w_act (m_map f c) ;
    `ieq` { theta_map_as_bind w_act f c }
    theta w_act (m_bind c (fun x -> m_ret (f x))) ;
    `ile` { theta_bind w_act c (fun x -> m_ret (f x)) }
    i_bind (theta w_act c) (fun x -> theta w_act (m_ret (f x))) ;
    `ile` { i_bind_mono (theta w_act c) (fun x -> theta w_act (m_ret (f x))) (fun x -> i_ret (f x)) }
    i_bind (theta w_act c) (fun x -> i_ret (f x)) ;
  }

let theta_req #a #sg (w_act : action_iwp sg) (pre : pure_pre) :
  Lemma (theta w_act (m_req pre) `ile` i_req pre)
= ()

(** Definition of the Dijkstra monad *)

let dm sg (w_act : action_iwp sg) (a : Type) (w : iwp a) =
  c : m sg a { theta w_act c `ile` w }

let dm_ret #sg #w_act #a (x : a) : dm sg w_act a (i_ret x) =
  m_ret x

let dm_bind #sg #w_act #a #b #w #wf (c : dm sg w_act a w) (f : (x : a) -> dm sg w_act b (wf x)) : dm sg w_act b (i_bind_alt w wf) =
  calc (ile) {
    theta w_act (m_bind c f) ;
    `ile` { theta_bind w_act c f }
    i_bind (theta w_act c) (fun x -> theta w_act (f x)) ;
    `ile` { i_bind_mono (theta w_act c) (fun x -> theta w_act (f x)) wf }
    i_bind (theta w_act c) wf ;
    `ile` {}
    i_bind w wf ;
    `ile` { i_bind_alt_eq w wf }
    i_bind_alt w wf ;
  } ;
  m_bind c f

let dm_subcomp #sg #w_act #a #w #w' (c : dm sg w_act a w) :
  Pure (dm sg w_act a w') (requires w `ile` w') (ensures fun r -> r == c)
= c

unfold
let dm_if_then_else #sg #w_act (a : Type) (w1 w2 : iwp a) (f : dm sg w_act a w1) (g : dm sg w_act a w2) (b : bool) : Type =
  dm sg w_act a (iwite w1 w2 b)

let dm_req #sg #w_act (pre : pure_pre) : dm sg w_act (squash pre) (i_req pre) =
  m_req pre

let dm_call #sg (#w_act : action_iwp sg) (ac : sg.act) (x : sg.arg ac) : dm sg w_act (sg.res x) (w_act ac x) =
  calc (ile) {
    theta w_act (m_call ac x) ;
    == { _ by (compute ()) }
    i_bind (w_act ac x) (fun x -> theta w_act (m_ret x)) ;
    `ile` { i_bind_mono (w_act ac x) (fun x -> theta w_act (m_ret x)) i_ret }
    i_bind (w_act ac x) i_ret ;
    `ile` { i_bind_ret (w_act ac x) }
    w_act ac x ;
  } ;
  m_call ac x

let i_unlift_lift #a (w : iwp a) :
  Lemma (i_unLift (i_bind w (fun x -> i_ret (LiftTy x))) `ile` w)
= introduce forall post hist. w post hist ==> i_unLift (i_bind w (fun x -> i_ret (LiftTy x))) post hist
  with begin
    calc (==) {
      i_unLift (i_bind w (fun x -> i_ret (LiftTy x))) post hist ;
      == {}
      i_bind (i_bind w (fun x -> i_ret (LiftTy x))) (fun x -> i_ret (unLift x)) post hist ;
      == {}
      i_bind w (fun x -> i_ret (LiftTy x)) (i_bind_post (fun x -> i_ret (unLift x)) post hist) hist ;
      == {}
      w (i_bind_post (fun x -> i_ret (LiftTy x)) (i_bind_post (fun x -> i_ret (unLift x)) post hist) hist) hist ;
    } ;
    introduce forall r. post r ==> i_bind_post (fun x -> i_ret (LiftTy x)) (i_bind_post (fun x -> i_ret (unLift x)) post hist) hist r
    with begin
      match r with
      | Cv tr x -> ()
      | Dv s -> ()
    end ;
    assert (post `i_post_le` i_bind_post (fun x -> i_ret (LiftTy x)) (i_bind_post (fun x -> i_ret (unLift x)) post hist) hist)
  end

let dm_iter #sg #w_act #index #b #w (f : (j : index) -> dm sg w_act (either index b) (w j)) (i : index) : dm sg w_act b (i_iter w i) =

  introduce forall j. theta w_act (m_map LiftTy (f j)) `ile` i_bind (theta w_act (f j)) (fun x -> i_ret (LiftTy x))
  with begin
    theta_map w_act LiftTy (f j)
  end ;

  introduce forall j. i_unLift (i_bind (theta w_act (f j)) (fun x -> i_ret (LiftTy x))) `ile` w j
  with begin
    i_unlift_lift (theta w_act (f j))
  end ;

  calc (ile) {
    theta w_act (m_iter f i) ;
    == { _ by (compute ()) }
    i_bind (i_iter_lift (fun j -> theta w_act (m_map LiftTy (f j))) i) (fun x -> theta w_act (m_ret x)) ;
    `ile` { i_bind_mono (i_iter_lift (fun j -> theta w_act (m_map LiftTy (f j))) i) (fun x -> theta w_act (m_ret x)) i_ret }
    i_bind (i_iter_lift (fun j -> theta w_act (m_map LiftTy (f j))) i) i_ret ;
    `ile` { i_bind_ret (i_iter_lift (fun j -> theta w_act (m_map LiftTy (f j))) i) }
    i_iter_lift (fun j -> theta w_act (m_map LiftTy (f j))) i ;
    `ile` { i_iter_lift_mono (fun j -> theta w_act (m_map LiftTy (f j))) (fun j -> i_bind (theta w_act (f j)) (fun x -> i_ret (LiftTy x))) i }
    i_iter_lift (fun j -> i_bind (theta w_act (f j)) (fun x -> i_ret (LiftTy x))) i ;
    == { _ by (compute ()) }
    i_iter (fun j -> i_unLift (i_bind (theta w_act (f j)) (fun x -> i_ret (LiftTy x)))) i ;
    `ile` { i_iter_mono (fun j -> i_unLift (i_bind (theta w_act (f j)) (fun x -> i_ret (LiftTy x)))) w i }
    i_iter w i ;
  } ;
  m_iter f i

(** Lift from PURE *)

unfold
let w_lift_pure #a (w : pure_wp a) : iwp a =
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
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs = dm_req (as_requires w) in
  let rhs = (fun (pre:(squash (as_requires w))) -> dm_ret #sg #w_act #a (f pre)) in
  let m = dm_bind lhs rhs in
  dm_subcomp m

