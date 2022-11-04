(** Definition of a monad with iter and requires *)

module DivFree

open Util

noeq
type signature = {
  act : Type0 ;
  arg : a:act -> Type0 ;
  res : #a:act -> arg a -> Type0 ;
}

noeq
type m (sg : signature) (a : Type u#a) : Type =
| Ret : a -> m sg a
| Req : pre:pure_pre -> k:(squash pre -> m sg a) -> m sg a
| Iter : index:Type0 -> b:Type0 -> f:(index -> m sg (liftType u#a (either index b))) -> i:index -> k:(b -> m sg a) -> m sg a
| Call : ac:sg.act -> x:sg.arg ac -> k:(sg.res x -> m sg a) -> m sg a

let m_ret #sg #a (x : a) : m sg a =
  Ret x

let m_req #sg (pre : pure_pre) : m sg (squash pre) =
  Req pre (fun h -> m_ret h)

let rec m_map #sg (#a : Type u#a) (#b : Type u#b) (f : a -> b) (c : m sg a) : m sg b =
  match c with
  | Ret x -> Ret (f x)
  | Req pre k -> Req pre (fun h -> m_map f (k h))
  | Iter index d g i k -> Iter index d (fun j -> m_map reType (g j)) i (fun y -> m_map f (k y))
  | Call ac x k -> Call ac x (fun y -> m_map f (k y))

let m_iter #sg #index #b (f : index -> m sg (either index b)) (i : index) : m sg b =
  Iter index b (fun j -> m_map LiftTy (f j)) i (fun x -> m_ret x)

let m_call #sg (ac : sg.act) (x : sg.arg ac) : m sg (sg.res x) =
  Call ac x (fun y -> m_ret y)

// Could also define m_reType without going through m_map
let m_reType #sg (#d : Type0) (c : m u#a sg (liftType d)) : m u#b sg (liftType d) =
  m_map reType c

let rec m_bind #sg (#a : Type u#a) (#b : Type u#b) (c : m sg a) (f : a -> m sg b) : m sg b =
  match c with
  | Ret x -> f x
  | Req pre k -> Req pre (fun _ -> m_bind (k ()) f)
  | Iter index d g i k -> Iter index d (fun j -> m_reType (g j)) i (fun y -> m_bind (k y) f)
  | Call ac x k -> Call ac x (fun y -> m_bind (k y) f)
