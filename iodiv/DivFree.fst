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

let m_iter #sg #index #b (f : index -> m sg (liftType (either index b))) (i : index) : m sg (liftType b) =
  Iter index b f i (fun x -> m_ret (LiftTy x))

let m_call #sg (ac : sg.act) (x : sg.arg ac) : m sg (sg.res x) =
  Call ac x (fun y -> m_ret y)

let rec m_bind #sg (#a : Type u#a) (#b : Type u#b) (c : m sg a) (f : a -> m sg b) : m sg b =
  match c with
  | Ret x -> f x
  | Req pre k -> Req pre (fun _ -> m_bind (k ()) f)
  | Iter index b g i k -> Iter index b (fun j -> m_bind (g j) (fun z -> match z with LiftTy x -> m_ret (LiftTy u#b x))) i (fun y -> m_bind (k y) f)
  | Call ac x k -> Call ac x (fun y -> m_bind (k y) f)
