(** Alternative definition of ND *)

module NDAlt

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics
open FStar.Classical

(** Computational monad *)

let m a = list a

let m_return #a (x : a) : m a =
  [ x ]

let m_bind #a #b (c : m a) (f : a -> m b) : m b =
  concatMap f c

(** Specification monad *)

let wpre = Type0
let wpost a = a -> Type0

let wp a = wpost a -> wpre

unfold
let _wle #a (w1 w2 : wp a) =
  forall x. w2 x ==> w1 x

let wle #a (w1 w2 : wp a) =
  _wle w1 w2

unfold
let _w_return #a (x : a) : wp a =
  fun post -> post x

let w_return #a (x : a) : wp a =
  _w_return x

unfold
let _w_bind #a #b (w : wp a) (wf : a -> wp b) : wp b =
  fun post -> w (fun x -> wf x post)

let w_bind #a #b (w : wp a) (wf : a -> wp b) : wp b =
  _w_bind w wf

(** Effect observation *)

let theta #a (c : m a) : wp a =
  fun post -> forall x. x `memP` c ==> post x

(** Dijkstra monad *)

let dm a (w : wp a) =
  c : m a { theta c `wle` w }

let d_return #a (x : a) : dm a (w_return x) =
  m_return x

let rec memP_append_invert #a (x : a) (l l' : list a) :
  Lemma
    (requires x `memP` (l @ l'))
    (ensures x `memP` l \/ x `memP` l')
= match l with
  | [] -> ()
  | e :: tl ->
    eliminate x == e \/ x `memP` (tl @ l')
    returns x `memP` l \/ x `memP` l'
    with _. ()
    and _. memP_append_invert x tl l'

let rec memP_bind_inv #a #b (c : m a) (f : a -> m b) y :
  Lemma
    (requires y `memP` m_bind c f)
    (ensures exists x. x `memP` c /\ y `memP` f x)
= match c with
  | e :: l ->
    memP_append_invert y (f e) (m_bind l f) ;
    eliminate y `memP` f e \/ y `memP` m_bind l f
    returns exists x. x `memP` c /\ y `memP` f x
    with _. ()
    and _. memP_bind_inv l f y

let theta_bind #a #b (c : m a) (f : a -> m b) :
  Lemma (theta (m_bind c f) `wle` w_bind (theta c) (fun x -> theta (f x)))
= introduce forall post. w_bind (theta c) (fun x -> theta (f x)) post ==> theta (m_bind c f) post
  with begin
    introduce w_bind (theta c) (fun x -> theta (f x)) post ==> theta (m_bind c f) post
    with _. begin
      introduce forall x. x `memP` (m_bind c f) ==> post x
      with begin
        introduce x `memP` (m_bind c f) ==> post x
        with _. begin
          assert (theta c (fun x -> theta (f x) post)) ;
          assert (forall z. z `memP` c ==> theta (f z) (fun x -> post x)) ;
          assert (forall z z'. z `memP` c /\ z' `memP` (f z) ==> post z') ;
          memP_bind_inv c f x
        end
      end
    end
  end

let d_bind #a #b #w (#wf : a -> wp b) (c : dm a w) (f : (x : a) -> dm b (wf x)) : dm b (w_bind w wf) =
  theta_bind c f ;
  m_bind c f

let d_subcomp #a #w1 #w2 (c : dm a w1) :
  Pure (dm a w2) (requires w1 `wle` w2) (ensures fun _ -> True)
= c

(** Refine operator to overspecify the result of a computation *)

let respects #a (x : a) (w : wp a) =
  forall p. w p ==> p x

unfold
let resp #a (w : wp a) =
  x : a { x `respects` w }

unfold
let w_ref #a (w : wp a) : wp (resp w) =
  fun p -> w (fun x -> x `respects` w ==> p x)

let rec d_ref #a #w (c : dm a w) : dm (resp w) (w_ref w) =
  match c with
  | [] -> []
  | x :: l -> x :: d_ref l

(** Partial Dijkstra monad *)

let pdm a (w : wp a) =
  pre : pure_pre { forall post. w post ==> pre } & (squash pre -> dm a w)

let return a (x : a) : pdm a (_w_return x) =
  (| True , (fun _ -> d_return x) |)

let get_pre #a #w (t : pdm a w) : Pure pure_pre (requires True) (ensures fun r -> forall post. w post ==> r) =
  let (| pre , f |) = t in pre

let get_fun #a #w (t : pdm a w) : Pure (dm a w) (requires get_pre t) (ensures fun _ -> True) =
  let (| pre, f |) = t in f ()

let bind a b w wf (c : pdm a w) (f : (x:a) -> pdm b (wf x)) : pdm b (w_bind w wf) =
  assume (w_bind (w_ref w) wf `wle` w_bind w wf) ; // Missing monotonicity to prove it
  // introduce forall post. w_bind w wf post ==> w_bind (w_ref w) wf post
  // with begin
  //   introduce w_bind w wf post ==> w_bind (w_ref w) wf post
  //   with _. begin
  //     admit ()
  //   end
  // end ;
  (| (get_pre c /\ (forall x. x `respects` w ==> get_pre (f x))) , (fun _ -> d_bind (d_ref (get_fun c)) (fun x -> get_fun (f x))) |)

let subcomp (a : Type) (w1 w2 : wp a) (m : pdm a w1) :
  Pure (pdm a w2) (requires w1 `_wle` w2) (ensures fun _ -> True)
= (| get_pre m , (fun _ -> get_fun m) |)

let w_if_then_else #a (w1 w2 : wp a) (b : bool) : wp a =
  fun post -> (b ==> w1 post) /\ (~ b ==> w2 post)

let if_then_else (a : Type) (w1 w2 : wp a) (f : pdm a w1) (g : pdm a w2) (b : bool) : Type =
  pdm a (w_if_then_else w1 w2 b)

let elim_pure #a #w (f : unit -> PURE a w) :
  Pure
    a
    (requires w (fun _ -> True))
    (ensures fun r -> forall post. w post ==> post r)
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall () ;
  f ()

unfold
let wlift #a (w : pure_wp a) : wp a =
  fun post -> w post

let as_requires_wlift #a (w : pure_wp a) :
  Lemma (forall post. wlift w post ==> as_requires w)
= assert (forall post (x : a). post x ==> True) ;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity w ;
  assert (forall post. w post ==> w (fun _ -> True)) ;
  assert (forall post. (True ==> w post) ==> w (fun _ -> True))

let lift_pure (a : Type) (w : pure_wp a) (f:(eqtype_as_type unit -> PURE a w)) : pdm a (wlift w) =
  as_requires_wlift w ;
  (| as_requires w , (fun _ ->
    let r = elim_pure #a #w f in
    let r' : dm a (w_return r) = d_return r in
    d_subcomp r'
  ) |)

[@@allow_informative_binders]
reflectable reifiable total layered_effect {
  NDw : a:Type -> w:wp a -> Effect
  with
    repr         = pdm ;
    return       = return ;
    bind         = bind ;
    subcomp      = subcomp ;
    if_then_else = if_then_else
}

sub_effect PURE ~> NDw = lift_pure

unfold
let wprepost #a (pre : Type0) (post : a -> Pure Type0 (requires pre) (ensures fun _ -> True)) : wp a =
  fun p -> pre /\ (forall x. post x ==> p x)

effect ND (a : Type) (pre : Type0) (post : a -> Pure Type0 (requires pre) (ensures fun _ -> True)) =
  NDw a (wprepost pre post)

(** Action *)

let m_choose #a (l : list a) : m a =
  l

let w_choose #a (l : list a) : wp a =
  fun post -> forall x. x `memP` l ==> post x

let d_choose #a (l : list a) : dm a (w_choose l) =
  m_choose l

let p_choose #a (l : list a) : pdm a (w_choose l) =
  (| True , (fun _ -> d_choose l) |)

let choose #a (l : list a) : ND a (requires True) (ensures fun r -> r `memP` l) =
  ND?.reflect (subcomp _ _ _ (p_choose l))

(** Some tests for ND *)

let test_assert p : ND unit (requires p) (ensures fun r -> True) =
  assert p

let partial_match (l : list nat) : ND unit (requires l <> []) (ensures fun r -> True) =
  match l with
  | x :: r -> ()

let partial_match_choose (l : list nat) : ND nat (requires l <> []) (ensures fun r -> r `memP` tail l) =
  match l with
  | x :: r -> choose r

assume val p : Type0
assume val p' : Type0
assume val pure_lemma (_ : unit) : Lemma p
assume val some_f (_ : squash p) : ND unit (requires True) (ensures fun _ -> True)
assume val some_f' : unit -> ND unit (requires p) (ensures fun _ -> p')

[@expect_failure]
let pure_lemma_test () : ND unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;
  some_f ()

[@expect_failure]
let pure_lemma_test2 () : ND unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;
  some_f () ;
  some_f' () ;
  assert p'

[@expect_failure]
let rec easy_rec (n : nat) : ND nat (requires True) (ensures fun _ -> True) =
  if n = 0 then 0 else easy_rec (n - 1)

let rec some_rec_tot (n : nat) : nat =
  if n > 3
  then 2 + some_rec_tot (n -3)
  else 1

[@expect_failure]
let rec some_rec (n : nat) : ND nat (requires True) (ensures fun _ -> True) =
  if n > 3
  then 2 + some_rec (n -3)
  else 1

[@expect_failure]
let rec some_rec (n : nat) : ND nat (requires True) (ensures fun _ -> True) =
  if n > 3
  then begin
    let x = some_rec (n-3) in
    2 + x
  end
  else 1
