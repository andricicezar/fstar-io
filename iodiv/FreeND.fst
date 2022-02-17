(** This is a test towards general partial Dijkstra monads

    Here we build on the example of the ND effect but this time using
    a free monad representation.
*)

module FreeND

open FStar.Tactics
open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical
open FStar.Calc


// Because of the refinement on l, this is not an instance of Cezar's Free
noeq
type m a =
| Return : x:a -> m a
| Choose : #b:Type -> l:list b -> k:((x : b { x `memP` l }) -> m a) -> m a

let m_return #a (x : a) : m a =
  Return x

let rec return_of #a (x : a) (c : m a) =
  match c with
  | Return y -> x == y
  | Choose l k -> exists y. y `memP` l /\ x `return_of` (k y)

unfold
let ret #a (c : m a) =
  x : a { x `return_of` c }

let rec m_bind #a #b (c : m a) (f : ret c -> m b) : m b =
  match c with
  | Return x -> f x
  | Choose l k -> Choose l (fun x -> m_bind (k x) f)

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

// Cezar's subcomp_w
let wcast #a p q (w : wp (x : a { p x })) :
  Pure (wp (x : a { q x })) (requires forall x. p x ==> q x) (ensures fun _ -> True) =
  w

let wcast_implies #a p q (w : wp (x : a { p x })) (post : wpost (x : a { q x })) :
  Lemma
    (requires (forall x. p x ==> q x) /\ wcast p q w post)
    (ensures w post)
= ()


let w_choose #a (l : list a) : wp (x : a { x `memP` l }) =
  fun post -> forall x. x `memP` l ==> post x

let rec theta #a (c : m a) : wp (ret c) =
  match c with
  | Return x -> w_return x
  | Choose l k -> w_bind #_ #(ret c) (w_choose l) (fun x -> theta (k x))

// This one would work too!
// let theta #a (c : m a) : wp (ret c) =
//   fun post -> forall x. x `return_of` c ==> post x

let dm a (w : wp a) =
  c : m a { theta c `wle #a` w }

let d_return #a (x : a) : dm a (w_return x) =
  m_return x

let rec memP_in_append #a (x : a) (l l' : list a) :
  Lemma
    (requires x `memP` l \/ x `memP` l')
    (ensures x `memP` (l @ l'))
    [SMTPat (x `memP` (l @ l'))]
= match l with
  | [] -> ()
  | e :: tl ->
    eliminate x == e \/ (x `memP` tl \/ x `memP` l')
    returns x `memP` (l @ l')
    with _. ()
    and _. memP_in_append x tl l'

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

let rec return_of_bind #a #b (c : m a) (f : ret c -> m b) (x : ret c) :
  Lemma (forall y. y `return_of` f x ==> y `return_of` m_bind c f)
= match c with
  | Return y -> ()
  | Choose l k ->
    eliminate exists y. y `memP` l /\ x `return_of` (k y)
    returns forall u. u `return_of` f x ==> u `return_of` Choose l (fun z -> m_bind (k z) f)
    with _. return_of_bind (k y) f x

// let rec memP_bind_inv #a #b (c : m a) (f : ret c -> m b) y :
//   Lemma
//     (requires y `memP` m_bind c f)
//     (ensures exists x. x `memP` c /\ y `memP` f x)
// = match c with
//   | e :: l ->
//     memP_append_invert y (f e) (m_bind l f) ;
//     eliminate y `memP` f e \/ y `memP` m_bind l f
//     returns exists x. x `memP` c /\ y `memP` f x
//     with _. ()
//     and _. memP_bind_inv l f y

let w_bind_imples #a #b (w : wp a) (wf : a -> wp b) (post : wpost b) :
  Lemma
    (requires w_bind w wf post)
    (ensures w (fun x -> wf x post))
= ()

// let m_bind_choose #a #b #c (l : list a) (k : (x : a { x `memP` l }) -> m b) (f : ret (Choose l k) -> m c) :
//   Lemma (m_bind (Choose l k) f == Choose l (fun x -> m_bind (k x) f))
// = admit ()

let rec theta_bind #a #b (c : m a) (f : ret c -> m b) :
  Lemma (theta (m_bind c f) `wle` w_bind #(ret c) #(ret (m_bind c f)) (theta c) (fun x -> return_of_bind c f x ; wcast (fun y -> y `return_of` f x) _ (theta (f x))))
= forall_intro (return_of_bind c f) ;
  introduce forall post. w_bind #(ret c) #(ret (m_bind c f)) (theta c) (fun x -> wcast (fun y -> y `return_of` f x) _ (theta (f x))) post ==> theta (m_bind c f) post
  with begin
    introduce w_bind #(ret c) #(ret (m_bind c f)) (theta c) (fun x -> wcast (fun y -> y `return_of` f x) _ (theta (f x))) post ==> theta (m_bind c f) post
    with _. begin
      match c with
      | Return x -> ()
      | Choose l k ->
        assert (w_bind #(ret c) #(ret (m_bind c f)) (theta (Choose l k)) (fun x -> wcast (fun y -> y `return_of` f x) _ (theta (f x))) post) ;
        assert (w_bind #(ret c) #(ret (m_bind c f)) (w_bind #_ #(ret c) (w_choose l) (fun x -> theta (k x))) (fun x -> wcast (fun y -> y `return_of` f x) _ (theta (f x))) post) ;
        w_bind_imples (w_bind #_ #(ret c) (w_choose l) (fun x -> theta (k x))) (fun x -> wcast (fun y -> y `return_of` f x) _ (theta (f x))) post ;
        assert (w_bind #_ #(ret c) (w_choose l) (fun x -> theta (k x)) (fun x -> wcast (fun y -> y `return_of` f x) _ (theta (f x)) post)) ;
        w_bind_imples #_ #(ret c) (w_choose l) (fun x -> theta (k x)) (fun x -> wcast (fun y -> y `return_of` f x) _ (theta (f x)) post) ;
        // assert (w_choose l (fun x -> theta (k x) (fun x -> wcast (fun y -> y `return_of` f x) _ (theta (f x)) post))) ;
        // assume (forall x. x `memP` l ==> theta (k x) (fun x -> wcast (fun y -> y `return_of` f x) _ (theta (f x)) post)) ; // Seems to be efficiency issue

        introduce forall x. x `memP` l ==> theta ((fun x -> m_bind (k x) f) x) post
        with begin
          introduce x `memP` l ==> theta (m_bind (k x) f) post
          with _. begin
            // Should follow from the above
            assume (theta (k x) (fun x -> wcast (fun y -> y `return_of` f x) _ (theta (f x)) post)) ;
            assume (w_bind #(ret (k x)) #(ret (m_bind (k x) f)) (theta (k x)) (fun y -> return_of_bind (k x) f y ; wcast (fun z -> z `return_of` f y) _ (theta (f y))) post) ;
            admit () ; // Sadly not enough?
            theta_bind (k x) f
          end
        end
    end
  end

// Also works with == but I guess wle is enough
let theta_bind #a #b (c : m a) (f : ret c -> m b) :
  Lemma (theta (m_bind c f) `wle` w_bind #(ret c) #(ret (m_bind c f)) (theta c) (fun x -> return_of_bind c f x ; wcast (fun y -> y `return_of` f x) _ (theta (f x))))
= forall_intro (return_of_bind c f) ;
  introduce forall post. w_bind #(ret c) #(ret (m_bind c f)) (theta c) (fun x -> wcast (fun y -> y `return_of` f x) _ (theta (f x))) post ==> theta (m_bind c f) post
  with begin
    introduce w_bind #(ret c) #(ret (m_bind c f)) (theta c) (fun x -> wcast (fun y -> y `return_of` f x) _ (theta (f x))) post ==> theta (m_bind c f) post
    with _. begin
      introduce forall x. x `memP` (m_bind c f) ==> post x
      with begin
        introduce x `memP` (m_bind c f) ==> post x
        with _. begin
          assert (theta c (fun x -> wcast (fun y -> y `return_of` f x) _ (theta (f x)) post)) ;
          assert (forall z. z `memP` c ==> wcast (fun y -> y `return_of` f z) _ (theta (f z)) post) ;
          assert (forall z. z `memP` c ==> theta (f z) (fun x -> post x)) ;
          assert (forall z z'. z `memP` c /\ z' `memP` (f z) ==> post z') ;
          memP_bind_inv c f x
        end
      end
    end
  end

let d_bind #a #b #w (#wf : a -> wp b) (c : dm a w) (f : (x : ret c) -> dm b (wf x)) : dm b (w_bind w wf) =
  theta_bind c f ;
  m_bind c f


let pdm a (w : wp a) =
  pre : pure_pre { forall post. w post ==> pre } & (squash pre -> dm a w)

let return a (x : a) : pdm a (_w_return x) =
  (| True , (fun _ -> d_return x) |)

let get_pre #a #w (t : pdm a w) : Pure pure_pre (requires True) (ensures fun r -> forall post. w post ==> r) =
  let (| pre , f |) = t in pre

let get_fun #a #w (t : pdm a w) : Pure (dm a w) (requires get_pre t) (ensures fun _ -> True) =
  let (| pre, f |) = t in f ()

let bind a b w wf (c : pdm a w) (f : (x:a) -> pdm b (wf x)) : pdm b (_w_bind w wf) =
  (| (get_pre c /\ (forall x. x `return_of` (get_fun c) ==> get_pre (f x))) , (fun _ -> d_bind (get_fun c) (fun x -> get_fun (f x))) |)

let d_subcomp #a (w1 w2 : wp a) (m : dm a w1) :
  Pure (dm a w2) (requires w1 `wle` w2) (ensures fun _ -> True)
= m

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
    d_subcomp (w_return r) (wlift w) r'
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

let pure_lemma_test () : ND unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;
  some_f ()

let pure_lemma_test2 () : ND unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;
  some_f () ;
  some_f' () ;
  assert p'