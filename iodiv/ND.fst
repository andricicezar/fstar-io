(** This is a test towards general partial Dijkstra monads

    Here we build on the example of the ND effect
*)

module ND

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics // Also defines forall_intro so place before Classical
open FStar.Classical


let m a = list a

let m_return #a (x : a) : m a =
  [ x ]

let return_of #a (x : a) (c : m a) =
  x `memP` c

unfold
let ret #a (c : m a) =
  x : a { x `return_of` c }

(* Can't be concatMap because of the refinement *)
let rec m_bind #a #b (c : m a) (f : ret c -> m b) : m b =
  match c with
  | [] -> []
  | x :: l -> f x @ m_bind l f

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
  fun post -> w (fun x -> post x)

let wforget #a #c (w : wp (ret c)) : wp a =
  wcast (fun x -> x `return_of` c) (fun x -> True) w


let theta #a (c : m a) : wp (ret c) =
  fun post -> forall x. x `memP` c ==> post x

let dm a (w : wp a) =
  c : m a { wforget (theta c) `wle` w }

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
  | [] -> ()
  | e :: l ->
    eliminate x == e \/ x `memP` l
    returns forall y. y `return_of` f x ==> y `return_of` m_bind c f
    with _. ()
    and _. return_of_bind l f x

let rec memP_bind_inv #a #b (c : m a) (f : ret c -> m b) y :
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
let wprepost #a (pre : Type0) (post : a -> Type0) : wp a =
  fun p -> pre /\ (forall x. post x ==> p x)

effect ND (a : Type) (pre : Type0) (post : a -> Type0) =
  NDw a (wprepost pre post)

(** Some tests for ND *)

let test_assert p : ND unit (requires p) (ensures fun r -> True) =
  assert p

let partial_match (l : list nat) : ND unit (requires l <> []) (ensures fun r -> True) =
  match l with
  | x :: r -> ()

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
