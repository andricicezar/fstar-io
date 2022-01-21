(** This is a test towards general partial Dijkstra monads

    Here we build on the example of the ND effect
*)

module ND

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics
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

let wpre = prop
let wpost a = a -> prop

let wp a = wpost a -> wpre

let wle #a (w1 w2 : wp a) =
  forall x. w2 x ==> w1 x

let w_return #a (x : a) : wp a =
  fun post -> post x

let w_bind #a #b (w : wp a) (wf : a -> wp b) : wp b =
  fun post -> w (fun x -> wf x post)

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
