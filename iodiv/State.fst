module State

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc

(** Computational monad *)

assume val state : Type

let m a = state -> state * a

let m_return #a (x : a) : m a =
  fun s -> (s, x)

let m_bind #a #b (c : m a) (f : a -> m b) : m b =
  fun s0 ->
    let (s1, x) = c s0 in
    f x s1

(** Specification monad *)

let w_pre = state -> Type0
let w_post a = state -> a -> Type0

let wp a = w_post a -> w_pre

unfold
let _wle #a (w1 w2 : wp a) =
  forall post s. w2 post s ==> w1 post s

let wle #a (w1 w2 : wp a) =
  _wle w1 w2

unfold
let _w_return #a (x : a) : wp a =
  fun post s0 -> post s0 x

let w_return #a (x : a) : wp a =
  _w_return x

unfold
let _w_bind #a #b (w : wp a) (wf : a -> wp b) : wp b =
  fun post -> w (fun s1 x -> wf x post s1)

let w_bind #a #b (w : wp a) (wf : a -> wp b) : wp b =
  _w_bind w wf

(** Effect observation *)

let theta #a (c : m a) : wp a =
  fun post s0 -> let (s1, x) = c s0 in post s1 x

let theta_bind #a #b (c : m a) (f : a -> m b) :
  Lemma (theta (m_bind c f) `wle` w_bind (theta c) (fun x -> theta (f x)))
= ()

(** Dijkstra monad *)

let dm a w =
  c : m a { theta c `wle` w }

let d_return #a (x : a) =
  m_return x

let d_bind #a #b #w #wf (c : dm a w) (f : (x:a) -> dm b (wf x)) : dm b (w_bind w wf) =
  m_bind c f

(** Partial Dijkstra monad *)

let pdm a (w : wp a) =
  pre : pure_pre { forall post s0. w post s0 ==> pre } & (squash pre -> dm a w)

let get_pre #a #w (t : pdm a w) : Pure pure_pre (requires True) (ensures fun r -> forall post s0. w post s0 ==> r) =
  let (| pre , f |) = t in pre

let get_fun #a #w (t : pdm a w) : Pure (dm a w) (requires get_pre t) (ensures fun _ -> True) =
  let (| pre, f |) = t in f ()

let return a (x : a) : pdm a (_w_return x) =
  (| True , (fun _ -> d_return x) |)

(* Trying to find the right pre for bind to see what is missing *)
let bind_pre #a #b #w #wf (c : pdm a w) (f : (x:a) -> pdm b (wf x)) : pure_pre =
  get_pre c /\ (exists s0. let (s1, x) = get_fun c s0 in get_pre (f x))

let w_bind_pre #a #b #w #wf (c : pdm a w) (f : (x:a) -> pdm b (wf x)) :
  Lemma (forall post s0. _w_bind w wf post s0 ==> bind_pre c f)
= introduce forall post s0. _w_bind w wf post s0 ==> bind_pre c f
  with begin
    introduce _w_bind w wf post s0 ==> bind_pre c f
    with _. begin
      assert (w (fun s1 x -> wf x post s1) s0) ;
      assert (get_pre c) ;
      // Now for the continuation, let's use theta
      assert (theta (get_fun c) (fun s1 x -> wf x post s1) s0) ;
      assert (let (s1, x) = (get_fun c) s0 in (fun s1 x -> wf x post s1) s1 x) ;
      assert (let (s1, x) = (get_fun c) s0 in wf x post s1) ;
      let (s1, x) = get_fun c s0 in
      assert (wf x post s1) ;
      assert (get_pre (f x)) ; // The problem is that here the x is not arbitrary!
      // It makes me want to use m_bind in the definition of bind_pre with the hope
      // that we can somehow prove something about m_bind externally
      // currently it gets us return_of again...
      assert (bind_pre c f)
    end
  end

let bind_pre_left #a #b #w #wf (c : pdm a w) (f : (x:a) -> pdm b (wf x)) :
  Lemma (bind_pre c f ==> get_pre c)
= ()

// This one is the problem because we don't know anything about x!
let bind_pre_right #a #b #w #wf (c : pdm a w) (f : (x:a) -> pdm b (wf x)) (x : a) :
  Lemma (bind_pre c f ==> get_pre (f x))
= admit ()

let bind a b w wf (c : pdm a w) (f : (x:a) -> pdm b (wf x)) : pdm b (_w_bind w wf) =
  w_bind_pre c f ;
  bind_pre_left c f ;
  forall_intro (bind_pre_right c f) ;
  (| bind_pre c f , (fun _ -> d_bind (get_fun c) (fun x -> get_fun (f x))) |)
