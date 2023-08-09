module Pure_Async_Await

open FStar.Tactics
open FStar.List.Tot.Base

type w_post (a:Type) = a -> Type0
type w_pre = Type0

type w0 (a:Type) = w_post a -> w_pre

unfold
let w_post_ord (#a:Type) (p1 p2:w_post a) = forall (r:a). p1 r ==> p2 r

let w_monotonic (#a:Type) (wp:w0 a) =
  forall (p1 p2:w_post a). (p1 `w_post_ord` p2) ==> (wp p1 ==> wp p2)

type w (a:Type) = wp:(w0 a){w_monotonic wp}

let w_ord (#a:Type) (wp1:w a) (wp2:w a) = forall (p:w_post a). wp1 p ==> wp2 p
unfold let (⊑) = w_ord

let w_return (#a:Type) (x:a) : w a =
  (fun p -> p x)

let w_bind (#a:Type u#a) (#b:Type u#b) (wp : w a) (kwp : a -> w b) : w b =
  fun (p:w_post b) -> wp (fun (x:a) -> kwp x p)

type promise (a:Type) = | Promise : v:a -> promise a

noeq
type free (a:Type u#a) : Type u#(max 1 a) =
| Require : (pre:pure_pre) -> k:((squash pre) -> free u#a a) -> free a
| Return : a -> free a
| Async : #c:Type u#0 -> free (Universe.raise_t c) -> k:(promise c -> free u#a a) -> free a
| Await : #c:Type u#0 -> promise c -> k:(c -> free a) -> free a

let free_return (#a:Type) (x:a) : free a =
  Return x

let rec free_bind
  (#a:Type u#a)
  (#b:Type u#b)
  (l : free a)
  (cont : a -> free b) :
  free b =
  match l with
  | Require pre k ->
      Require pre (fun _ -> free_bind (k ()) cont)
  | Return x -> cont x
  | Async f k ->
      Async 
        (free_bind f (fun x -> free_return (Universe.raise_val u#0 u#b (Universe.downgrade_val x))))
        (fun x -> free_bind (k x) cont)
  | Await pr k ->
      Await pr (fun x -> free_bind (k x) cont)

let w_require (pre:pure_pre) : w (squash pre) = 
  let wp' : w0 (squash pre) = fun p -> pre /\ p () in
  assert (forall post1 post2. (w_post_ord post1 post2 ==> (wp' post1 ==> wp' post2)));
  assert (w_monotonic wp');
  wp'

val theta : (#a:Type) -> free a -> w a
let rec theta m =
  match m with
  | Require pre k ->
      w_bind (w_require pre) (fun r -> theta (k r))
  | Return x -> w_return x
  | Async f k ->
      w_bind (theta f) (fun rf -> theta (k (Promise (Universe.downgrade_val rf))))
  | Await pr k -> theta (k (Promise?.v pr))

let theta_monad_morphism_ret (v:'a) :
  Lemma (theta (free_return v) == w_return v) = ()

let theta_lax_monad_morphism_bind (m:free 'a) (km:'a -> free 'b) :
  Lemma (w_bind (theta m) (fun x -> theta (km x)) ⊑ theta (free_bind m km)) = admit ()

let dm (a:Type u#a) (wp:w a) =
  m:(free a){wp ⊑ theta m}

let dm_return (a:Type u#a) (x:a) : dm a (w_return x) =
  Return x

let dm_bind
  (a:Type u#a)
  (b:Type u#b)
  (wp:w a)
  (kwp:a -> w b)
  (c:dm a wp)
  (kc:(x:a -> dm b (kwp x))) :
  dm b (w_bind wp kwp) =
  theta_lax_monad_morphism_bind c kc;
  free_bind c kc

let dm_subcomp
  (a:Type u#a)
  (wp1:w a)
  (wp2:w a)
  (c:dm a wp1) :
  Pure (dm a wp2)
    (requires (wp2 ⊑ wp1))
    (ensures (fun _ -> True)) =
    c 

let w_if_then_else (wp1 wp2:w 'a) (b:bool) : w 'a =
  fun p -> (b ==> wp1 p) /\ ((~b) ==> wp2 p)

let dm_if_then_else (a : Type u#a) 
  (wp1 wp2: w a) (f : dm a wp1) (g : dm a wp2) (b : bool) : Type =
  dm a (w_if_then_else wp1 wp2 b)

let dm_partial_return
  (pre:pure_pre) : dm (squash pre) (w_require pre) =
  let m = Require pre (Return) in
  assert (w_require pre ⊑ theta m);
  m

let lift_pure_w (#a:Type) (wp : pure_wp a) : w a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  (fun (p:w_post a) -> wp (fun (r:a) -> p r))

let lift_pure_w_as_requires (wp : pure_wp 'a) :
  Lemma (forall (p:w_post 'a) h. lift_pure_w wp p ==> as_requires wp) =
    assert (forall (p:w_post 'a) x. p x ==> True) ;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    assert (forall (p:w_post 'a). wp (fun x -> p x) ==> wp (fun _ -> True))

[@"opaque_to_smt"]
let lift_pure_dm 
  (a : Type u#a) 
  (wp : pure_wp a)
  (f:(eqtype_as_type unit -> PURE a wp)) : 
  dm a (lift_pure_w wp) =
  lift_pure_w_as_requires #a wp;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs = dm_partial_return (as_requires wp) in
  let rhs = (fun (pre:(squash (as_requires wp))) -> dm_return a (f ())) in
  let m = dm_bind _ _ _ _ lhs rhs in
  dm_subcomp a _ (lift_pure_w wp) m
  
reflectable
reifiable
total
effect {
  CyWP (a:Type) (wp : w a)
  with {
       repr       = dm
     ; return     = dm_return
     ; bind       = dm_bind
     ; subcomp    = dm_subcomp
     ; if_then_else = dm_if_then_else
     }
}

sub_effect PURE ~> CyWP = lift_pure_dm

effect Cy
  (a:Type)
  (pre : Type0)
  (post : a -> Pure Type0 (requires pre) (ensures (fun _ -> True))) =
  CyWP a (fun p -> pre /\ (forall r. post r ==> p r))

(** *** Tests partiality of the effect **)
let test_using_assume (fd:int) : Cy int (requires True) (ensures fun r -> fd % 2 == 0) =
  assume (fd % 2 == 0) ;
  fd

// A second test to make sure exfalso isn't used
let test_assume #a #pre (f : unit -> Cy a (requires pre) (ensures fun r -> True)) : Cy a True (fun r -> True) =
  assume pre ;
  f ()

let test_assert p : Cy unit (requires p) (ensures fun r -> True) =
  assert p

let partial_match (l : list nat) : Cy unit (requires l <> []) (ensures fun r -> True) =
  match l with
  | x :: r -> ()

let partial_match_io (l : list int) : Cy int (requires l <> []) (ensures fun r -> True) =
  match l with
  | s :: _ -> s + 10 

let partial_match_pre (l : list nat) : Cy nat (requires l <> []) (ensures fun r -> r == hd l) =
  match l with
  | x :: r -> x

// Cezar's tests

assume val p : prop
assume val p' : prop
assume val pure_lemma (_ : unit) : Lemma p
assume val some_f (_ : squash p) : Cy unit (requires True) (ensures fun _ -> True)
assume val some_f' : unit -> Cy unit (requires p) (ensures fun _ -> p')

// TODO: why is this failing?
let pure_lemma_test () : Cy unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;
  some_f ()

let pure_lemma_test2 () : Cy unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;
  some_f () ;
  some_f' () ;
  assert p'
(** *** DONE with tests of partiality **)


let true_wp (#a:Type) : w a = fun p -> forall r. p r

let raise_w (wp:w 'a) : w (Universe.raise_t 'a) =
  let wp' = (fun p -> wp (fun r -> p (Universe.raise_val r))) in
  assume (w_monotonic wp');
  wp'

let async0 (#a:Type) (#pre:w_pre) (#post:w_post a) ($f:unit -> Cy a pre post) : dm (promise a) (fun p -> pre /\ (forall r. post (Promise?.v r) ==> p r)) =
  let f' : free a = reify (f ()) in
  let f'' : free (Universe.raise_t a) = free_bind f' (fun x -> free_return (Universe.raise_val x)) in
  let m : free (promise a) = Async f'' free_return in
  assume ((fun p -> pre /\ (forall r. post (Promise?.v r) ==> p r)) ⊑ theta m);
  m

[@"opaque_to_smt"]
let async (#a:Type) (#pre:w_pre) (#post:w_post a) ($f:unit -> Cy a pre post) : Cy (promise a) pre (fun r -> post (Promise?.v r)) =
  CyWP?.reflect (async0 f)

[@"opaque_to_smt"]
let await (#a:Type) (pr:promise a) : Cy a True (fun r -> Promise?.v pr == r) =
  CyWP?.reflect (Await pr (free_return))

let return (#a:Type) (x:a) () : Cy a True (fun r -> r == x) = x

let test () : Cy int True (fun r -> True) = //r == 5)=
  let prx = async (return 2) in
  assert (Promise?.v prx == 2) by (dump "H"); 
  let pry = async (return 3) in
 // assert (Promise?.v prx+ Promise?.v pry == 5) by (dump "h");
  let x : int = await prx in
  let y : int = await pry in
  x + y

