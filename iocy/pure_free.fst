module Pure_Free

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

unfold
let w_ord0 (#a:Type) (wp1:w a) (wp2:w a) = forall (p:w_post a). wp1 p ==> wp2 p

let w_ord = w_ord0
unfold let (⊑) = w_ord

unfold
let w_return0 (#a:Type) (x:a) : w a = fun p -> p x
let w_return = w_return0

unfold
let w_bind0 (#a:Type u#a) (#b:Type u#b) (wp : w a) (kwp : a -> w b) : w b =
  fun (p:w_post b) -> wp (fun (x:a) -> kwp x p)
let w_bind = w_bind0
  
noeq
type free (a:Type u#a) : Type u#(max 1 a) =
| Require : (pre:pure_pre) -> k:((squash pre) -> free u#a a) -> free a
| Return : a -> free a

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

let w_require (pre:pure_pre) : w (squash pre) = 
  let wp' : w0 (squash pre) = fun p -> pre /\ p () in
  assert (forall (post1 post2:w_post (squash pre)). (w_post_ord post1 post2 ==> (wp' post1 ==> wp' post2)));
  assert (w_monotonic wp');
  wp'

val theta : (#a:Type) -> free a -> w a
let rec theta m =
  match m with
  | Require pre k ->
      w_bind (w_require pre) (fun r -> theta (k r))
  | Return x -> w_return x

let theta_monad_morphism_ret (v:'a) :
  Lemma (theta (free_return v) == w_return v) = ()

let theta_lax_monad_morphism_bind (m:free 'a) (km:'a -> free 'b) :
  Lemma (w_bind (theta m) (fun x -> theta (km x)) ⊑ theta (free_bind m km)) = 
  match m with
  | Return x -> ()
  | Require pre k -> admit ()
      

let dm (a:Type u#a) (wp:w a) =
  m:(free a){wp ⊑ theta m}

let dm_return (a:Type u#a) (x:a) : dm a (w_return0 x) =
  Return x

let dm_bind
  (a:Type u#a)
  (b:Type u#b)
  (wp:w a)
  (kwp:a -> w b)
  (c:dm a wp)
  (kc:(x:a -> dm b (kwp x))) :
  dm b (w_bind0 wp kwp) =
  theta_lax_monad_morphism_bind c kc;
  free_bind c kc

let dm_subcomp
  (a:Type u#a)
  (wp1:w a)
  (wp2:w a)
  (c:dm a wp1) :
  Pure (dm a wp2)
    (requires (wp2 `w_ord0` wp1))
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

unfold
let lift_pure_w (#a:Type) (wp : pure_wp a) : w a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  wp
  //(fun (p:w_post a) -> wp (fun (r:a) -> p r))

let lift_pure_w_as_requires (#a:Type) (wp : pure_wp a) :
  Lemma (forall (p:w_post a) h. lift_pure_w wp p ==> as_requires wp) =
    assert (forall (p:w_post a) x. p x ==> True) ;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    assert (forall (p:w_post a). wp (fun x -> p x) ==> wp (fun _ -> True))

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
  FreeWP (a:Type) (wp : w a)
  with {
       repr       = dm
     ; return     = dm_return
     ; bind       = dm_bind
     ; subcomp    = dm_subcomp
     ; if_then_else = dm_if_then_else
     }
}

sub_effect PURE ~> FreeWP = lift_pure_dm

effect Free
  (a:Type u#a)
  (pre : Type0)
  (post : a -> Pure Type0 (requires pre) (ensures (fun _ -> True))) =
  FreeWP a (fun p -> pre /\ (forall (r:a). post r ==> p r))

(** *** Tests partiality of the effect **)
let test_using_assume (fd:int) : Free int (requires True) (ensures fun r -> fd % 2 == 0) =
  assume (fd % 2 == 0) ;
  fd

// A second test to make sure exfalso isn't used
let test_assume #a #pre (f : unit -> Free a (requires pre) (ensures fun r -> True)) : Free a True (fun r -> True) =
  assume pre ;
  f ()

let test_assert p : Free unit (requires p) (ensures fun r -> True) =
  assert p

let partial_match (l : list nat) : Free unit (requires l <> []) (ensures fun r -> True) =
  match l with
  | x :: r -> ()

let partial_match_io (l : list int) : Free int (requires l <> []) (ensures fun r -> True) =
  match l with
  | s :: _ -> s + 10 

let partial_match_pre (l : list nat) : Free nat (requires l <> []) (ensures fun r -> r == hd l) =
  match l with
  | x :: r -> x

assume val p : prop
assume val p' : prop
assume val pure_lemma (_ : unit) : Lemma p
assume val some_f (_ : squash p) : Free unit (requires True) (ensures fun _ -> True)
assume val some_f' : unit -> Free unit (requires p) (ensures fun _ -> p')

// TODO: why is this failing?
let pure_lemma_test () : Free unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;
  some_f ()

// TODO: why is this failing?
let pure_lemma_test2 () : Free unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;
  some_f () ;
  some_f' () ;
  assert p'
