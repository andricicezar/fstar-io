module FancyTraces_Ints

open FStar.Tactics
open FStar.List.Tot
open FStar.Classical.Sugar
open FStar.Ghost

noeq
type promise (a:Type0) : Type0 =
| Promise : id:erased nat -> r:erased a -> promise a

noeq
type event (e: Type0) =
| Ev : e -> event e
| EAsync : #b:Type0 -> promise b -> trace e -> event e
| EAwait : #b:Type0 -> promise b -> event e
and trace e = list (event e)

type w_post (a:Type) = trace int -> a -> Type0
type w_pre = trace int -> Type0
type w0 (a:Type) = w_post a -> w_pre

unfold
let w_post_ord (#a:Type) (p1 p2:w_post a) =
  forall lt (r:a). p1 lt r ==> p2 lt r

unfold
let w_monotonic (#a:Type) (wp:w0 a) =
  forall (p1 p2:w_post a). (p1 `w_post_ord` p2) ==> (forall h. wp p1 h ==> wp p2 h)

type w (a:Type) = wp:(w0 a){w_monotonic wp}

unfold
let (⊑) (#a:Type) (wp1:w a) (wp2:w a) =
  forall (p:w_post a) h. wp2 p h ==> wp1 p h

unfold
let (≡) (wp1:w 'a) (wp2:w 'a) =
  wp1 ⊑ wp2 /\ wp2 ⊑ wp1

let w_subcomp (#a:Type) (wp:w a) (p1 p2:w_post a) (h:trace int) :
  Lemma (requires (wp p1 h /\ p1 `w_post_ord` p2))
        (ensures (wp p2 h)) = ()

let w_return (#a:Type) (x:a) : w a =
  fun p _ -> p [] x

let w_post_shift (p:w_post 'b) (lt:trace int) : w_post 'b =
  fun lt' r' -> p (lt@lt') r'

unfold
let w_post_bind
  (#a:Type u#a) (#b:Type u#b)
  (h:trace int)
  (kw : a -> w b)
  (p:w_post b) :
  Tot (w_post a) =
  fun lt (x:a) ->
    kw x (w_post_shift p lt) (h@lt) (** Having local trace separate from the history helps with interleavings **)

let w_bind (#a:Type u#a) (#b:Type u#b) (wp : w a) (kwp : a -> w b) : w b =
  fun p h -> wp (w_post_bind h kwp p) h

let w_bind_subcomp (wp1:w 'a) (wp2:'a -> w 'b) (wp3:'a -> w 'b) :
  Lemma
    (requires ((forall x. wp2 x ≡ wp3 x)))
    (ensures (w_bind wp1 wp2 ≡ w_bind wp1 wp3)) = ()

let __iff_refl a : Lemma (a <==> a) = ()
let w_law1 (x:'a) (k:'a -> w 'b) : Lemma (w_bind (w_return x) k ≡ k x) = ()

let w_law2 (m:w 'a) : Lemma (w_bind m w_return ≡ m) = ()
let w_law3 (m:w 'a) (g:'a -> w 'b) (k:'b -> w 'c) : Lemma (w_bind (w_bind m g) k ≡ w_bind m (fun x -> w_bind (g x) k)) =
  let lhs = w_bind m (fun r1 -> w_bind (g r1) k) in
  let rhs = w_bind (w_bind m g) k in
  let pw (p : w_post 'c) h : Lemma (lhs p h <==>  rhs p h) =
    assert (lhs p h <==> rhs p h) by begin
      unfold_def (`w_bind);
      norm [];
      l_to_r [`List.Tot.Properties.append_assoc];
      mapply (`__iff_refl)
    end
  in
  Classical.forall_intro_2 pw

noeq
type free (a:Type u#a) : Type u#(max 1 a) =
| Require : (pre:pure_pre) -> k:((squash pre) -> free u#a a) -> free a
| Return : a -> free a
| Print : (arg:int) -> cont:(unit -> free u#a a) -> free a
| Async : #c:Type u#0 -> free (Universe.raise_t u#0 u#a c) -> k:(promise c -> free u#a a) -> free a
| Await : #c:Type u#0 -> promise c -> k:(c -> free u#a a) -> free a

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
  | Print str k ->
      Print str (fun i -> free_bind (k i) cont)
  | Async f k ->
      Async
        (free_bind f (fun x -> free_return (Universe.raise_val u#0 u#b (Universe.downgrade_val x))))
        (fun x -> free_bind (k x) cont)
  | Await pr k ->
      Await pr (fun x -> free_bind (k x) cont)

let w_require (pre:pure_pre) : w (squash pre) =
  let wp' : w0 (squash pre) = fun p h -> pre /\ p [] () in
  wp'

unfold
let w_print (ev:int) : w unit =
  fun p _ -> p [Ev ev] ()

unfold let async_event (pr:promise 'a) (asynced_lt:trace 'e) : trace 'e = [EAsync pr asynced_lt]

type wst a = s0:nat -> w (nat * a) // {s0 <= s1}
let wst_return #a x : wst a = fun s0 -> w_return (s0, x)
let wst_bind #a (m:wst a) #b (k:a -> wst b) : wst b =
  fun s0 -> w_bind #(nat * a) #(nat * b) (m s0) (fun (s1, r) -> k r s1)

unfold let w_async0 (#a:Type0) (wf:wst (Universe.raise_t u#0 u#c a)) : wst (promise a) =
  wst_bind wf (fun r s1 -> w_return #_ (s1+1, (Promise (s1+1) (hide (Universe.downgrade_val r)))))

let wst_async #a (wf:wst (Universe.raise_t a)) : wst (promise a) =
  fun s0 p h -> w_async0 wf s0 (fun ltf (s1, pr) -> p (async_event pr ltf) (s1, pr)) h

let w_await (pr:promise 'a) : w 'a =
  fun p h -> p [EAwait pr] (reveal (Promise?.r pr))

val theta : (#a:Type) -> free a -> wst a
let rec theta m = fun s0 ->
  match m with
  | Require pre k ->
      w_bind (w_require pre) (fun r -> theta (k r) s0)
  | Return x -> w_return (s0, x)
  | Print arg k ->
      w_bind (w_print arg) (fun r -> theta (k r) s0)
  | Async f k ->
      w_bind (wst_async (theta f) s0) (fun (s1, pr) -> theta (k pr) s1)
  | Await pr k ->
      w_bind (w_await pr) (fun r -> theta (k r) s0)

let theta_monad_morphism_ret (v:'a) (s0:nat) :
  Lemma (theta (free_return v) s0 == w_return (s0, v)) = ()

unfold val theta' : (#a:Type) -> free a -> nat -> w a
let theta' #a m s0 =
  w_bind (theta m s0) (fun (s1, x) -> w_return #a x)

let lemma_wp_drop_state (wp:w (nat * 'a)) p h : Lemma (
   w_bind wp (fun (_, x) -> w_return x) p h <==> wp (fun lt (_, rf) -> p lt rf) h) = ()

let lemma_theta_theta'0 (m:free 'a) s0 p h : Lemma (
   theta' m s0 p h <==> theta m s0 (fun lt (s1, rf) -> p lt rf) h) =
   lemma_wp_drop_state (theta m s0) p h

let lemma_theta_theta' (m:free 'a) : Lemma (
   forall s0 p h. theta' m s0 p h <==> theta m s0 (fun lt (s1, rf) -> p lt rf) h) =
   Classical.forall_intro_3 (lemma_theta_theta'0 m)

let dm (a:Type u#a) (wp:w a) =
  m:(free a){forall s0. theta' m s0 ⊑ wp}

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
  let m = free_bind c kc in
  admit ();
 // lemma_better wp kwp c kc;
 // theta_monad_morphism_bind c kc;
 // assert (forall s0. w_bind (theta c s0) (fun (s1, x) -> theta (kc x) s1) ⊑ theta m s0);
 // assert (forall s0. w_bind wp kwp ⊑ theta' m s0);
  m

let dm_subcomp
  (a:Type u#a)
  (wp1:w a)
  (wp2:w a)
  (c:dm a wp1) :
  Pure (dm a wp2)
    (requires (wp1 ⊑ wp2))
    (ensures (fun _ -> True)) =
    c

unfold
let w_if_then_else (#a:Type) (wp1 wp2:w a) (b:bool) : w a =
  fun p h -> (b ==> wp1 p h) /\ ((~b) ==> wp2 p h)

let dm_if_then_else (a : Type u#a)
  (wp1 wp2: w a) (f : dm a wp1) (g : dm a wp2) (b : bool) : Type =
  dm a (w_if_then_else wp1 wp2 b)

let dm_require
  (pre:pure_pre) : dm (squash pre) (w_require pre) =
  let m = Require pre (Return) in
  assert (forall s0. (theta' m s0) ⊑ (w_require pre) ) by (compute ());
  m

let dm' (a:Type u#a) (wp:w a) = dm a wp
let dm_return' (a:Type u#a) (x:a) : dm' a (w_return x) =
  dm_return a x
let dm_bind'
  (a:Type u#a)
  (b:Type u#b)
  (wp:w a)
  (kwp:a -> w b)
  (c:dm' a wp)
  (kc:(x:a -> dm' b (kwp x))) :
  dm' b (w_bind wp kwp) =
  dm_bind a b wp kwp c kc

let dm_subcomp'
  (a:Type u#a)
  (wp1:w a)
  (wp2:w a)
  (c:dm' a wp1) :
  Pure (dm' a wp2)
    (requires (wp1 ⊑ wp2))
    (ensures (fun _ -> True)) =
 dm_subcomp a wp1 wp2 c

let dm_if_then_else' (a : Type u#a)
  (wp1 wp2: w a) (f : dm' a wp1) (g : dm' a wp2) (b : bool) : Type =
  dm_if_then_else a wp1 wp2 f g b

total
reflectable
reifiable
effect {
  CyWP (a:Type) (wp : w a)
  with {
       repr       = dm'
     ; return     = dm_return'
     ; bind       = dm_bind'
     ; subcomp    = dm_subcomp'
     ; if_then_else = dm_if_then_else'
     }
}

unfold
let wp_lift_pure (wp : pure_wp 'a) : w 'a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fun p _ -> wp (fun r -> p [] r)

let lift_pure_dm
  (a : Type u#a)
  (wp : pure_wp a)
  (f:(eqtype_as_type unit -> PURE a wp)) :
  dm' a (wp_lift_pure wp) =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs = dm_require (as_requires wp) in
  let rhs = (fun (pre:(squash (as_requires wp))) -> dm_return a (f pre)) in
  let m = dm_bind _ _ _ _ lhs rhs in
  dm_subcomp _ _ _ m

sub_effect PURE ~> CyWP = lift_pure_dm

effect Cy
  (a:Type)
  (pre : trace int -> Type0)
  (post : trace int -> a -> trace int -> Type0) =
  CyWP a (fun p h -> pre h /\ (forall lt r. post h r lt ==> p lt r))

(** *** Tests partiality of the effect **)
let test_using_assume (fd:int) : Cy int (requires (fun h -> True)) (ensures fun h r lt -> fd % 2 == 0) =
  assume (fd % 2 == 0) ;
  fd

// A second test to make sure exfalso isn't used
let test_assume #a #pre (f : unit -> Cy a (requires (fun _ -> pre)) (ensures fun _ _ _ -> True)) : Cy a (fun _ -> True) (fun _ _ _ -> True) =
  assume pre ;
  f ()

let test_assert p : Cy unit (requires (fun _ -> p)) (ensures fun _ _ _ -> True) =
  assert p

let partial_match (l : list nat) : Cy unit (requires (fun _ -> l <> [])) (ensures fun _ _ _ -> True) =
  match l with
  | x :: r -> ()

let partial_match_io (l : list int) : Cy int (requires fun _ -> l <> []) (ensures fun _ _ _ -> True) =
  match l with
  | s :: _ -> s + 10

// Cezar's tests

assume val p : prop
assume val p' : prop
assume val pure_lemma (_ : unit) : Lemma (ensures (p))
assume val some_f (_ : squash p) : Cy unit (requires fun _ -> True) (ensures fun _ _ _ -> True)
assume val some_f' : unit -> Cy unit (requires fun _ -> p) (ensures fun _ _ _ -> p')

let pure_lemma_test () : Cy unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  pure_lemma ();
  some_f ()

let pure_lemma_test2 () : Cy unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  pure_lemma ();
  some_f ();
  some_f' ();
  assert p'

(** *** DONE with tests of partiality **)
