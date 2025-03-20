module FancyTraces_Ints

open FStar.Tactics
open FStar.List.Tot
open FStar.Classical.Sugar
open FStar.Ghost

noeq
type promise (e:Type0) (a:Type0) : Type u#1 =
| Promise : id:erased nat -> lt:erased (trace e) -> r:erased a -> promise e a
and event (e: Type0) : Type u#1 =
| Ev : e -> event e
| EAsync : #b:Type0 -> pr:promise e b -> event e
| EAwait : #b:Type0 -> pr:promise e b -> event e
and trace e : Type u#1 = list (event e)

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
  forall p h. wp2 p h ==> wp1 p h

unfold
let (≡) (wp1:w 'a) (wp2:w 'a) =
  wp1 ⊑ wp2 /\ wp2 ⊑ wp1

let w_subcomp (#a:Type) (wp:w a) (p1 p2:w_post a) (h:trace int) :
  Lemma (requires (wp p1 h /\ p1 `w_post_ord` p2))
        (ensures (wp p2 h)) = ()

unfold
let w_return (#a:Type) (x:a) : w a =
  fun p _ -> p [] x

unfold
let w_post_shift (p:w_post 'b) (lt:trace int) : w_post 'b =
  fun lt' r' -> p (lt@lt') r'

unfold
let w_post_bind
  (#a:Type) (#b:Type)
  (h:trace int)
  (kw : a -> w b)
  (p:w_post b) :
  Tot (w_post a) =
  fun lt (x:a) ->
    kw x (w_post_shift p lt) (h@lt) (** Having local trace separate from the history helps with interleavings **)

unfold
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
| Async : #c:Type u#0 -> free (Universe.raise_t u#0 u#a c) -> k:(promise int c -> free u#a a) -> free a
| Await : #c:Type u#0 -> promise int c -> k:(c -> free u#a a) -> free a

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

unfold
let w_require (pre:pure_pre) : w (squash pre) =
  let wp' : w0 (squash pre) = fun p h -> pre /\ p [] () in
  wp'

unfold
let w_print (ev:int) : w unit =
  fun p _ -> p [Ev ev] ()

unfold let async_event (pr:promise 'e 'a) : trace 'e = [EAsync pr]

type wst a = s0:nat -> w (nat * a) // {s0 <= s1}
let wst_return #a x : wst a = fun s0 -> w_return (s0, x)
let wst_bind #a (m:wst a) #b (k:a -> wst b) : wst b =
  fun s0 -> w_bind #(nat * a) #(nat * b) (m s0) (fun (s1, r) -> k r s1)

unfold let w_async0 (#a:Type0) (wf:wst (Universe.raise_t u#0 u#c a)) : wst (promise int a) =
 fun s0 (p:w_post (nat * promise int a)) h -> wf s0 (fun lt (s1, r) -> p [] (s1+1, Promise (s1+1) lt (hide (Universe.downgrade_val r)))) h
 // wst_bind wf (fun r s1 -> w_return #_ (s1+1, (Promise (s1+1) (hide (Universe.downgrade_val r)))))

let wst_async #a (wf:wst (Universe.raise_t a)) : wst (promise int a) =
  fun s0 p h -> w_async0 wf s0 (fun ltf (s1, pr) -> p (async_event pr) (s1, pr)) h

let w_await (pr:promise int 'a) : w 'a =
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
  Lemma (theta (free_return v) s0 == w_return (s0, v)) by (compute ())= ()

val theta' : (#a:Type) -> free a -> nat -> w a
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
  assert (forall s0. (theta' m s0) ⊑ (w_require pre) );
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

let print (e:int) : Cy unit (fun _ -> True) (fun _ () lt -> lt == [Ev e]) by (
  compute ()
) =
  CyWP?.reflect (Print e (Return))

let raise_w (#a:Type u#a) (wp:w a) : w (Universe.raise_t u#a u#b a) =
  w_bind wp (fun r -> w_return (Universe.raise_val r))
//  fun p h -> wp (fun lt r -> p lt (Universe.raise_val u#a u#b r)) h

[@"opaque_to_smt"]
let async00 (#a:Type u#a) (#wp:w a) ($f:unit -> CyWP a wp) : dm (Universe.raise_t u#a u#b a) (raise_w u#a u#b wp)  =
  let f' : dm a wp = reify (f ()) in
  dm_subcomp _ _ _ (dm_bind _ _ _ _ f' (fun x -> dm_return _ (Universe.raise_val u#a u#b x)))

  (**
let async_spec_implies_theta
  (#a:Type)
  (pre:w_pre) (post:trace int -> a -> trace int -> Type0)
  (f:dm (Universe.raise_t a) (fun p h -> pre h /\ (forall r lt. post h r lt ==> p lt (Universe.raise_val r)))) :
  Lemma (
    forall s0.
    (fun p h -> pre h /\ (forall pr lt. post h (Promise?.r pr) lt ==> p (async_event (Promise?.id pr) lt) pr))
    ⊑
    theta' (Async f free_return) s0) =
  introduce forall s0 (p:w_post (promise a)) h. (pre h /\ (forall pr lt. post h (Promise?.r pr) lt ==> p (async_event (Promise?.id pr) lt) pr) ==>
       theta' (Async f free_return) s0 p h) with begin
       introduce (pre h /\ (forall pr lt. post h (Promise?.r pr) lt ==> p (async_runtree (Promise?.id pr) lt) pr)) ==>
       theta' (Async f free_return) s0 p h with hyp. begin
         let p' : w_post (Universe.raise_t a) = (fun ltf rf -> p (async_runtree (s0+1) ltf) (Promise (s0+1) (Universe.downgrade_val rf))) in
         let _:squash (theta f (s0+1) (fun ltf (s1, rf) -> p' ltf rf) h) = begin
            assert (forall (p':w_post (Universe.raise_t a)). pre h /\ (forall r lt. post h r lt ==> p' lt (Universe.raise_val r)) ==> theta' f (s0+1) p' h);
            lemma_theta_theta' f;
            assert (forall s0 p h. theta' f s0 p h <==> theta f s0 (fun lt (s1, rf) -> p lt rf) h);
            eliminate forall p'. pre h /\ (forall r lt. post h r lt ==> p' lt (Universe.raise_val r)) ==> theta f (s0+1) (fun lt (s1, rf) -> p' lt rf) h with p';
            introduce forall r lt. post h r lt ==> p' lt (Universe.raise_val r) with begin
              eliminate forall pr. (forall lt. post h (Promise?.r pr) lt ==> p (async_runtree (Promise?.id pr) lt) pr) with (Promise (s0+1) r);
              eliminate forall lt. post h r lt ==> p (async_runtree (s0+1) lt) (Promise (s0+1) r) with lt
            end;
            assert (theta f (s0+1) (fun ltf (s1, rf) -> p' ltf rf) h)
         end in
         let _:squash (theta (Async f free_return) s0 (fun lt (s1, pr) -> p lt pr) h) = begin
            calc (==>) {
            theta f (s0+1) (fun ltf (s1, rf) -> p' ltf rf) h;
            ==> { }
            theta f (s0+1) (fun ltf (s1, rf) -> p (async_runtree (s0+1) ltf) (Promise (s0+1) (Universe.downgrade_val rf))) h;
            ==> { _ by (norm [delta_only [`%append_runtree;`%empty_runtree]; zeta; iota]; assumption ())}
            theta f (s0+1) (fun lt (s1, rf) -> p (async_runtree (s0+1) (append_runtree lt empty_runtree)) (Promise (s0+1) (Universe.downgrade_val rf))) h;
            ==> { _ by (norm [delta_only [`%w_return;`%w_return0]; iota]; assumption ())}
            theta f (s0+1) (fun lt (s1, rf) -> w_return (s1, Promise (s0+1) (Universe.downgrade_val rf))
                  (fun lt' (_, pr) -> p (async_runtree (s0+1) (append_runtree lt lt')) pr) (append_runtree h lt)) h;
            ==> { _ by (norm [delta_only [`%w_async0;`%w_bind;`%w_bind0;`%w_post_bind;`%w_post_shift]; zeta;iota]) }
            w_async0 (s0+1) (theta f (s0+1)) (fun ltf (s1, pr) -> p (async_runtree (s0+1) ltf) pr) h;
            ==> { _ by (norm [delta_only [`%w_async]; zeta;iota]; assumption ()) }
            w_async (s0+1) (theta f (s0+1)) (fun lt (s1, pr) -> p lt pr) h;
            ==> { _ by (norm [delta_only [`%append_runtree;`%empty_runtree]; zeta; iota]; assumption ())}
            w_async (s0+1) (theta f (s0+1)) (fun lt (s1, pr) ->
               p (lt `append_runtree` empty_runtree) pr) h;
            ==> { _ by (norm [delta_only [`%w_return;`%w_return0]; iota]; assumption ())}
            w_async (s0+1) (theta f (s0+1)) (fun lt (s1, pr) ->
              w_return (s1, pr) (fun lt' (_, pr) -> p (lt `append_runtree` lt') pr) (h `append_runtree` lt)) h;
            ==> { _ by (norm [delta_only [`%w_bind;`%w_bind0;`%w_post_bind;`%w_post_shift]; iota])}
            w_bind (w_async (s0+1) (theta f (s0+1))) (fun (s1, pr) ->
              w_return (s1, pr)) (fun lt (s1, pr) -> p lt pr) h;
            ==> {}
            w_bind (w_async (s0+1) (theta f (s0+1))) (fun (s1, pr) ->
              theta (Return pr) s1) (fun lt (s1, pr) -> p lt pr) h;
            ==> {}
            w_bind (w_async (s0+1) (theta f (s0+1))) (fun (s1, pr) ->
              theta (free_return pr) s1) (fun lt (s1, pr) -> p lt pr) h;
            ==> { _ by (norm [delta_only [`%theta]; zeta;iota]; assumption ()) }
            theta (Async f free_return) s0 (fun lt (s1, pr) -> p lt pr) h;
            }
         end in
         let _:squash (theta' (Async f free_return) s0 p h) = begin
           lemma_theta_theta' (Async f free_return)
         end in
         assert (theta' (Async f free_return) s0 p h)
       end
  end

let async0 (#a:Type) (#pre:w_pre) (#post:tracetree int -> a -> tracetree int -> Type0) ($f:unit -> Cy a pre post) :
  dm (promise a) (fun p h -> pre h /\ (forall pr lt. post h (Promise?.r pr) lt ==> p (async_runtree (Promise?.id pr) lt) pr)) =
  let wp' : w (Universe.raise_t a) = raise_w (fun p h -> pre h /\ (forall lt r. post h r lt ==> p lt r)) in
  let f' : dm (Universe.raise_t a) wp' = async00 f in
  let m : free (promise a) = Async f' free_return in
  async_spec_implies_theta pre post f';
  m
**)

[@"opaque_to_smt"]
let async (#a:Type) (#pre:w_pre) (#post:trace int -> a -> trace int -> Type0) ($f:unit -> Cy a pre post) :
  Cy (promise int a) pre (fun h pr lt -> lt == async_event pr /\ post h pr.r pr.lt) =
  admit ()
//  CyWP?.reflect (Async (async00 #a #_ f) Return)

[@"opaque_to_smt"]
let await (#a:Type) (pr:promise int a) : Cy a (fun _ -> True) (fun h r lt -> reveal pr.r == r /\ lt == [EAwait pr]) =
  admit ()
  // CyWP?.reflect (Await pr Return)

let synced (#a:Type) (x:a) () : Cy a (fun _ -> True) (fun h r lt -> r == x /\ lt == [Ev 0;Ev 1;Ev 2]) by (compute ()) = print 0; print 1; print 2; x

let pre_test () : Cy (promise int int) (fun _ -> True) (fun h pr lt -> lt == [EAsync pr]) =
  let prx = async (synced 2) in
  prx

let pre_test' () : Cy int (fun _ -> True) (fun h r lt -> r == 1 /\ (exists (pr1:promise int int). lt == [EAsync pr1])) =
  let prx = async (synced 2) in
  1

let test () : Cy int (fun _ -> True) (fun h r lt ->
  exists (pr1 pr2:promise int int). r == 1 /\ lt == [EAsync pr1; EAsync pr2; Ev 1; Ev 2; Ev 2]) =
  let prx = async (synced 2) in
  let pry = async (synced 3) in
  print 1;
  print 2;
  (if false then print 3
  else print 2);
  1

let test2 () : Cy int (fun _ -> True) (fun h r lt -> r == 5 /\
  exists (pr1 pr2:promise int int). lt == [EAsync pr1; EAsync pr2; EAwait pr1; EAwait pr2]) =
  let prx = async (synced 2) in
  let pry = async (synced 3) in
  let x : int = await prx in
  let y : int = await pry in
  x + y


let f () : Cy (promise int unit) (fun _ -> True) (fun h pr lt -> lt == [EAsync pr] /\ reveal pr.lt == [Ev 0; Ev 1; Ev 2]) =
  async (synced ())

let g () : Cy (promise int unit) (fun _ -> True) (fun h pr lt -> lt == [Ev 10; EAsync pr]) =
  print 10;
  f ()

let h () : Cy unit (fun _ -> True) (fun h r lt -> exists (pr1:promise int unit). lt == [Ev 10; EAsync pr1; EAwait pr1; Ev 20]) =
  await (g ());
  print 20

noeq
type ltl_syntax (s:Type0) =
| Eventually : ltl_syntax s -> ltl_syntax s
| Always: ltl_syntax s -> ltl_syntax s
| And: ltl_syntax s -> ltl_syntax s -> ltl_syntax s
| Or: ltl_syntax s -> ltl_syntax s -> ltl_syntax s
| Impl: ltl_syntax s -> ltl_syntax s -> ltl_syntax s
| Now: s -> ltl_syntax s

let rec ltl_denote (#s: Type0) (form: ltl_syntax s) (tr: trace s) : GTot Type0 =
  match form with
  | Now ev -> begin
    match tr with
    | [] -> False
    | Ev x :: _ -> ev == x
    | EAsync pr :: tl ->
      assume (reveal (pr.lt) << tr); (** this is just because of reveal. fixable **)
      ltl_denote form pr.lt /\ ltl_denote form tl
    | EAwait pr :: tl -> True (** Wrong! if it is already awaited, then it should be the event from the tail. if it is not awaited, then it is some other event **)
  end
  | Eventually p -> begin
    match tr with
    | [] -> False
    | Ev x :: tl -> ltl_denote p tr \/ ltl_denote form tl
    | EAsync pr :: tl ->
      assume (reveal (pr.lt) << tr); (** this is just because of reveal. fixable **)
      ltl_denote form pr.lt \/ ltl_denote form tl (** ??? is it a conjunction or a disjunction? what if it is a prop that holds after interleaving (e.g., syncronization)? **)
    | EAwait pr :: tl -> ltl_denote form tl
  end
  | Always p -> begin
    match tr with
    | [] -> False
    | Ev x :: tl -> ltl_denote p tr /\ ltl_denote form tl
    | EAsync pr :: tl ->
      assume (reveal (pr.lt) << tr); (** this is just because of reveal. fixable **)
      ltl_denote form pr.lt /\ ltl_denote form tl (** what if it is a prop that holds after interleaving (e.g., syncronization)? **)
    | EAwait _ :: tl -> ltl_denote form tl
  end
  | And p q -> ltl_denote p tr /\ ltl_denote q tr
  | Or p q -> ltl_denote p tr \/ ltl_denote q tr
  | Impl p q -> ltl_denote p tr ==> ltl_denote q tr

assume val law_one form (pr:promise 'e 'a) :
  Lemma (ltl_denote form pr.lt <==> ltl_denote form [EAsync pr; EAwait pr])

(** Unit Tests **)

let tr_sync0 : trace int = [Ev 0; Ev 1; Ev 2]
let pr_sync0 : promise int int = Promise 1 tr_sync0 2
let tr_async0 : trace int = [EAsync pr_sync0; EAwait pr_sync0]

let _ = assert (ltl_denote (And (Now 0) (Eventually (And (Now 1) (Eventually (Now 2))))) tr_sync0)
let _ = assert (ltl_denote (Eventually (And (Now 0) (Eventually (And (Now 1) (Eventually (Now 2)))))) tr_sync0)

let _ = assert (ltl_denote (And (Now 0) (Eventually (And (Now 1) (Eventually (Now 2))))) tr_async0)

//[@expect_failure]
//let _ = assert (ltl_denote (Now 0) [EAwait pr_sync0])

let rec process_async (id:nat) (tr:trace 'e) : GTot (list (nat * trace 'e)) (decreases tr) =
  match tr with
  | [] -> [(id, [])]
  | Ev _ :: _ -> [(id, tr)]
  | EAwait _ :: _ -> [(id, tr)]
  | EAsync pr :: tl ->
    assume (reveal (pr.lt) << tr);
    process_async id tl @ process_async pr.id pr.lt

let _ = assert (forall (pr:promise int int). process_async 0 [Ev 5; EAsync pr] == [(0, [Ev 5; EAsync pr])])
let _ = assert (forall (pr:promise int int). process_async 0 [EAsync (Promise 1 [Ev 2; EAsync pr] ()); Ev 6] == [(0, [Ev 6]); (1, [Ev 2; EAsync pr])])
let _ = assert (process_async 0 [EAsync (Promise 1 [EAsync (Promise 2 [Ev 5] ()); Ev 2] ()); Ev 6] == [((0 <: nat), [Ev 6]); ((1 <: nat), [Ev 2]); ((2 <: nat), [Ev 5])])

let rec can_process_await
  (id:nat)
  (tr:(trace 'e){Cons? tr /\ EAwait? (hd tr)})
  (trs:list (nat * trace 'e){exists (i:nat{i < List.Tot.length trs}). fst (List.Tot.index trs i) == reveal (Promise?.id (EAwait?.pr (hd tr)))}) : GTot bool =
  match trs with
  | (id', tr') :: tl ->
    if id = id' then begin
      if List.Tot.length tr' = 0 then true
      else false
    end else begin
      admit ();
      can_process_await id tr tl
    end

type proc_await = | PrUnk | PrPending | PrFulfilled
let rec can_process_await'
  (id:nat)
  (trs:list (nat * trace 'e)) : GTot proc_await =
  match trs with
  | [] -> PrUnk
  | (id', tr') :: tl ->
    if id = id' then begin
      if List.Tot.length tr' = 0 then PrFulfilled
      else PrPending
    end else can_process_await' id tl

let normalized_trace (tr:trace 'e) (trs:list (nat * trace 'e)) : Type0 =
  match tr with
  | [] -> True
  | Ev _ :: _ -> True
  | EAsync _:: _ -> False
  | EAwait pr :: _ -> begin
    match can_process_await' pr.id trs with
    | PrFulfilled -> False
    | _ -> True
  end

let normalized_traces (trs:list (nat * trace 'e)) : Type0 =
  forall (itr:nat * trace 'e). itr `memP` trs ==>
    normalized_trace (snd itr) trs

(* Normalizes traces by looking at the trace head and processing EAsync and EAwaits.
   Thus, in the end, traces should not start with EAsync or EAwaits that are PrFulfilled.**)
[@@admit_termination]
let rec _normalize_traces (ntrs trs:list (nat * trace 'e)) : GTot (list (nat * trace 'e)) =
  match trs with
  | [] -> ntrs
  | (i, tr)::tls -> begin
    match tr with
    | [] | Ev _ :: _ -> _normalize_traces (ntrs@[(i,tr)]) tls
    | EAsync _ :: tl -> _normalize_traces ntrs (process_async i tl @ tls)
    | EAwait pr :: tl -> begin
      match can_process_await' pr.id (ntrs @ tls) with
      | PrFulfilled -> _normalize_traces [] (ntrs @ [(i,tl)] @ tls)
      | _ -> _normalize_traces (ntrs@[(i,tr)]) tls
    end
  end

let normalize_traces (trs:list (nat * trace 'e)) : GTot (ntrs:(list (nat * trace 'e)){normalized_traces ntrs}) =
  let ntrs = _normalize_traces [] trs in
  assume (normalized_traces ntrs);
  ntrs

let progress (trs:list (nat * trace 'e){length trs > 0}) (idx:nat{idx < length trs}) : GTot (list (nat * trace 'e)) =
  // assume empty, Ev or Await
  lemma_splitAt_snd_length idx trs;
  let part1, (id, tr)::part2 = splitAt idx trs in
  let tr' = match tr with | Ev _ :: tl -> tl | _ -> tr in
  normalize_traces (part1 @ (id, tr') :: part2)

let rec interval (l:int) (r:int{l <= r}) : Tot (list (x:int)) (decreases (r-l)) =
  if l = r then []
  else l :: (interval (l+1) r)

let rec ltl_denote2 (#s: Type0) (form: ltl_syntax s) (trs: list (nat * trace s)) : GTot Type0 =
  assume (normalized_traces trs);
  match trs with | [] -> False | _ ->
  match form with
  | Now ev -> begin
    (** TODO: if all traces are empty, then it should return false **)
    fold_left (/\) True
      (map (fun (id, tr) ->
        assume (normalized_trace tr trs);
        match tr with
        | [] -> True
        | Ev x :: tl -> ev == x
        | EAwait pr :: tl -> begin
          match can_process_await' pr.id trs with
          | PrUnk -> False
          | PrPending -> True
        end) trs)
  end
  | Eventually p -> begin
    (** TODO: if all traces are empty, then it should return false **)
    ltl_denote2 p trs \/
    fold_left (/\) True
      (map (fun (idx:int) ->
        assume (0 <= idx /\ idx < length trs);
        let new_trs = progress trs idx in
        assume (new_trs << trs);
        ltl_denote2 form new_trs
      ) (interval 0 (length trs)))
  end
  | And p q -> ltl_denote2 p trs /\ ltl_denote2 q trs
  | Or p q -> ltl_denote2 p trs \/ ltl_denote2 q trs
  | Impl p q -> ltl_denote2 p trs ==> ltl_denote2 q trs
  | _ -> False

let ltl_denote' form tr =
  ltl_denote2 form (normalize_traces [(0, tr)])

let _ = assert (ltl_denote' (And (Now 0) (Eventually (And (Now 1) (Eventually (Now 2))))) tr_sync0)
let _ = assert (ltl_denote' (Eventually (And (Now 0) (Eventually (And (Now 1) (Eventually (Now 2)))))) tr_sync0)

// let _ = assert (ltl_denote' (And (Now 0) (Eventually (And (Now 1) (Eventually (Now 2))))) tr_async0) by (compute ())

[@expect_failure]
let _ = assert (ltl_denote' (Now 0) [EAwait pr_sync0])
