module Runtree_Async_Await

open FStar.Tactics
open FStar.List.Tot.Base
open FStar.Classical.Sugar

open Runtree

type event (e:Type0) =
| Ev : e -> event e
| EAsync : nat -> event e
| EAwait : nat -> event e

type tracetree 'e = runtree (event 'e)

type w_post #e (a:Type) = tracetree e -> a -> Type0
type w_pre #e = (tracetree e) -> Type0

type w0 #e (a:Type) = w_post #e a -> w_pre #e

unfold
let w_post_ord (#e:Type) (#a:Type) (p1 p2:w_post #e a) = forall lt (r:a). p1 lt r ==> p2 lt r

let w_monotonic (#e:Type) (#a:Type) (wp:w0 #e a) =
  forall (p1 p2:w_post a). (p1 `w_post_ord` p2) ==> (forall h. wp p1 h ==> wp p2 h)

type w (#e:Type) (a:Type) = wp:(w0 #e a){w_monotonic wp}

unfold
let w_ord0 (#e:Type) (#a:Type) (wp1:w #e a) (wp2:w #e a) = forall (p:w_post a) h. wp1 p h ==> wp2 p h
let w_ord = w_ord0
unfold let (⊑) = w_ord

unfold
let w_return0 (#a:Type) (#e:Type) (x:a) : w #e a = 
  fun p _ -> p empty_runtree x
let w_return = w_return0

unfold
let w_post_shift (#e:Type) (p:w_post #e 'b) (lt:tracetree e) : w_post #e 'b =
  fun lt' r' -> p (lt `append_runtree` lt') r'

unfold
let w_post_bind
  (#e:Type)
  (#a:Type u#a) (#b:Type u#b)
  (h:tracetree e)
  (kw : a -> w #e b)
  (p:w_post #e b) :
  Tot (w_post #e a) =
  fun lt x ->
    kw x (w_post_shift p lt) (h `append_runtree` lt)


unfold
let w_bind0 (#e:Type) (#a:Type u#a) (#b:Type u#b) (wp : w #e a) (kwp : a -> w #e b) : w #e b =
  fun p h -> wp (w_post_bind h kwp p) h
let w_bind = w_bind0

open FStar.Ghost

noeq
type promise (a:Type) = | Promise : id:erased nat -> r:erased a -> promise a

noeq
type free (#e:Type u#0) (a:Type u#a) : Type u#(max 1 a) =
| Require : (pre:pure_pre) -> k:((squash pre) -> free u#a #e a) -> free #e a
| Return : a -> free #e a
| Print : (arg:e) -> cont:(unit -> free u#a #e a) -> free #e a 
| Async : #c:Type u#0 -> free #e (Universe.raise_t c) -> k:(promise c -> free u#a #e a) -> free #e a
| Await : #c:Type u#0 -> promise c -> k:(c -> free u#a #e a) -> free #e a

let free_return (#e:Type) (#a:Type) (x:a) : free #e a =
  Return x

let rec free_bind
  (#e:Type)
  (#a:Type u#a)
  (#b:Type u#b)
  (l : free #e a)
  (cont : a -> free #e b) :
  free #e b =
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

let w_require #e (pre:pure_pre) : w #e (squash pre) = 
  let wp' : w0 (squash pre) = fun p h -> pre /\ p empty_runtree () in
  wp'

unfold
let w_print #e (ev:e) : w #e unit =
  fun p _ -> p (return_runtree [Ev ev]) ()

unfold let async_runtree (id:nat) (l:tracetree 'e) : tracetree 'e = Node [EAsync id] l Leaf
  
let w_async #e #a (id:nat) (wf:w #e a) : w #e a =
  fun p ->
    wf (fun ltf rf -> p (async_runtree id ltf) rf)


let w_await #e (id:nat) : w #e unit =
  fun p h -> p (return_runtree [EAwait id]) ()
  
val theta : (#e:Type) -> (#a:Type) -> free #e a -> nat -> w #e (nat * a)
let rec theta m = fun s0 ->
  match m with
  | Require pre k ->
      w_bind (w_require pre) (fun r -> theta (k r) s0)
  | Return x -> w_return (s0, x)
  | Print arg k ->
      w_bind (w_print arg) (fun r -> theta (k r) s0)
  | Async f k -> 
      let id = s0+1 in
      w_bind (w_async id (theta f (s0+1))) (fun (s1, rf) -> 
        theta (k (Promise id (Universe.downgrade_val rf))) s1)
  | Await pr k -> 
      w_bind (w_await (Promise?.id pr)) (fun () -> theta (k (Promise?.r pr)) s0)

let theta' m s0 = w_bind (theta m s0) (fun (s1, x) -> w_return x)



unfold let (<==) p x = x ==> p

let lemma_theta_theta' (m:free #'e 'a) : Lemma (
   forall s0 p h. theta' m s0 p h <==> theta m s0 (fun lt (s1, rf) -> p lt rf) h) =
   introduce forall s0 p h. theta' m s0 p h <==> theta m s0 (fun lt (s1, rf) -> p lt rf) h with begin
     calc (==>) {
       theta m s0 (fun lt (s1, pr) -> p lt pr) h;
       ==> { _ by (norm [delta_only [`%append_runtree; `%empty_runtree]; zeta; iota]; assumption ()) }
       theta m s0 (fun lt (s1, pr) -> p (lt `append_runtree` empty_runtree) pr) h;
       ==> { _ by (norm [iota]; assumption ()) }
       theta m s0 (fun lt (s1, pr) -> (fun lt' r' -> p (lt `append_runtree` lt') r') empty_runtree pr) h;
       ==> { _ by (norm [delta_only [`%w_post_shift]; iota]; assumption ())}
       theta m s0 (fun lt (s1, pr) -> (w_post_shift p lt) empty_runtree pr) h;
       ==> { _ by (norm [delta_only [`%w_return;`%w_return0]; iota]; assumption ())}
       theta m s0 (fun lt (s1, pr) -> w_return pr (w_post_shift p lt) (h `append_runtree` lt)) h;
       ==> { _ by (norm [iota]) }
       theta m s0 (fun lt r -> (fun (s1, x) -> w_return x) r (w_post_shift p lt) (h `append_runtree` lt)) h;
       ==> { _ by (norm [delta_only [`%w_post_bind]; iota]; assumption ())}
       theta m s0 (w_post_bind h (fun (s1, x) -> w_return x) p) h;
       ==> { _ by (norm [delta_only [`%w_bind;`%w_bind0]; iota]; assumption ())}
       w_bind (theta m s0) (fun (s1, x) -> w_return x) p h;
       ==> { _ by (norm [delta_only [`%theta']; iota]; assumption ()) }
       theta' m s0 p h;
    };

    calc (==>) {
       theta' m s0 p h;
       ==> { _ by (norm [delta_only [`%theta']; iota]; assumption ()) }
       w_bind (theta m s0) (fun (s1, x) -> w_return x) p h;
       ==> { _ by (norm [delta_only [`%w_bind;`%w_bind0]; iota]; assumption ())}
       theta m s0 (w_post_bind h (fun (s1, x) -> w_return x) p) h;
       ==> { _ by (norm [delta_only [`%w_post_bind]; iota]; assumption ())}
       theta m s0 (fun lt r -> (fun (s1, x) -> w_return x) r (w_post_shift p lt) (h `append_runtree` lt)) h;
       ==> { _ by (norm [iota]) }
       theta m s0 (fun lt (s1, pr) -> w_return pr (w_post_shift p lt) (h `append_runtree` lt)) h;
       ==> { _ by (norm [delta_only [`%w_return;`%w_return0]; iota]; assumption ())}
       theta m s0 (fun lt (s1, pr) -> (w_post_shift p lt) empty_runtree pr) h;
       ==> { _ by (norm [delta_only [`%w_post_shift]; iota]; assumption ())}
       theta m s0 (fun lt (s1, pr) -> (fun lt' r' -> p (lt `append_runtree` lt') r') empty_runtree pr) h;
       ==> { _ by (norm [iota]; assumption ()) }
       theta m s0 (fun lt (s1, pr) -> p (lt `append_runtree` empty_runtree) pr) h;
       ==> { _ by (norm [delta_only [`%append_runtree; `%empty_runtree]; zeta; iota]; assumption ()) }
theta m s0 (fun lt (s1, pr) -> p lt pr) h;
    }
  end

let theta_monad_morphism_ret (v:'a) (s0:nat) :
  Lemma (theta' (free_return v) s0 == w_return v) by (compute ()) = ()

let theta_lax_monad_morphism_bind (#e:Type) (#a:Type) (#b:Type) (m:free a) (km:a -> free b) :
  Lemma (forall s0. w_bind (theta #e m s0) (fun (s1, x) -> theta #e (km x) s1) ⊑ theta #e (free_bind m km) s0) = admit ()

let dm (#e:Type) (a:Type u#a) (wp:w #e a) =
  m:(free a){forall s0. wp ⊑ theta' m s0}

let dm_return (a:Type u#a) (x:a) : dm a (w_return0 x) =
  Return x

let dm_bind
  (#e:Type)
  (a:Type u#a)
  (b:Type u#b)
  (wp:w #e a)
  (kwp:a -> w #e b)
  (c:dm a wp)
  (kc:(x:a -> dm b (kwp x))) :
  dm #e b (w_bind0 wp kwp) =
  theta_lax_monad_morphism_bind #e c kc;
  let m = free_bind c kc in
  assume (forall s0. w_bind0 wp kwp ⊑ theta' m s0);
  m

let dm_subcomp
  (#e:Type)
  (a:Type u#a)
  (wp1:w #e a)
  (wp2:w #e a)
  (c:dm a wp1) :
  Pure (dm a wp2)
    (requires (wp2 `w_ord0` wp1))
    (ensures (fun _ -> True)) =
    c 

let w_if_then_else (#e:Type) (#a:Type) (wp1 wp2:w #e a) (b:bool) : w #e a =
  fun p h -> (b ==> wp1 p h) /\ ((~b) ==> wp2 p h)

let dm_if_then_else (#e:Type) (a : Type u#a) 
  (wp1 wp2: w #e a) (f : dm a wp1) (g : dm a wp2) (b : bool) : Type =
  dm a (w_if_then_else wp1 wp2 b)

let dm_partial_return
  (#e:Type)
  (pre:pure_pre) : dm #e (squash pre) (w_require pre) =
  let m = Require pre (Return) in
  assert (forall s0. w_require pre ⊑ theta' #e m s0) by (compute ());
  m

unfold
let lift_pure_w (#e:Type0) (#a:Type u#a) (wp : pure_wp a) : w #e a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  (fun (p:w_post a) _ -> wp (fun (r:a) -> p empty_runtree r))

let lift_pure_w_as_requires (#e:Type) (#a:Type) (wp : pure_wp a) :
  Lemma (forall (p:w_post #e a) h. lift_pure_w wp p h ==> as_requires wp) =
    assert (forall (p:w_post #e a) x. p empty_runtree x ==> True) ;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    assert (forall (p:w_post #e a). wp (fun x -> p empty_runtree x) ==> wp (fun _ -> True))
  
unfold let repr' = dm #int
unfold let return' = dm_return #int
unfold let bind' = dm_bind #int
unfold let subcomp' = dm_subcomp #int
unfold let if_then_else' = dm_if_then_else #int


reflectable
reifiable
total
effect {
  CyWP (a:Type) (wp : w #int a)
  with {
       repr       = repr'
     ; return     = return' 
     ; bind       = bind'
     ; subcomp    = subcomp'
     ; if_then_else = if_then_else'
     }
}

let lift_pure_dm 
  (a : Type u#a) 
  (wp : pure_wp a)
  (f:(eqtype_as_type unit -> PURE a wp)) : 
  dm #int a (lift_pure_w wp) =
  lift_pure_w_as_requires #int #a wp;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs = dm_partial_return (as_requires wp) in
  let rhs = (fun (pre:(squash (as_requires wp))) -> dm_return a (f ())) in
  let m = dm_bind _ _ _ _ lhs rhs in
  dm_subcomp a _ (lift_pure_w wp) m

sub_effect PURE ~> CyWP = lift_pure_dm

effect Cy
  (a:Type)
  (pre : tracetree int -> Type0)
  (post : tracetree int -> a -> tracetree int -> Type0) =
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
assume val pure_lemma (_ : unit) : Lemma p
assume val some_f (_ : squash p) : Cy unit (requires fun _ -> True) (ensures fun _ _ _ -> True)
assume val some_f' : unit -> Cy unit (requires fun _ -> p) (ensures fun _ _ _ -> p')

// TODO: why is this failing?
let pure_lemma_test () : Cy unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  pure_lemma () ;
  some_f ()

let pure_lemma_test2 () : Cy unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  pure_lemma () ;
  some_f () ;
  some_f' () ;
  assert p'
(** *** DONE with tests of partiality **)

let print (e:int) : Cy unit (fun _ -> True) (fun _ () lt -> lt == return_runtree [Ev e]) =
  CyWP?.reflect (Print e (Return))

let raise_w (#a:Type u#a) (wp:w a) : w (Universe.raise_t u#a u#b a) =
  fun p -> wp (fun lt r -> p lt (Universe.raise_val r))

[@"opaque_to_smt"]
let async00 (#a:Type u#a) (#wp:w a) ($f:unit -> CyWP a wp) : dm (Universe.raise_t u#a u#b a) (raise_w u#a u#b wp)  = 
  let f' : dm a wp = reify (f ()) in
  dm_subcomp _ _ _ (dm_bind _ _ _ _ f' (fun x -> dm_return _ (Universe.raise_val u#a u#b x)))

let async_spec_implies_theta 
  (#a:Type)
  (pre:w_pre) (post:tracetree int -> a -> tracetree int -> Type0)
  (f:dm (Universe.raise_t a) (fun p h -> pre h /\ (forall r lt. post h r lt ==> p lt (Universe.raise_val r)))) :
  Lemma (
    forall s0.
    (fun p h -> pre h /\ (forall pr lt. post h (Promise?.r pr) lt ==> p (async_runtree (Promise?.id pr) lt) pr))
    ⊑
    theta' (Async f free_return) s0) = 
  introduce forall s0 (p:w_post (promise a)) h. (pre h /\ (forall pr lt. post h (Promise?.r pr) lt ==> p (async_runtree (Promise?.id pr) lt) pr) ==>
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
            ==> { _ by (norm [delta_only [`%w_async]; zeta;iota]; assumption ()) }
            w_async (s0+1) (theta f (s0+1)) (fun lt (s1, rf) -> p lt (Promise (s0+1) (Universe.downgrade_val rf))) h;
            ==> { _ by (norm [delta_only [`%append_runtree;`%empty_runtree]; zeta; iota]; assumption ())}
            w_async (s0+1) (theta f (s0+1)) (fun lt (s1, rf) -> 
               p (lt `append_runtree` empty_runtree) (Promise (s0+1) (Universe.downgrade_val rf))) h;
            ==> { _ by (norm [delta_only [`%w_return;`%w_return0]; iota]; assumption ())}
            w_async (s0+1) (theta f (s0+1)) (fun lt (s1, rf) -> 
              w_return (s1, Promise (s0+1) (Universe.downgrade_val rf)) (fun lt' (_, pr) -> p (lt `append_runtree` lt') pr) (h `append_runtree` lt)) h;
            ==> { _ by (norm [delta_only [`%w_bind;`%w_bind0;`%w_post_bind;`%w_post_shift]; iota])}
            w_bind (w_async (s0+1) (theta f (s0+1))) (fun (s1, rf) -> 
              w_return (s1, (Promise (s0+1) (Universe.downgrade_val rf)))) (fun lt (s1, pr) -> p lt pr) h;
            ==> {}
            w_bind (w_async (s0+1) (theta f (s0+1))) (fun (s1, rf) -> 
              w_return (s1, (Promise (s0+1) (Universe.downgrade_val rf)))) (fun lt (s1, pr) -> p lt pr) h;
            ==> {}
            w_bind (w_async (s0+1) (theta f (s0+1))) (fun (s1, rf) -> 
              theta (Return (Promise (s0+1) (Universe.downgrade_val rf))) s1) (fun lt (s1, pr) -> p lt pr) h;
            ==> {}
            w_bind (w_async (s0+1) (theta f (s0+1))) (fun (s1, rf) -> 
              theta (free_return (Promise (s0+1) (Universe.downgrade_val rf))) s1) (fun lt (s1, pr) -> p lt pr) h;
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

[@"opaque_to_smt"]
let async (#a:Type) (#pre:w_pre) (#post:tracetree int -> a -> tracetree int -> Type0) ($f:unit -> Cy a pre post) : 
  Cy (promise a) pre (fun h pr lt -> exists lt'. lt == async_runtree (Promise?.id pr) lt' /\ post h (Promise?.r pr) lt') =
  CyWP?.reflect (async0 f)

[@"opaque_to_smt"]
let await (#a:Type) (pr:promise a) : Cy a (fun _ -> True) (fun h r lt -> reveal (Promise?.r pr) == r /\ lt == return_runtree [EAwait (Promise?.id pr)]) =
  CyWP?.reflect (Await pr (free_return))

let return (#a:Type) (x:a) () : Cy a (fun _ -> True) (fun h r lt -> r == x /\ lt == return_runtree [Ev 0;Ev 1;Ev 2]) = print 0; print 1; print 2; x

let test () : Cy int (fun _ -> True) (fun h r lt -> exists (id1 id2:nat). r == 1 /\ lt == Node [EAsync id1] (Node [Ev 0; Ev 1; Ev 2] Leaf Leaf) (Node [EAsync id2] (Node [Ev 0; Ev 1; Ev 2] Leaf Leaf) (Node [Ev 1; Ev 2; Ev 2] Leaf Leaf))) =
  let prx = async (return 2) in
  let pry = async (return 3) in
  print 1;
  print 2;
  (if false then print 3
  else print 2);
  1
 // let x : int = await prx in
 // let y : int = await pry in
//  2 + 3

let test2 () : Cy int (fun _ -> True) (fun h r lt -> r == 5) =
  let prx = async (return 2) in
  let pry = async (return 3) in
  let x : int = await prx in
  let y : int = await pry in
  x + y



