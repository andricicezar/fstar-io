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

let w_subcomp (#e:Type) (#a:Type) (wp:w #e a) (p1 p2:w_post a) (h:tracetree e) :
  Lemma (requires (wp p1 h /\ p1 `w_post_ord` p2))
        (ensures (wp p2 h)) = ()

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
  fun lt (x:a) ->
    kw x (w_post_shift p lt) (h `append_runtree` lt)


unfold
let w_bind0 (#e:Type) (#a:Type u#a) (#b:Type u#b) (wp : w #e a) (kwp : a -> w #e b) : w #e b =
  fun p h -> wp (w_post_bind h kwp p) h
let w_bind = w_bind0

let __list_assoc_l l1 l2 l3 : Lemma (l1 `append_runtree` (l2 `append_runtree` l3) == (l1 `append_runtree` l2) `append_runtree` l3) = 
  lemma_append_runtree_assoc l1 l2 l3
let __iff_refl a : Lemma (a <==> a) = ()
let w_law1 (x:'a) (k:'a -> w 'b) : Lemma (forall p h. w_bind (w_return x) k p h <==> k x p h) = ()
let w_law2 (m:w 'a) : Lemma (forall p h. w_bind m w_return p h <==> m p h) = ()
let w_law3 (m:w 'a) (g:'a -> w 'b) (k:'b -> w 'c) : Lemma (forall p h. w_bind (w_bind m g) k p h <==> w_bind m (fun x -> w_bind (g x) k) p h) =
  let lhs = w_bind m (fun r1 -> w_bind (g r1) k) in
  let rhs = w_bind (w_bind m g) k in
  let pw (p : w_post 'c) h : Lemma (lhs p h <==> rhs p h) =
    assert (lhs p h <==> rhs p h) by begin
      unfold_def (`w_bind);
      norm [];
      l_to_r [`__list_assoc_l];
      mapply (`__iff_refl)
    end
  in
  Classical.forall_intro_2 pw
  
open FStar.Ghost

noeq
type promise (a:Type) = | Promise : id:erased nat -> r:erased a -> promise a

noeq
type free (#e:Type u#0) (a:Type u#a) : Type u#(max 1 a) =
| Require : (pre:pure_pre) -> k:((squash pre) -> free u#a #e a) -> free #e a
| Return : a -> free #e a
| Print : (arg:e) -> cont:(unit -> free u#a #e a) -> free #e a 
| Async : #c:Type u#0 -> free #e (Universe.raise_t u#0 u#a c) -> k:(promise c -> free u#a #e a) -> free #e a
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
  
unfold let w_async0 #e #a id (wf:w #e (nat * (Universe.raise_t a))) : w #e (nat * promise a) =
  w_bind wf (fun (s1, r) -> w_return (s1, (Promise id (hide (Universe.downgrade_val r)))))
  
let w_async #e #a (id:nat) (wf:w #e (nat * (Universe.raise_t a))) : w #e (nat * (promise a)) =
  fun p -> (w_async0 id wf) (fun ltf spr -> p (async_runtree id ltf) spr)

let w_await #e (pr:promise 'a) : w #e 'a =
  fun p h -> p (return_runtree [EAwait (Promise?.id pr)]) (reveal (Promise?. r pr))
  
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
      w_bind (w_async id (theta f (s0+1))) (fun (s1, pr) -> theta (k pr) s1)
  | Await pr k -> 
      w_bind (w_await pr) (fun r -> theta (k r) s0)

let theta' m s0 = w_bind (theta m s0) (fun (s1, x) -> w_return x)

let lemma_wp_drop_state (wp:w #'e (nat * 'a)) p h : Lemma (
   w_bind wp (fun (_, x) -> w_return x) p h <==> wp (fun lt (_, rf) -> p lt rf) h) = ()
   
let lemma_theta_theta'0 (m:free #'e 'a) s0 p h : Lemma (
   theta' m s0 p h <==> theta m s0 (fun lt (s1, rf) -> p lt rf) h) =
   lemma_wp_drop_state (theta m s0) p h

let lemma_theta_theta' (m:free #'e 'a) : Lemma (
   forall s0 p h. theta' m s0 p h <==> theta m s0 (fun lt (s1, rf) -> p lt rf) h) =
   Classical.forall_intro_3 (lemma_theta_theta'0 m)

let theta_monad_morphism_ret (v:'a) (s0:nat) :
  Lemma (theta' (free_return v) s0 == w_return v) by (compute ()) = ()

let w_bind_subcomp (wp1:w 'a) (wp2:'a -> w 'b) (wp3:'a -> w 'b) : 
  Lemma 
    (requires ((forall x p h. wp2 x p h <==> wp3 x p h)))
    (ensures (forall p h. w_bind wp1 wp2 p h <==> w_bind wp1 wp3 p h)) = ()

let rec free_bind'
  (#e:Type)
  (#a:Type u#a)
  (#b:Type u#b)
  (l : free #e a)
  (cont : a -> free #e b) :
  free #e b =
  match l with
  | Async f k ->
      Async 
        (free_bind f (fun x -> free_return (Universe.raise_val u#0 u#b (Universe.downgrade_val x))))
        (fun x -> free_bind (k x) cont)
  | _ -> free_bind l cont


let lemma_w_async #e #a (wf:w #e (nat * (Universe.raise_t a))) (s0:nat) : Lemma (forall p h.
  w_async (s0+1) (w_bind wf (fun (s1,x) -> w_return (s1,(Universe.raise_val (Universe.downgrade_val x))))) p h
  <==> w_async (s0+1) wf p h) by (norm [delta_only [`%w_bind;`%w_bind0;`%w_return;`%w_return0]; iota]) = ()

#set-options "--split_queries always --z3rlimit 10"
let rec theta_monad_morphism_bind0 (#e:Type) (#a:Type u#a) (#b:Type u#b) (m:free a) (km:a -> free b) (s0:nat) (p:w_post (nat * b)) h :
  Lemma (w_bind (theta #e m s0) (fun (s1, x) -> theta #e (km x) s1) p h <==> theta #e (free_bind m km) s0 p h) = 
  match m with
  | Return _ -> ()
  | Require pre k ->
    calc (<==>) {
      w_bind (theta #e m s0) (fun (s1, x) -> theta #e (km x) s1) p h;
      <==> {}
      w_bind (theta #e (Require pre k) s0) (fun (s1, x) -> theta #e (km x) s1) p h;
      <==> {}
      w_bind (w_bind (w_require pre) (fun x -> theta (k x) s0)) (fun (s1, x) -> theta #e (km x) s1) p h;
      <==> { w_law3 (w_require pre) (fun x ->  theta (k x) s0) (fun (s1, x) -> theta #e (km x) s1) }
      w_bind (w_require pre) (fun x -> w_bind (theta (k x) s0) (fun (s1, x) -> theta #e (km x) s1)) p h;
      <==> { 
        let rhs = (fun x -> w_bind (theta (k x) s0) (fun (s1, x) -> theta #e (km x) s1)) in
        let rhs' = (fun x -> theta (free_bind (k x) km) s0) in
        introduce forall (x:squash pre) p h. rhs x p h <==> rhs' x p h with 
          theta_monad_morphism_bind0 (k x) km s0 p h;
        assert (forall x. rhs x p h <==> rhs' x p h);
        w_bind_subcomp (w_require pre) rhs rhs';
        assert (w_bind (w_require pre) rhs p h <==> w_bind (w_require pre) rhs' p h)
       }
      w_bind (w_require pre) (fun x -> theta (free_bind (k x) km) s0) p h;
      <==> {}
      theta #e (Require pre (fun x -> free_bind (k x) km)) s0 p h;
      <==> {}
      theta #e (free_bind (Require pre k) km) s0 p h;
      <==> {}
      theta #e (free_bind m km) s0 p h;
    }
  | Print arg k -> 
    calc (<==>) {
      w_bind (theta #e m s0) (fun (s1, x) -> theta #e (km x) s1) p h;
      <==> {}
      w_bind (theta #e (Print arg k) s0) (fun (s1, x) -> theta #e (km x) s1) p h;
      <==> {}
      w_bind (w_bind (w_print arg) (fun x -> theta (k x) s0)) (fun (s1, x) -> theta #e (km x) s1) p h;
      <==> { w_law3 (w_print arg) (fun x ->  theta (k x) s0) (fun (s1, x) -> theta #e (km x) s1) }
      w_bind (w_print arg) (fun x -> w_bind (theta (k x) s0) (fun (s1, x) -> theta #e (km x) s1)) p h;
      <==> { 
        let rhs = (fun x -> w_bind (theta (k x) s0) (fun (s1, x) -> theta #e (km x) s1)) in
        let rhs' = (fun x -> theta (free_bind (k x) km) s0) in
        introduce forall x p h. rhs x p h <==> rhs' x p h with 
          theta_monad_morphism_bind0 (k x) km s0 p h;
        assert (forall x. rhs x p h <==> rhs' x p h);
        w_bind_subcomp (w_print arg) rhs rhs';
        assert (w_bind (w_print arg) rhs p h <==> w_bind (w_print arg) rhs' p h)
       }
      w_bind (w_print arg) (fun x -> theta (free_bind (k x) km) s0) p h;
      <==> {}
      theta #e (Print arg (fun x -> free_bind (k x) km)) s0 p h;
      <==> {}
      theta #e (free_bind (Print arg k) km) s0 p h;
      <==> {}
      theta #e (free_bind m km) s0 p h;
    }
  | Await pr k -> 
    calc (<==>) {
      w_bind (theta #e m s0) (fun (s1, x) -> theta #e (km x) s1) p h;
      <==> {}
      w_bind (theta #e (Await pr k) s0) (fun (s1, x) -> theta #e (km x) s1) p h;
      <==> {}
      w_bind (w_bind (w_await pr) (fun x -> theta (k x) s0)) (fun (s1, x) -> theta #e (km x) s1) p h;
      <==> { w_law3 (w_await pr) (fun x ->  theta (k x) s0) (fun (s1, x) -> theta #e (km x) s1) }
      w_bind (w_await pr) (fun x -> w_bind (theta (k x) s0) (fun (s1, x) -> theta #e (km x) s1)) p h;
      <==> { 
        let rhs = (fun x -> w_bind (theta (k x) s0) (fun (s1, x) -> theta #e (km x) s1)) in
        let rhs' = (fun x -> theta (free_bind (k x) km) s0) in
        introduce forall x p h. rhs x p h <==> rhs' x p h with 
          theta_monad_morphism_bind0 (k x) km s0 p h;
        assert (forall x. rhs x p h <==> rhs' x p h);
        w_bind_subcomp (w_await pr) rhs rhs';
        assert (w_bind (w_await pr) rhs p h <==> w_bind (w_await pr) rhs' p h)
       }
      w_bind (w_await pr) (fun x -> theta (free_bind (k x) km) s0) p h;
      <==> {}
      theta #e (Await pr (fun x -> free_bind (k x) km)) s0 p h;
      <==> {}
      theta #e (free_bind (Await pr k) km) s0 p h;
      <==> {}
      theta #e (free_bind m km) s0 p h;
    }
  | Async f k ->
    calc (<==>) {
      w_bind (theta #e m s0) (fun (s1, x) -> theta #e (km x) s1) p h;
      <==> {}
      w_bind (theta #e (Async f k) s0) (fun (s1, x) -> theta #e (km x) s1) p h;
      <==> {}
      w_bind (w_bind (w_async (s0+1) (theta f (s0+1))) (fun (s1, x) -> theta (k x) s1)) (fun (s2, x) -> theta #e (km x) s2) p h;
      <==> { w_law3 (w_async (s0+1) (theta f (s0+1))) (fun (s1, x) ->  theta (k x) s1) (fun (s2, x) -> theta #e (km x) s2) }
      w_bind (w_async (s0+1) (theta f (s0+1))) (fun (s1, x) -> w_bind (theta (k x) s1) (fun (s2, x) -> theta #e (km x) s2)) p h;
      <==> { 
        let rhs = (fun (s1, x) -> w_bind (theta (k x) s1) (fun (s2, x) -> theta #e (km x) s2)) in
        let rhs' = (fun (s1, x) -> theta (free_bind (k x) km) s1) in
        introduce forall x s0 p h. rhs (s0,x) p h <==> rhs' (s0,x) p h with 
          theta_monad_morphism_bind0 (k x) km s0 p h;
        assert (forall x. rhs x p h <==> rhs' x p h);
        w_bind_subcomp (w_async (s0+1) (theta f (s0+1))) rhs rhs';
        assert (w_bind (w_async (s0+1) (theta f (s0+1))) rhs p h <==> w_bind (w_async (s0+1) (theta f (s0+1))) rhs' p h)
       }
      w_bind (w_async (s0+1) (theta f (s0+1))) (fun (s1, x) -> theta (free_bind (k x) km) s1) p h;
      <==> { lemma_w_async (theta f (s0+1)) s0 }
      w_bind (w_async (s0+1) (w_bind (theta f (s0+1)) (fun (s1,x) -> w_return (s1,(Universe.raise_val (Universe.downgrade_val x)))))) 
           (fun (s1, x) -> theta (free_bind (k x) km) s1) p h;
      <==> { _ by (norm [delta_only [`%free_return]; iota]) }
      w_bind (w_async (s0+1) (w_bind (theta f (s0+1)) (fun (s1,x) -> theta (free_return (Universe.raise_val (Universe.downgrade_val x))) s1))) 
           (fun (s1, x) -> theta (free_bind (k x) km) s1) p h;
      <==> { 
        let k = (fun x -> free_return (Universe.raise_val (Universe.downgrade_val x))) in
        introduce forall s0 p h. w_bind (theta #e f s0) (fun (s1, x) -> theta #e (k x) s1) p h <==> theta #e (free_bind f k) s0 p h with 
          theta_monad_morphism_bind0 f k s0 p h }
      w_bind (w_async (s0+1) (theta ((free_bind f (fun x -> free_return (Universe.raise_val (Universe.downgrade_val x))))) (s0+1))) (fun (s1, x) -> theta (free_bind (k x) km) s1) p h;
      <==> {}
      theta (Async (free_bind f (fun x -> free_return (Universe.raise_val (Universe.downgrade_val x)))) (fun x -> free_bind (k x) km)) s0 p h;
      <==> { _ by (compute ()) }
      theta #e (free_bind (Async f k) km) s0 p h;
      <==> {}
      theta #e (free_bind m km) s0 p h;
    }
#reset-options

let theta_monad_morphism_bind (#e:Type) (#a:Type) (#b:Type) (m:free a) (km:a -> free b) :
  Lemma (forall s0. w_bind (theta #e m s0) (fun (s1, x) -> theta #e (km x) s1) ⊑ theta #e (free_bind m km) s0) =
  Classical.forall_intro_3 (theta_monad_morphism_bind0 m km)

let dm (#e:Type) (a:Type u#a) (wp:w #e a) =
  m:(free a){forall s0. wp ⊑ theta' m s0}

let dm_return (a:Type u#a) (x:a) : dm a (w_return0 x) =
  Return x

let lemma_better_sub0
  (#e:Type)
  (#a:Type u#a)
  (#b:Type u#b)
  (wp:w #e a)
  (kwp:a -> w #e b)
  (c:dm a wp)
  (kc:(x:a -> dm b (kwp x))) 
  (s0:nat)
  (p:w_post #e b)
  h : Lemma
    (requires (
      let p1' : w_post #e (nat * a) = (fun lt (s1, x) -> theta (kc x) s1 (w_post_shift (fun lt' (_, x') -> p lt' x') lt) (append_runtree h lt)) in
      theta c s0 p1' h))
    (ensures (w_bind (w_bind (theta c s0) (fun (s1, x) -> theta (kc x) s1)) (fun (_, x) -> w_return x) p h)) =
  calc (==>) {
    theta c s0 (fun lt (s1, x) -> theta (kc x) s1 (w_post_shift (fun lt' (_, x') -> p lt' x') lt) (append_runtree h lt)) h;
    ==> { _ by (norm [delta_only [`%w_bind; `%w_bind0]; iota]) }
    w_bind (theta c s0) (fun (s1, x) -> theta (kc x) s1) (fun lt (_, x) -> p lt x) h;
    ==> { lemma_wp_drop_state (w_bind (theta c s0) (fun (s1, x) -> theta (kc x) s1)) p h }
    w_bind (w_bind (theta c s0) (fun (s1, x) -> theta (kc x) s1)) (fun (_, x) -> w_return x) p h;
  }
  

let lemma_better
  (#e:Type)
  (#a:Type u#a)
  (#b:Type u#b)
  (wp:w #e a)
  (kwp:a -> w #e b)
  (c:dm a wp)
  (kc:(x:a -> dm b (kwp x))) : Lemma
    (requires ((forall s0. wp ⊑ w_bind (theta c s0) (fun (_, x) -> w_return x)) /\
              (forall s0 x. kwp x ⊑ w_bind (theta (kc x) s0) (fun (_, x) -> w_return x))))
    (ensures (forall s0. w_bind wp kwp ⊑ w_bind (w_bind (theta c s0) (fun (s1, x) -> theta (kc x) s1)) (fun (_, x) -> w_return x))) =
  introduce forall s0 (p:w_post b) h. w_bind wp kwp p h ==> w_bind (w_bind (theta c s0) (fun (s1, x) -> theta (kc x) s1)) (fun (_, x) -> w_return x) p h with begin
    introduce w_bind wp kwp p h ==> w_bind (w_bind (theta c s0) (fun (s1, x) -> theta (kc x) s1)) (fun (_, x) -> w_return x) p h with _. begin
      let p1' : w_post #e (nat * a) = (fun lt (s1, x) -> theta (kc x) s1 (w_post_shift (fun lt' (_, x') -> p lt' x') lt) (append_runtree h lt)) in
      let _ : squash (theta c s0 p1' h) = begin
        eliminate forall s0. wp ⊑ w_bind (theta c s0) (fun (_, x) -> w_return x) with s0;
        assert (forall (p':w_post #e a) h. wp p' h ==> w_bind (theta c s0) (fun (_, x) -> w_return x) p' h);
        let p0 : w_post #e a = fun lt x -> kwp x (w_post_shift p lt) (append_runtree h lt) in
        assert (wp p0 h);
        let p0' : w_post #e a = fun lt x -> forall s1. theta (kc x) s1 (w_post_shift (fun lt' (_, x') -> p lt' x') lt) (append_runtree h lt) in
        introduce forall lt x. p0 lt x ==> p0' lt x with begin
            assert (forall p h s1 x. kwp x p h ==> w_bind (theta (kc x) s1) (fun (_, x) -> w_return x) p h);
            assert (forall p h x. kwp x p h ==> (forall s1. w_bind (theta (kc x) s1) (fun (_, x) -> w_return x) p h));
            let p' : w_post #e b = w_post_shift p lt in
            let h' = (append_runtree h lt) in
            eliminate forall p h x. kwp x p h ==> (forall s1. w_bind (theta (kc x) s1) (fun (_, x) -> w_return x) p h) with p' h' x;
            introduce p0 lt x ==> p0' lt x with _. begin
            assert (kwp x p' h');
            assert (forall s1. w_bind (theta (kc x) s1) (fun (_, x) -> w_return x) p' h');
            introduce forall s1. theta (kc x) s1 (fun lt (_, x) -> p' lt x) h' with
                lemma_theta_theta'0 (kc x) s1 p' h';
            assert (p0' lt x)
            end
        end;
        assert (wp p0' h);
        eliminate forall (p':w_post #e a) h. wp p' h ==> w_bind (theta c s0) (fun (_, x) -> w_return x) p' h with p0' h;
        assert (w_bind (theta c s0) (fun (_, x) -> w_return x) p0' h);
        let p1 : w_post #e (nat * a) = (fun lt (_, x) -> p0' lt x) in
        lemma_theta_theta'0 c s0 p0' h;
        assert (theta c s0 p1 h);
        assert (p1 `w_post_ord` p1');
        w_subcomp (theta c s0) p1 p1' h;
        assert (theta c s0 p1' h)
      end in

      lemma_better_sub0 wp kwp c kc s0 p h
    end
  end

let dm_bind
  (#e:Type)
  (a:Type u#a)
  (b:Type u#b)
  (wp:w #e a)
  (kwp:a -> w #e b)
  (c:dm a wp)
  (kc:(x:a -> dm b (kwp x))) :
  dm #e b (w_bind0 wp kwp) =
  let m = free_bind c kc in
  lemma_better wp kwp c kc;
  theta_monad_morphism_bind c kc;
  assert (forall s0. w_bind (theta c s0) (fun (s1, x) -> theta (kc x) s1) ⊑ theta m s0);
  assert (forall s0. w_bind wp kwp ⊑ theta' m s0);
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

let test2 () : Cy int (fun _ -> True) (fun h r lt -> exists (id1 id2:nat). r == 5 /\ lt == Node [EAsync id1] (Node [Ev 0; Ev 1; Ev 2] Leaf Leaf) (Node [EAsync id2] (Node [Ev 0; Ev 1; Ev 2] Leaf Leaf) (Node [EAwait id1; EAwait id2] Leaf Leaf))) =
  let prx = async (return 2) in
  let pry = async (return 3) in
  let x : int = await prx in
  let y : int = await pry in
  x + y



