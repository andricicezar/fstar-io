module DMFree.Refine

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open DMFree
open Hist

unfold
let refine_free (#op:Type) (#s:op_sig op) (m:free op s 'a) (q:pure_post 'a) : 
  Pure (free op s (x:'a{q x}))
    (requires (forall x. x `return_of` m ==> q x)) 
    (ensures (fun _ -> True)) =
  free_subcomp _ (fun _ -> True) q m 

unfold
let cast_post0 (#event:Type) (q:pure_post 'a) (p:hist_post (v:'a{q v})) : hist_post #event 'a =
  (fun lt (r:'a) -> q r ==> p lt r)

let cast_post (#event:Type) (q:pure_post 'a) (p : hist_post (v:'a{q v})) : hist_post #event 'a = 
  cast_post0 q p

let refine_hist #event (wp:hist #event 'a) (q:pure_post 'a) : hist #event (v:'a{q v}) = 
  let wp' : hist0 (v:'a{q v}) = (fun p -> wp (cast_post q p)) in
  assert (forall (post1:hist_post (x:'a{q x})) (post2:hist_post (x:'a{q x})). (hist_post_ord post1 post2 ==> (forall h. wp' post1 h ==> wp' post2 h)));
  assert (hist_wp_monotonic #(x:'a{q x}) wp');
  wp'

let lemma_refine_hist_implies_weaken_post #event (wp:hist #event 'a) (q:pure_post 'a) : Lemma (
  forall (p:hist_post 'a) h. refine_hist wp q p h ==> wp (cast_post q p) h) = ()

let lemma_cast_post0 #event (q:pure_post 'a) (p:hist_post #event (v:'a{q v})) :
  Lemma (
    let p2 : hist_post (v:'a{q v}) = fun lt r -> cast_post0 q p lt r in
    p2 `hist_post_ord` p
  ) = ()

let rec lemma_free_subcomp
  (#op:Type) (#s:op_sig op) (#event)
  (cmd_wp:op_wp op s event)
  (q1:pure_post 'a) (q2:pure_post 'a)
  (m : free op s (v:'a{q1 v})) :
  Lemma
    (requires (forall x. q1 x /\ x `return_of` m ==> q2 x))
    (ensures (theta cmd_wp m `hist_ord #_ #'a` theta cmd_wp (free_subcomp _ q1 q2 m))) =
  match m with
  | Return x -> assert (theta cmd_wp m `hist_ord #_ #'a` theta cmd_wp (free_subcomp _ q1 q2 m)) by (compute ())
  | Call cmd arg k -> begin
    let fst : s.res cmd -> hist (v:'a{q1 v}) = fun r -> theta cmd_wp (k r) in
    let snd : s.res cmd -> hist (v:'a{q2 v}) = fun r -> theta cmd_wp (free_subcomp _ q1 q2 (k r)) in
    calc (==) {
      theta cmd_wp m;
      == {}
      theta cmd_wp (Call cmd arg k);
      == { _ by (compute ()) } // unfold theta
      hist_bind (cmd_wp cmd arg) (fun r -> theta cmd_wp (k r));
      == {}
      hist_bind (cmd_wp cmd arg) fst;
    };
    (** fst ==> snd /\ hist is monotonic **)
    introduce forall (p:hist_post 'a) h. hist_bind (cmd_wp cmd arg) fst p h ==> hist_bind (cmd_wp cmd arg) snd p h with begin 
      introduce forall (r:s.res cmd). (fst r `hist_ord #event #'a` snd r) with begin
        lemma_free_subcomp cmd_wp q1 q2 (k r)
      end
    end;
    calc (==) {
      hist_bind (cmd_wp cmd arg) snd;
      == {}
      hist_bind (cmd_wp cmd arg) (fun r -> theta cmd_wp (free_subcomp _ q1 q2 (k r)));
      == { _ by (compute ()) }
      theta cmd_wp (Call cmd arg (fun r -> free_subcomp _ q1 q2 (k r)));
      == { _ by (compute ()) }
      theta cmd_wp (free_subcomp _ q1 q2 (Call cmd arg k));
      == {}
      theta cmd_wp (free_subcomp _ q1 q2 m);
    }
  end
  

let lemma_free_subcomp_2
  (#op:Type) (#s:op_sig op) (#event)
  (cmd_wp:op_wp op s event)
  (q:pure_post 'a) (m : free op s 'a) :
  Lemma 
    (requires (forall x. x `return_of` m ==> q x))
    (ensures (forall p h. theta cmd_wp m (cast_post0 q p) h ==> theta cmd_wp (free_subcomp _ (fun _ -> True) q m) p h)) =
  introduce forall p h. (theta cmd_wp m (cast_post0 q p) h ==> theta cmd_wp (free_subcomp _ (fun _ -> True) q m) p h) with begin 
    introduce theta cmd_wp m (cast_post0 q p) h ==> (theta cmd_wp (free_subcomp _ (fun _ -> True) q m) p h) with _. begin 
      assert (theta cmd_wp m (cast_post0 q p) h);
      lemma_free_subcomp cmd_wp (fun _ -> True) q m;
      assert (theta cmd_wp (free_subcomp _ (fun _ -> True) q m) p h)
    end
  end

let lemma_theta_cast_post_implies_theta_refine_io 
  (#op:Type) (#s:op_sig op) #event
  (cmd_wp:op_wp op s event)
  (#wp:hist #event 'a)
  (d:dm op s event cmd_wp 'a wp) (q:pure_post 'a) :
  Lemma (requires (forall x. x `return_of` d ==> q x))
        (ensures (forall p h. theta cmd_wp d (cast_post q p) h ==> theta cmd_wp (refine_free d q) p h)) =
  lemma_free_subcomp_2 cmd_wp q d
  
let lemma_refine_io_refine_hist
  (#op:Type) (#s:op_sig op) #event
  (cmd_wp:op_wp op s event)
  (#wp:hist #event 'a)
  (d:dm op s event cmd_wp 'a wp) (q:pure_post 'a) : 
  Lemma
    (requires (forall x. x `return_of` d ==> q x))
    (ensures (refine_hist wp q `hist_ord` theta cmd_wp (refine_free d q))) =
  assert (wp `hist_ord` theta cmd_wp d);
  lemma_refine_hist_implies_weaken_post wp q;
  assert (forall p h. refine_hist wp q p h ==> theta cmd_wp d (cast_post q p) h);
  lemma_theta_cast_post_implies_theta_refine_io cmd_wp d q;
  assert (forall p h. theta cmd_wp d (cast_post q p) h ==> theta cmd_wp (refine_free d q) p h)
  
let refine_dm 
  (#op:Type) (#s:op_sig op) #event
  (cmd_wp:op_wp op s event)
  (#wp:hist #event 'a)
  (d:dm op s event cmd_wp 'a wp) (q:pure_post 'a) : 
  Pure (dm op s event cmd_wp (v:'a{q v}) (refine_hist wp q))
    (requires (forall x. x `return_of` d ==> q x))
    (ensures (fun _ -> True)) =
  lemma_refine_io_refine_hist cmd_wp d q;
  refine_free d q
