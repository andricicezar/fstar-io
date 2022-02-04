module DM.IO.Refine

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open DM.IO
open Hist

unfold
let refine_io (d:dm 'a 'wp) (q:pure_post 'a) : 
  Pure (io (x:'a{q x}))
    (requires (forall x. x `return_of` d ==> q x)) 
    (ensures (fun _ -> True)) =
  free_subcomp _ (fun _ -> True) q d

unfold
let cast_post0 (q:pure_post 'a) (p:hist_post (v:'a{q v})) : hist_post 'a =
  (fun lt (r:'a) -> q r ==> p lt r)

let cast_post (q:pure_post 'a) (p : hist_post (v:'a{q v})) : hist_post 'a = 
  cast_post0 q p

let refine_hist (wp:hist 'a) (q:pure_post 'a) : hist (v:'a{q v}) = 
  let wp' : hist0 (v:'a{q v}) = (fun p -> wp (cast_post q p)) in
  assert (forall (post1:hist_post (x:'a{q x})) (post2:hist_post (x:'a{q x})). (hist_post_ord post1 post2 ==> (forall h. wp' post1 h ==> wp' post2 h)));
  assert (hist_wp_monotonic #(x:'a{q x}) wp');
  wp'

let lemma_refine_hist_implies_weaken_post (wp:hist 'a) (q:pure_post 'a) : Lemma (
  forall (p:hist_post 'a) h. refine_hist wp q p h ==> wp (cast_post q p) h) = ()

let lemma_cast_post0 (q:pure_post 'a) (p:hist_post (v:'a{q v})) :
  Lemma (
    let p2 : hist_post (v:'a{q v}) = fun lt r -> cast_post0 q p lt r in
    p2 `hist_post_ord` p
  ) = ()

let rec lemma_io_subcomp
  (q1:pure_post 'a) (q2:pure_post 'a)
  (m : io (v:'a{q1 v})) :
  Lemma
    (requires (forall x. q1 x /\ x `return_of` m ==> q2 x))
    (ensures (theta m `hist_ord #_ #'a` theta (free_subcomp _ q1 q2 m))) =
  match m with
  | Return x -> assert (theta m `hist_ord #_ #'a` theta (free_subcomp _ q1 q2 m)) by (compute ())
  | Call cmd arg k -> begin
    let fst : io_resm cmd -> hist (v:'a{q1 v}) = fun r -> theta (k r) in
    let snd : io_resm cmd -> hist (v:'a{q2 v}) = fun r -> theta (free_subcomp _ q1 q2 (k r)) in
    calc (==) {
      theta m;
      == {}
      theta (Call cmd arg k);
      == { _ by (compute ()) } // unfold theta
      hist_bind (io_wps cmd arg) (fun r -> theta (k r));
      == {}
      hist_bind (io_wps cmd arg) fst;
    };
    (** fst ==> snd /\ hist is monotonic **)
    introduce forall (p:hist_post 'a) h. hist_bind (io_wps cmd arg) fst p h ==> hist_bind (io_wps cmd arg) snd p h with begin 
      introduce forall (r:io_resm cmd). (fst r `hist_ord #event #'a` snd r) with begin
        lemma_io_subcomp q1 q2 (k r)
      end
    end;
    calc (==) {
      hist_bind (io_wps cmd arg) snd;
      == {}
      hist_bind (io_wps cmd arg) (fun r -> theta (free_subcomp _ q1 q2 (k r)));
      == { _ by (compute ()) }
      theta (Call cmd arg (fun r -> free_subcomp _ q1 q2 (k r)));
      == { _ by (compute ()) }
      theta (free_subcomp _ q1 q2 (Call cmd arg k));
      == {}
      theta (free_subcomp _ q1 q2 m);
    }
  end
  

let lemma_io_subcomp_2 (q:pure_post 'a) (m : io 'a) :
  Lemma 
    (requires (forall x. x `return_of` m ==> q x))
    (ensures (forall p h. theta m (cast_post0 q p) h ==> theta (free_subcomp _ (fun _ -> True) q m) p h)) =
  introduce forall p h. (theta m (cast_post0 q p) h ==> theta (free_subcomp _ (fun _ -> True) q m) p h) with begin 
    introduce theta m (cast_post0 q p) h ==> (theta (free_subcomp _ (fun _ -> True) q m) p h) with _. begin 
      assert (theta m (cast_post0 q p) h);
      lemma_io_subcomp (fun _ -> True) q m;
      assert (theta (free_subcomp _ (fun _ -> True) q m) p h)
    end
  end

let lemma_theta_cast_post_implies_theta_refine_io (d:dm 'a 'wp) (q:pure_post 'a) :
  Lemma (requires (forall x. x `return_of` d ==> q x))
        (ensures (forall p h. theta d (cast_post q p) h ==> theta (refine_io d q) p h)) =
  lemma_io_subcomp_2 q d
  
let lemma_refine_io_refine_hist (d:dm 'a 'wp) (q:pure_post 'a) : 
  Lemma
    (requires (forall x. x `return_of` d ==> q x))
    (ensures (refine_hist 'wp q `hist_ord` theta (refine_io d q))) =
  assert ('wp `hist_ord` theta d);
  lemma_refine_hist_implies_weaken_post 'wp q;
  assert (forall p h. refine_hist 'wp q p h ==> theta d (cast_post q p) h);
  lemma_theta_cast_post_implies_theta_refine_io d q;
  assert (forall p h. theta d (cast_post q p) h ==> theta (refine_io d q) p h)
  
let refine_dm (d:dm 'a 'wp) (q:pure_post 'a) : 
  Pure (dm (v:'a{q v}) (refine_hist 'wp q))
    (requires (forall x. x `return_of` d ==> q x))
    (ensures (fun _ -> True)) =
  lemma_refine_io_refine_hist d q;
  refine_io d q
