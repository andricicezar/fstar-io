module DM.IIO.Refine

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open DM.IIO
open Hist

let respects (x:'a) (wp:hist #event 'a) : Type0 =
  forall (h:trace) (p:hist_post #event 'a). wp p h ==> (exists (lt:trace). p lt x)

let resp (wp:hist 'a) = x:'a{x `respects` wp}
let resph (wp:hist 'a) = hist #event (resp wp) 

let lemma_return_of_implies_respects (d:dm 'a 'wp) :
  Lemma (forall x. x `return_of` d ==> x `respects` 'wp) = 
  assert ('wp `hist_ord` theta d);
  introduce forall x. x `return_of` d ==> x `respects` 'wp with begin
    introduce x `return_of` d ==> x `respects` 'wp with _. begin
      admit ()
    end
  end

unfold
let refine_io (wp:hist 'a) (d:dm 'a wp) : iio (resp wp) =
  lemma_return_of_implies_respects d;
  free_subcomp _ (fun _ -> True) (fun x -> respects x wp) d

unfold
let cast_post0 (q:pure_post 'a) (p:hist_post (v:'a{q v})) : hist_post 'a =
  (fun lt (r:'a) -> q r ==> p lt r)

unfold
let cast_post (wp:hist 'a) (p : hist_post (resp wp)) : hist_post 'a = 
  cast_post0 (fun x -> x `respects` wp) p

let refine_hist (wp:hist 'a) : resph wp = 
  let newhist : hist0 (resp wp) = (fun p -> wp (cast_post wp p)) in
  assert (hist_wp_monotonic newhist);
  newhist

let lemma_refine_hist_implies_weaken_post (wp:hist 'a) : Lemma (
  forall (p:hist_post 'a) h. refine_hist wp p h ==> wp (cast_post wp p) h) = ()

let lemma_cast_post0 (q:pure_post 'a) (p:hist_post (v:'a{q v})) :
  Lemma (
    let p2 : hist_post (v:'a{q v}) = fun lt r -> cast_post0 q p lt r in
    p2 `hist_post_ord` p
  ) = ()

#push-options "--quake 1/10"
let rec lemma_io_subcomp
  (q1:pure_post 'a) (q2:pure_post 'a)
  (m : iio (v:'a{q1 v})) :
  Lemma
    (requires (forall x. q1 x /\ x `return_of` m ==> q2 x))
    (ensures (theta m `hist_ord #_ #'a` theta (free_subcomp _ q1 q2 m))) =
  match m with
  | Return x -> assert (theta m `hist_ord #_ #'a` theta (free_subcomp _ q1 q2 m)) by (compute ())
  | Call cmd arg k -> begin
    let fst : iio_sig.res cmd -> hist (v:'a{q1 v}) = fun r -> theta (k r) in
    let snd : iio_sig.res cmd -> hist (v:'a{q2 v}) = fun r -> theta (free_subcomp _ q1 q2 (k r)) in
    calc (==) {
      theta m;
      == {}
      theta (Call cmd arg k);
      == { _ by (compute ()) } // unfold theta
      hist_bind (iio_wps cmd arg) (fun r -> theta (k r));
      == {}
      hist_bind (iio_wps cmd arg) fst;
    };
    (** fst ==> snd /\ hist is monotonic **)
    introduce forall (p:hist_post 'a) h. hist_bind (iio_wps cmd arg) fst p h ==> hist_bind (iio_wps cmd arg) snd p h with begin 
      introduce forall (r:iio_sig.res cmd). (fst r `hist_ord #event #'a` snd r) with begin
        lemma_io_subcomp q1 q2 (k r)
      end
    end;
    calc (==) {
      hist_bind (iio_wps cmd arg) snd;
      == {}
      hist_bind (iio_wps cmd arg) (fun r -> theta (free_subcomp _ q1 q2 (k r)));
      == { _ by (compute ()) }
      theta (Call cmd arg (fun r -> free_subcomp _ q1 q2 (k r)));
      == { _ by (compute ()) }
      theta (free_subcomp _ q1 q2 (Call cmd arg k));
      == {}
      theta (free_subcomp _ q1 q2 m);
    }
  end
  

let lemma_io_subcomp_2 (q:pure_post 'a) (m : iio 'a) :
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

let lemma_theta_cast_post_implies_theta_refine_io (d:dm 'a 'wp) :
  Lemma (forall p h. theta d (cast_post 'wp p) h ==> theta (refine_io 'wp d) p h) =
  lemma_return_of_implies_respects d;
  lemma_io_subcomp_2 (fun x -> x `respects` 'wp) d
  
let lemma_refine_io_refine_hist (d:dm 'a 'wp) : 
  Lemma (refine_hist 'wp `hist_ord` theta (refine_io 'wp d)) =
  assert ('wp `hist_ord` theta d);
  lemma_refine_hist_implies_weaken_post 'wp;
  assert (forall p h. refine_hist 'wp p h ==> theta d (cast_post 'wp p) h);
  lemma_theta_cast_post_implies_theta_refine_io d;
  assert (forall p h. theta d (cast_post 'wp p) h ==> theta (refine_io 'wp d) p h)
  
let refine_dm (d:dm 'a 'wp) : dm (resp 'wp) (refine_hist 'wp) =
  lemma_refine_io_refine_hist d;
  refine_io 'wp d


