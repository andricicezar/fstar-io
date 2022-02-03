module DM.IIO.Refine

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open DM.IIO
open Hist

(** the post-condition is written over an output value and local trace, therefore,
  `return_of` is not enough and we need predicates and lemmas that show that for 
  each x that is a returned value by m, also exists a local trace **)
  
let rec trace_of (lt:trace) (m:iio 'a) (x:'a) =
  match lt, m with
  | _, Call GetTrace arg k -> exists h. trace_of lt (k h) x
  | [], Return x' -> x == x'
  | e::es, Call cmd arg k -> 
     (let (| cmd', arg', res' |) = destruct_event e in 
          (cmd' == cmd /\ arg == arg' /\ (trace_of es (k res') x)))
  | _, _ -> False

let exists_trace_of (x:'a) (m:iio 'a) =
  exists lt. trace_of lt m x

let rec lemma_return_of_implies_exists_trace_of (m:iio 'a) (x:'a) : 
  Lemma
    (requires (x `return_of` m))
    (ensures (exists_trace_of x m)) =
  match m with
  | Return _ -> assert (trace_of [] m x)
  | Call cmd arg k -> begin
    eliminate exists r. (x `return_of` (k r)) returns (exists_trace_of x m) with _. begin
      lemma_return_of_implies_exists_trace_of (k r) x;
      assert (exists klt. trace_of klt (k r) x) by (assumption ());
      eliminate exists klt. trace_of klt (k r) x returns (exists_trace_of x m) with _. begin
        match cmd with
        | GetTrace ->
          introduce exists lt. (trace_of lt m x) with klt and begin
            assert (exists (h: trace).
              iio_wps GetTrace arg (fun lt r -> lt == [] /\ r == h) h /\ trace_of klt (k h) x)
          end
        | _ -> begin
          let e = convert_call_to_event cmd arg r in
          introduce exists lt. (trace_of lt m x) with (e::klt) and begin
            assert (trace_of (e::klt) m x)
          end
        end
      end
    end
  end

unfold let cast_trace (h:trace) : iio_sig.res GetTrace = h

#push-options "--z3rlimit 10"
let rec lemma_theta_result_implies_post (m:iio 'a) (p:hist_post #event 'a) (h:trace) : 
  Lemma 
    (requires theta m p h) 
    (ensures (forall x lt. trace_of lt m x ==> p lt x)) =
    match m with
    | Call GetTrace arg k -> begin
      assert (theta (k h) p h);
      lemma_theta_result_implies_post (k h) p h;
      assert (forall x lt. trace_of lt (k h) x ==> p lt x);

      introduce forall x lt. trace_of lt (Call GetTrace arg k) x ==> trace_of lt (k h) x with begin
        introduce trace_of lt (Call GetTrace arg k) x ==> trace_of lt (k h) x with _. begin
          
          assert (iio_wps GetTrace arg (fun lt r -> lt == [] /\ r == h) h);
          assert (trace_of lt (Call GetTrace arg k) x);
          assert (trace_of lt (k h) x) by (
            let h = nth_binder 3 in
            let x = nth_binder (-7) in
 //           let y = nth_binder (-15) in
            binder_retype x;
              norm [delta_only [`%trace_of];zeta];
//              witness (`(`#h));
            trefl ();
//            let _ = ExtraTactics.apply_in x y in
            dump "H");
          admit ()
        end
      end;
      assert (forall x lt. trace_of lt m x ==> p lt x)
    end
    | _ -> admit ()
(**
    | Return _ -> ()
    | Call cmd arg k -> begin
      introduce forall x lt. trace_of lt m x ==> p lt x with begin
        introduce trace_of lt m x ==> p lt x with _. begin
          let e::klt = lt in
          let (| cmd', arg', res' |) = destruct_event e in
          let p' = (hist_post_shift p [convert_call_to_event cmd arg res']) in
          let h' = (convert_call_to_event cmd arg res' :: h) in
          assert (theta (k res') p' h');
          lemma_theta_result_implies_post (k res') p' h';
          assert (trace_of klt (k res') x);
          assert (p' klt x);
          assert (p lt x)
       end
     end
    end**)

let respects (x:'a) (wp:hist #event 'a) : Type0 =
  forall (h:trace) (p:hist_post #event 'a). wp p h ==> (exists (lt:trace). p lt x)

let resp (wp:hist 'a) = x:'a{x `respects` wp}
let resph (wp:hist 'a) = hist #event (resp wp) 

(** and we show that return_of implies respects **)
let lemma_return_of_implies_respects (d:dm 'a 'wp) :
  Lemma (forall x. x `return_of` d ==> x `respects` 'wp) = 
  assert ('wp `hist_ord` theta d);
  introduce forall x. x `return_of` d ==> x `respects` 'wp with begin
    introduce x `return_of` d ==> x `respects` 'wp with _. begin
      lemma_return_of_implies_exists_trace_of d x;
      Classical.forall_intro_2 (Classical.move_requires_2 (lemma_theta_result_implies_post d));
      assert (x `respects` 'wp)
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


