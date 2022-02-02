module DM

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open Hist

unfold let io_wps (cmd:io_cmds) (arg:io_args cmd) : hist #event (io_resm cmd) = fun p h ->
  match cmd with
 // | GetTrace -> p [] h
  | _ -> io_pre cmd arg h /\ (forall r. p [convert_call_to_event cmd arg r] r)

(** Inspierd from Kenji's thesis (2.4.5) **)
let rec theta #a
  (m : io a) : hist a =
  match m with
  | Return x -> hist_return x
  | Call cmd arg k ->
    hist_bind (io_wps cmd arg) (fun r -> theta (k r))
  
let lemma_theta_is_monad_morphism_ret v h p :
  Lemma (theta (io_return v) == hist_return v) by (compute ()) = ()

(** TODO: remove the admits **)
let rec lemma_theta_is_monad_morphism_bind (m:io 'a) (f:(x:'a) -> io 'b) :
  Lemma
    (theta (io_bind m f) == hist_bind (theta m) (fun x -> theta (f x))) = 
  match m with
  | Return x ->
    calc (==) {
      theta (io_bind m f);
      == {}
      theta (io_bind (Return x) f);
      == {} // unfold io_bind
      theta (f x); 
      == { _ by (tadmit ()) } // unfold hist_bind
      hist_bind (hist_return x) (fun x -> theta (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (theta (Return x)) (fun x -> theta (f x));
    };
    (** this should be inside calc, but for some reason it fails there **)
    assert (hist_bind (theta (Return x)) (fun x -> theta (f x))
      == hist_bind (theta m) (fun x -> theta (f x))) by (rewrite_eqs_from_context ())
  | Call cmd arg k ->
    (** this should be useful later to do a rewrite **)
    introduce forall (r:io_resm cmd). theta (io_bind (k r) f) == hist_bind (theta (k r)) (fun x -> theta (f x)) with begin
      lemma_theta_is_monad_morphism_bind (k r) f
    end;

    calc (==) {
      theta (io_bind m f);
      == {}
      theta (io_bind (Call cmd arg k) f);
      == { _ by (compute ()) } // unfold io_bind
      theta (Call cmd arg (fun r -> io_bind (k r) f));
      == { _ by (compute ()) } // unfold theta
      hist_bind (io_wps cmd arg) (fun r -> theta (io_bind (k r) f));
      == { _ by (tadmit ()) } // rewrite here by applying this lemma again for (k r) and f
      hist_bind (io_wps cmd arg) (fun r -> hist_bind (theta (k r)) (fun x -> theta (f x)));
      == { lemma_hist_bind_associativity (io_wps cmd arg) (fun r -> theta (k r)) (fun x -> theta (f x)) }
      hist_bind (hist_bind (io_wps cmd arg) (fun r -> theta (k r))) (fun x -> theta (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (theta (Call cmd arg k)) (fun x -> theta (f x));
    };
    (** this should be inside calc, but for some reason it fails there **)
    assert (hist_bind (theta (Call cmd arg k)) (fun x -> theta (f x))
      == hist_bind (theta m) (fun x -> theta (f x))) by (rewrite_eqs_from_context ())

// The Dijkstra Monad
let dm (a:Type) (wp:hist a) =
  (m:(io a){wp `hist_ord` theta m})

let dm_return (a : Type) (x : a) : dm a (hist_return x) =
  io_return x

let dm_bind
  (a b : Type)
  (wp_v : hist a)
  (wp_f: a -> hist b)
  (v : dm a wp_v)
  (f : (x:a -> dm b (wp_f x))) :
  Tot (dm b (hist_bind wp_v wp_f)) =
  lemma_theta_is_monad_morphism_bind v f;
  io_bind v f

let dm_subcomp (a:Type) (wp1 wp2: hist a) (f : dm a wp1) :
  Pure (dm a wp2)
    (requires hist_ord wp2 wp1)
    (ensures fun _ -> True) =
  f

let dm_if_then_else (a : Type) (wp1 wp2: hist a) (f : dm a wp1) (g : dm a wp2) (b : bool) : Type =
  dm a (hist_if_then_else wp1 wp2 b)

(*** new repr for dm **)
let rec io_subcomp (a:Type)
  (q1:pure_post a) (q2:pure_post a)
  (m : io (v:a{q1 v})) :
  Pure (io (v:a{q2 v})) 
    (requires (forall x. x `return_of` m /\ q1 x ==> q2 x))
    (ensures (fun r -> True)) =
  match m with
  | Return r -> Return r
  | Call cmd arg k -> 
      Call cmd arg (fun r -> 
        io_subcomp _ q1 q2 (k r))

let respects (x:'a) (wp:hist #event 'a) : Type0 =
  forall (h:trace) (p:hist_post #event 'a). wp p h ==> (exists (lt:trace). p lt x)

let resp (wp:hist 'a) = x:'a{x `respects` wp}
let resph (wp:hist 'a) = hist #event (resp wp) 

let rec trace_of (lt:trace) (m:io 'a) (x:'a) =
  match lt, m with
  | [], Return x' -> x == x'
  | e::es, Call cmd arg k -> 
     (let (| cmd', arg', res' |) = destruct_event e in 
          (cmd' == cmd /\ arg == arg' /\ (trace_of es (k res') x)))
  | _, _ -> False

let exists_trace_of (x:'a) (m:io 'a) =
  exists lt. trace_of lt m x

let rec lemma_return_of_implies_exists_trace_of (m:io 'a) (x:'a) : 
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
        let e = convert_call_to_event cmd arg r in
        introduce exists lt. (trace_of lt m x) with (e::klt) and begin
          assert (trace_of (e::klt) m x)
        end
      end
    end
  end

(** this proof is not robust, sometimes it passes, sometimes it is not **)
let rec lemma_theta_result_implies_post m p h : 
  Lemma 
    (requires theta m p h) 
    (ensures (forall x lt. trace_of lt m x ==> p lt x)) =
  introduce forall x lt. trace_of lt m x ==> p lt x with begin
    introduce trace_of lt m x ==> p lt x with _. begin
      match m with
      | Return _ -> ()
      | Call cmd arg k -> begin
        let e::klt = lt in
        let (| cmd', arg', res' |) = destruct_event e in
        lemma_theta_result_implies_post (k res') (hist_post_shift p [convert_call_to_event cmd arg res']) (convert_call_to_event cmd arg res' :: h);
        assert (trace_of klt (k res') x) by (smt ());
        assert (hist_post_shift p [convert_call_to_event cmd arg res'] klt x) by (smt ())
      end
    end
  end


unfold
let refine_io (wp:hist 'a) (d:dm 'a wp) : io (resp wp) =
  assert (wp `hist_ord` theta d);
  introduce forall x. x `return_of` d ==> x `respects` wp with begin
    introduce x `return_of` d ==> x `respects` wp with _. begin
      lemma_return_of_implies_exists_trace_of d x;
      Classical.forall_intro_2 (Classical.move_requires_2 (lemma_theta_result_implies_post d));
      assert (x `respects` wp)
    end
  end;
  io_subcomp _ (fun _ -> True) (fun x -> respects x wp) d

unfold
let refine_post0 (q:pure_post 'a) (p:hist_post (v:'a{q v})) : hist_post 'a =
  (fun lt (r:'a) -> q r ==> p lt r)

let lemma_refine_post0 (q:pure_post 'a) (p:hist_post (v:'a{q v})) :
  Lemma (
    let p1 : hist_post (v:'a{q v}) = p in
    let p2 : hist_post (v:'a{q v}) = fun lt r -> refine_post0 q p lt r in
    p2 `hist_post_ord` p1
  ) = ()

unfold
let refine_post (wp:hist 'a) (p : hist_post (resp wp)) : hist_post 'a = 
  refine_post0 (fun x -> x `respects` wp) p

let refine_hist (wp:hist 'a) : resph wp = 
  let newhist : hist0 (resp wp) = (fun p -> wp (refine_post wp p)) in
  assert (hist_wp_monotonic newhist);
  newhist

let dm' (a:Type) (wp:hist a) = dm (resp wp) (refine_hist wp)

let lemma_step_1 (a:Type) (wp:hist a) : Lemma (
  forall (p:hist_post a) h. refine_hist wp p h ==> wp (refine_post wp p) h) = ()
  
let lemma_step_2 (a:Type) (wp:hist a) (m:io a) : Lemma
  (requires (wp `hist_ord` theta m))
  (ensures (
    forall (p:hist_post a) h. wp (refine_post wp p) h ==> theta m (refine_post wp p) h)) = ()

(** lemma is not robust **)
let rec lemma_io_subcomp (a:Type)
  (q1:pure_post a) (q2:pure_post a)
  (m : io (v:a{q1 v})) :
  Lemma
    (requires (forall x. q1 x /\ x `return_of` m ==> q2 x))
    (ensures (theta m `hist_ord #_ #a` theta (io_subcomp _ q1 q2 m))) =
  match m with
  | Return x -> assert (theta m `hist_ord #_ #a` theta (io_subcomp _ q1 q2 m)) by (compute ())
  | Call cmd arg k -> begin
    let fst : io_resm cmd -> hist (v:a{q1 v}) = fun r -> theta (k r) in
    let snd : io_resm cmd -> hist (v:a{q2 v}) = fun r -> theta (io_subcomp _ q1 q2 (k r)) in
    calc (==) {
      theta m;
      == {}
      theta (Call cmd arg k);
      == { _ by (compute ()) } // unfold theta
      hist_bind (io_wps cmd arg) (fun r -> theta (k r));
      == {}
      hist_bind (io_wps cmd arg) fst;
    };

    calc (==) {
      theta (io_subcomp _ q1 q2 m);
      == {}
      theta (io_subcomp _ q1 q2 (Call cmd arg k));
      == { _ by (compute ()) }
      theta (Call cmd arg (fun r -> io_subcomp _ q1 q2 (k r)));
      == { _ by (compute ()) }
      hist_bind (io_wps cmd arg) (fun r -> theta (io_subcomp _ q1 q2 (k r)));
      == {}
      hist_bind (io_wps cmd arg) snd;
    };

    introduce forall (r:io_resm cmd). (fst r `hist_ord #event #a` snd r) with begin
      lemma_io_subcomp _ q1 q2 (k r)
    end;
    introduce forall (p:hist_post a) h. hist_bind (io_wps cmd arg) fst p h ==> hist_bind (io_wps cmd arg) snd p h with begin 
      introduce hist_bind (io_wps cmd arg) fst p h ==> hist_bind (io_wps cmd arg) snd p h with _. begin
        assert (hist_bind (io_wps cmd arg) snd p h)
     end
    end
  end
  

(** lemma is not robust **)
let lemma_io_subcomp_2 (a:Type)
  (q2:pure_post a)
  (m : io a) :
  Lemma
    (requires (forall x. x `return_of` m ==> q2 x))
    (ensures (forall p h. theta m (refine_post0 q2 p) h ==>
                  theta (io_subcomp _ (fun _ -> True) q2 m) p h)) =
  introduce forall p h. (theta m (refine_post0 q2 p) h ==>
                  theta (io_subcomp _ (fun _ -> True) q2 m) p h) with begin 
    introduce theta m (refine_post0 q2 p) h ==>
                  (theta (io_subcomp _ (fun _ -> True) q2 m) p h) with _. begin 
      assert (theta m (refine_post0 q2 p) h);
      lemma_io_subcomp a (fun _ -> True) q2 m;
      assert (theta (io_subcomp _ (fun _ -> True) q2 m) p h)
    end
  end


let lemma_step_3 (a:Type) (wp:hist a) (d:dm a wp) :
  Lemma (forall p h. theta d (refine_post wp p) h ==> theta (refine_io wp d) p h) =
  assert (wp `hist_ord` theta d);
  introduce forall x. x `return_of` d ==> x `respects` wp with begin
    introduce x `return_of` d ==> x `respects` wp with _. begin
      lemma_return_of_implies_exists_trace_of d x;
      Classical.forall_intro_2 (Classical.move_requires_2 (lemma_theta_result_implies_post d));
      assert (x `respects` wp)
    end
  end;
  lemma_io_subcomp_2 a (fun x -> respects x wp) d

  
let lemma_refine_io_refine_hist (a:Type) (wp:hist a) (d:dm a wp) : Lemma (
  refine_hist wp `hist_ord` theta (refine_io wp d)) =
  assert (wp `hist_ord` theta d);
  let wp' = refine_hist wp in
  let d' = refine_io wp d in
  lemma_step_1 a wp;
  assert (forall (p:hist_post a) h. refine_hist wp p h ==> theta d (refine_post wp p) h);
 // lemma_step_2 a wp d;
  lemma_step_3 a wp d;
 // assert (wp `hist_ord` theta (refine_io wp d));
  assert (forall p h. theta d (refine_post wp p) h ==> theta (refine_io wp d) p h)
  

let lift_dm_dm' (a:Type) (wp:hist a) (d:dm a wp) : dm' a wp =
  lemma_refine_io_refine_hist _ wp d;
  refine_io wp d

