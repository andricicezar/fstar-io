module PDM.IIO.Respects

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open DM.IIO
open Hist 

(*** not working **)

let pdm (a:Type) (wp:hist a) = 
  pre : pure_pre { forall p h. wp p h ==> pre } & (squash pre -> dm a wp)

let get_pre (t : pdm 'a 'wp) : Pure pure_pre (requires True) (ensures fun r -> forall post hist. 'wp post hist ==> r) =
  let (| pre , f |) = t in pre

let get_fun (t : pdm 'a 'wp) : Pure (dm 'a 'wp) (requires get_pre t) (ensures fun _ -> True) =
  let (| pre, f |) = t in f ()



let rec return_of_dm (x:'a) (f:iio 'a) (h:trace) =
  match f with
  | Return x' -> x == x'
  | Call GetTrace arg k -> return_of_dm x (k h) h
  | Call cmd arg k ->
     exists r'. return_of_dm x (k r') (convert_call_to_event cmd arg r' :: h)

// let lemma_return_of_dm (x:'a) (f:iio 'a) (h:trace) :
//  Lemma (x `return_of` f ==> (exists h. return_of_dm x f h)) = ()
  
let rec trace_of (h:trace) (m:iio 'a) (lt:trace) (x:'a) : Tot Type0 (decreases m) =
  match lt, m with
  | [], Return x' -> x == x'
  | _, Call GetTrace arg k -> trace_of h (k h) lt x
  | e::es, Call cmd arg k -> 
     (let (| cmd', arg', res' |) = destruct_event e in 
          (cmd' == cmd /\ arg == arg' /\ (trace_of (e::h) (k res') es x)))
  | _, _ -> False

let exists_trace_of (h:trace) (m:iio 'a) (x:'a) =
  exists lt. trace_of h m lt x

let rec lemma_return_of_implies_exists_trace_of (h:trace) (m:iio 'a) (x:'a) : 
  Lemma
    (requires (return_of_dm x m h))
    (ensures (exists_trace_of h m x))
    (decreases m) =
  match m with
  | Return _ -> assert (trace_of h m [] x)
  | Call GetTrace arg k -> 
    lemma_return_of_implies_exists_trace_of h (k h) x
  | Call cmd arg k -> begin
    assert (exists r. return_of_dm x (k r) ((convert_call_to_event cmd arg r)::h));
    eliminate exists r. return_of_dm x (k r) ((convert_call_to_event cmd arg r)::h) returns (exists_trace_of h m x) with _. begin
      let e = convert_call_to_event cmd arg r in
      lemma_return_of_implies_exists_trace_of (e::h) (k r) x;
      assert (exists klt. trace_of (e::h) (k r) klt x) by (assumption ());
      eliminate exists klt. trace_of (e::h) (k r) klt x returns (exists_trace_of h m x) with _. begin
        introduce exists lt. (trace_of h m lt x) with (e::klt) and begin
          assert (trace_of h m (e::klt) x)
        end
      end
    end
  end

unfold let cast_trace (h:trace) : iio_sig.res GetTrace = h

let lemma_theta_some (k:iio_sig.res GetTrace -> iio 'a) (p:hist_post #event 'a) (h:trace) :
  Lemma 
    (requires (theta (Call GetTrace () k) p h))
    (ensures (theta (k (cast_trace h)) p h)) by (ExtraTactics.blowup ()) = ()

(** this lemma is not robust, don't sure why yet **)
#push-options "--quake 1/10"
let rec lemma_theta_result_implies_post (m:iio 'a) (p:hist_post #event 'a) (h:trace) : 
  Lemma 
    (requires theta m p h) 
    (ensures (forall x lt. trace_of h m lt x ==> p lt x)) =
      match m with
      | Return _ -> ()
      | Call GetTrace arg k ->
        lemma_theta_some #'a k p h;
        let m' = k (cast_trace h) in
        lemma_theta_result_implies_post #'a m' p h
      | Call cmd arg k -> begin
        introduce forall x lt. trace_of h m lt x ==> p lt x with begin
          introduce trace_of h m lt x ==> p lt x with _. begin
            let e::klt = lt in
            let (| _, _, res' |) = destruct_event e in
            let e' = convert_call_to_event cmd arg res' in
            let p' = hist_post_shift p [e'] in
            let h' = e' :: h in
            assert (theta (k res') p' h');
            lemma_theta_result_implies_post #'a (k res') p' h';
            assert (trace_of h' (k res') klt x);
            assert (p' klt x)
          end
        end
  end
#reset-options

let respects (x:'a) (d:dm 'a 'wp) : Type0 =
  forall (h:trace) (p:hist_post #event 'a). 'wp p h ==> (exists (lt:trace). p lt x)

let lemma_return_of_implies_respects (d:dm 'a 'wp) :
  Lemma (forall x. x `return_of` d ==> x `respects` d) =
  introduce forall x. x `return_of` d ==> x `respects` d with begin
    introduce x `return_of` d ==> x `respects` d with _. begin
      introduce forall (h:trace) (p:hist_post #event 'a). 'wp p h ==> return_of_dm x d h ==> (exists (lt:trace). p lt x) with begin
        introduce 'wp p h ==> (return_of_dm x d h ==> (exists (lt:trace). p lt x)) with _. begin
          introduce return_of_dm x d h ==> (exists (lt:trace). p lt x) with _. begin
            assert (return_of_dm x d h);
            lemma_return_of_implies_exists_trace_of h d x;
            assert (exists lt. trace_of h d lt x);
            lemma_theta_result_implies_post d p h;
            assert (exists lt. p lt x)
          end
        end
      end
    end
  end

let new_pre0 (d1:pdm 'a 'wp1) (d2:(x:'a) -> pdm 'b ('wp2 x)) : Type0 =
  get_pre d1 /\ (forall x. x `respects` (get_fun d1) ==> get_pre (d2 x))

let lemma_new_pre0_0 (d1:pdm 'a 'wp1) (d2:(x:'a) -> pdm 'b ('wp2 x)) :
  Lemma (forall p h. hist_bind 'wp1 'wp2 p h ==> get_pre d1) = ()

let lemma_new_pre0_1 (d1:pdm 'a 'wp1) (d2:(x:'a) -> pdm 'b ('wp2 x)) :
  Lemma (forall p h. hist_bind 'wp1 'wp2 p h ==>
  	   (forall x. x `respects` (get_fun d1) ==> get_pre (d2 x))) =
  introduce forall p h. hist_bind 'wp1 'wp2 p h ==> (forall x. x `respects` (get_fun d1) ==> get_pre (d2 x)) with begin
    introduce hist_bind 'wp1 'wp2 p h ==> (forall x. x `respects` (get_fun d1) ==> get_pre (d2 x)) with _. begin
      introduce forall x. x `respects` (get_fun d1) ==> get_pre (d2 x) with begin
        introduce x `respects` (get_fun d1) ==> get_pre (d2 x) with _. begin
          let p':hist_post #event 'a = (fun lt r -> 'wp2 r (fun lt' r' -> p (lt @ lt') r') (rev lt @ h)) in
          assert ('wp1 p' h ==> return_of_dm x (get_fun d1) h ==> (exists (lt:trace). p' lt x));
          assert ('wp1 p' h); (** this is hist bind **)
          assume (return_of_dm x (get_fun d1) h);
          assert (return_of_dm x (get_fun d1) h ==> (exists (lt:trace). p' lt x));
          assert (exists (lt:trace). 'wp2 x (fun lt' r' -> p (lt @ lt') r') (rev lt @ h));
          assert ((forall (lt:trace). 'wp2 x (fun lt' r' -> p (lt @ lt') r') (rev lt @ h)) ==> get_pre (d2 x));
          admit ();
          assert (get_pre (d2 x))
        end
      end
    end
  end

let lemma_new_pre0 (d1:pdm 'a 'wp1) (d2:(x:'a) -> pdm 'b ('wp2 x)) :
  Lemma (forall p h. hist_bind 'wp1 'wp2 p h ==> new_pre0 d1 d2) =
  lemma_new_pre0_0 d1 d2;
  lemma_new_pre0_1 d1 d2

let new_pre (d1:pdm 'a 'wp1) (d2:(x:'a) -> pdm 'b ('wp2 x)) : (pre:pure_pre {forall p h. hist_bind 'wp1 'wp2 p h ==> pre}) =
  lemma_new_pre0 d1 d2;
  new_pre0 d1 d2

[@@ "opaque_to_smt"]
let new_pre' (d1:pdm 'a 'wp1) (d2:(x:'a) -> pdm 'b ('wp2 x)) : (pre:pure_pre {forall p h. hist_bind 'wp1 'wp2 p h ==> pre}) =
    new_pre d1 d2

let lemma1  (d1:pdm 'a 'wp1) (d2:(x:'a) -> pdm 'b ('wp2 x)) :
    Lemma (new_pre' d1 d2 ==> get_pre d1) by (unfold_def (`new_pre'))= ()

let lemma2  (d1:pdm 'a 'wp1) (d2:(x:'a) -> pdm 'b ('wp2 x)) :
    Lemma (new_pre' d1 d2 ==> (forall x. x `respects` (get_fun d1) ==> get_pre (d2 x))) by (unfold_def (`new_pre')) = ()
