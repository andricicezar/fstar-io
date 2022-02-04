module PDM

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open Hist
open DM.IIO
open DM.IIO.Refine

let pdm (a:Type) (wp:hist a) = 
  pre : pure_pre { forall p h. wp p h ==> pre } & (squash pre -> dm a wp)

let get_pre #a #w (t : pdm a w) : Pure pure_pre (requires True) (ensures fun r -> forall post hist. w post hist ==> r) =
  let (| pre , f |) = t in pre

let get_fun #a #w (t : pdm a w) : Pure (dm a w) (requires get_pre t) (ensures fun _ -> True) =
  let (| pre, f |) = t in f ()

let pdm_return (a:Type) (x:a) : pdm a (hist_return x) =
 (| True, (fun _ -> dm_return _ x) |)
 
let rec return_of_dm (x:'a) (f:iio 'a) (h:trace) =
  match f with
  | Return x' -> x == x'
  | Call GetTrace arg k -> return_of_dm x (k h) h
  | Call cmd arg k ->
     exists r'. return_of_dm x (k r') (convert_call_to_event cmd arg r' :: h)
  
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
  
let value_of (x:'a) (d:dm 'a 'wp) : Type0 =
  (** if the precondition holds for the history, then the following implication holds:
        if x is a value returned by the dm, then exists a lt s.t. the post conidition holds for lt and x **)
  forall (p:hist_post #event 'a) (h:trace). 'wp p h ==> return_of_dm x d h ==> (exists (lt:trace). p lt x)

let lemma_return_of_implies_value_of (d:dm 'a 'wp) :
  Lemma (forall x. x `return_of` d ==> x `value_of` d) =
  introduce forall x. x `return_of` d ==> x `value_of` d with begin
    introduce x `return_of` d ==> x `value_of` d with _. begin
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
  get_pre d1 /\ (forall x. x `value_of` (get_fun d1) ==> get_pre (d2 x))

let lemma_new_pre0_0 (d1:pdm 'a 'wp1) (d2:(x:'a) -> pdm 'b ('wp2 x)) :
  Lemma (forall p h. hist_bind 'wp1 'wp2 p h ==> get_pre d1) = ()

let lemma_new_pre0_1 (d1:pdm 'a 'wp1) (d2:(x:'a) -> pdm 'b ('wp2 x)) :
  Lemma (forall p h. hist_bind 'wp1 'wp2 p h ==>
  	   (forall x. x `value_of` (get_fun d1) ==> get_pre (d2 x))) =
  introduce forall p h. hist_bind 'wp1 'wp2 p h ==> (forall x. x `value_of` (get_fun d1) ==> get_pre (d2 x)) with begin
    introduce hist_bind 'wp1 'wp2 p h ==> (forall x. x `value_of` (get_fun d1) ==> get_pre (d2 x)) with _. begin
      introduce forall x. x `value_of` (get_fun d1) ==> get_pre (d2 x) with begin
        introduce x `value_of` (get_fun d1) ==> get_pre (d2 x) with _. begin
          let p':hist_post #event 'a = (fun lt r -> 'wp2 r (fun lt' r -> p (lt @ lt') r) (rev lt @ h)) in
          assert ('wp1 p' h ==> return_of_dm x (get_fun d1) h ==> (exists (lt:trace). p' lt x));
          assert ('wp1 p' h); (** this is hist bind **)
          assert (return_of_dm x (get_fun d1) h);
          assert (exists (lt:trace). p' lt x);
          assert ('wp2 x p h ==> get_pre (d2 x));
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
    Lemma (new_pre' d1 d2 ==> (forall x. x `value_of` (get_fun d1) ==> get_pre (d2 x))) by (unfold_def (`new_pre')) = ()

let pdm_bind (a b:Type)
  (wp1:hist a) (wp2:a -> hist b)
  (f:pdm a wp1) 
  (g:(x:a) -> pdm b (wp2 x)) :
  pdm b (hist_bind wp1 wp2) =
  (| new_pre' f g, 
     (fun _ -> 
       lemma1 f g;
       dm_bind _ _ _ _ (refine_dm (get_fun f)) (fun x -> 
       	 lemma2 f g;
	 get_fun (g x))) 
   |)

let pdm_subcomp (a:Type) (wp1:hist a) (wp2:hist a) (f:pdm a wp1) :
  Pure (pdm a wp2)
    (requires (wp2 `hist_ord` wp1))
    (ensures fun _ -> True) =
  (| get_pre f, (fun _ -> dm_subcomp a wp1 wp2 (get_fun f)) |)

unfold
let pdm_if_then_else 
  (a : Type)
  (wp1: hist a)
  (wp2: hist a)
  (f : pdm a wp1)
  (g : pdm a wp2)
  (b : bool) : Type =
  pdm a (hist_if_then_else wp1 wp2 b)

total
reifiable
reflectable
effect {
  IOwp (a:Type) (wp : hist #event a) 
  with {
       repr       = pdm
     ; return     = pdm_return
     ; bind       = pdm_bind 
     ; subcomp    = pdm_subcomp
     ; if_then_else = pdm_if_then_else
     }
}

effect IO
  (a:Type)
  (pre : trace -> Type0)
  (post : trace -> trace -> a -> Type0) =
  IOwp a 
    (fun (p:hist_post a) (h:trace) -> pre h /\ (forall lt r. post h lt r ==>  p lt r)) 

let lift_pure_pdm (a : Type) 
  (w : pure_wp a)
  (f:(eqtype_as_type unit -> PURE a w)) : 
  pdm a (wp_lift_pure_hist w) =
  lemma_wp_lift_pure_hist_implies_as_requires #a #event w;
  (| as_requires w, (fun _ -> 
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    let r = f () in
    let r' = dm_return _ r in
    dm_subcomp _ _ _ r' ) |)

sub_effect PURE ~> IOwp = lift_pure_pdm
  
assume val p : prop
assume val p' : prop
assume val pure_lemma (_:unit) : Lemma p
assume val some_f (_:squash p) : IO unit (fun _ -> True) (fun _ _ _ -> True)
assume val some_f' : unit -> IO unit (requires (fun _ -> p)) (ensures fun _ _ _ -> p')

let test () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  pure_lemma ();
  some_f ()

let test'' () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  pure_lemma ();
  some_f ();
  some_f' ();
  assert p'

let static_cmd
  (cmd : io_cmds)
  (argz : io_args cmd) :
  IO (io_resm cmd)
    (requires (fun h -> io_pre cmd argz h))
    (ensures (fun h lt r ->
        lt == [convert_call_to_event cmd argz r])) =
  IOwp?.reflect (| True,  (fun _ -> io_call cmd argz) |)

let testStatic3 (fd:file_descr) : IO unit (fun h -> is_open fd h) (fun h lt r -> ~(is_open fd (List.rev lt @ h))) =
  let _ = static_cmd Close fd in
  ()

let testStatic2 () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  let fd = static_cmd Openfile "../Makefile" in
  if Some? fd then begin (** test if Openfile was successful **)
    let msg = static_cmd Read (Some?.v fd) in
    let _ = static_cmd Close (Some?.v fd) in
    ()
  end else ()
