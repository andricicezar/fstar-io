module PDM.IO.Respects

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open Hist
open DM.IO
open DM.IO.Refine

let pdm (a:Type) (wp:hist a) = 
  pre : pure_pre { forall p h. wp p h ==> pre } & (squash pre -> dm a wp)

let get_pre (t : pdm 'a 'wp) : Pure pure_pre (requires True) (ensures fun r -> forall post hist. 'wp post hist ==> r) =
  let (| pre , f |) = t in pre

let get_fun (t : pdm 'a 'wp) : Pure (dm 'a 'wp) (requires get_pre t) (ensures fun _ -> True) =
  let (| pre, f |) = t in f ()


(*** Defining the predicate needed, respects **)
(** the post-condition is written over an output value and local trace, therefore,
  `return_of` is not enough and we need predicates and lemmas that show that for 
  each x that is a returned value by m, also exists a local trace **)
  
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
        assert (trace_of klt (k res') x);
        assert (hist_post_shift p [convert_call_to_event cmd arg res'] klt x)
      end
    end
  end

(** here is Theo's idea with respects **)
let respects (x:'a) (d:dm 'a 'wp) : Type0 =
  forall (h:trace) (p:hist_post #event 'a). 'wp p h ==> (exists (lt:trace). p lt x)

(** and we show that return_of implies respects **)
let lemma_return_of_implies_respects (d:dm 'a 'wp) :
  Lemma (forall x. x `return_of` d ==> x `respects` d) = 
  assert ('wp `hist_ord` theta d);
  introduce forall x. x `return_of` d ==> x `respects` d with begin
    introduce x `return_of` d ==> x `respects` d with _. begin
      lemma_return_of_implies_exists_trace_of d x;
      Classical.forall_intro_2 (Classical.move_requires_2 (lemma_theta_result_implies_post d));
      assert (x `respects` d)
    end
  end

let new_pre0 (d1:pdm 'a 'wp1) (d2:(x:'a) -> pdm 'b ('wp2 x)) : Type0 =
  get_pre d1 /\ (forall (x:'a). x `respects` (get_fun d1) ==> get_pre (d2 x))

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
          assert ('wp1 p' h ==> (exists (lt:trace). p' lt x)) (** the refinement of d1's pre **);
          assert ('wp1 p' h); (** this is hist bind **)
          assert (exists (lt:trace). p' lt x); (** from the previous two, results this **)
          assert (exists (lt:trace). 'wp2 x (fun lt' r' -> p (lt @ lt') r') (rev lt @ h)); (** unfolding p' **)
          assert ((forall (lt:trace). 'wp2 x (fun lt' r' -> p (lt @ lt') r') (rev lt @ h)) ==> get_pre (d2 x)) (** the refinement of d2's pre **);
          assert (exists (lt:trace). get_pre (d2 x)); (** from the previous two **)
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

(*** Defining the PDM **)
let pdm_return (a:Type) (x:a) : pdm a (hist_return x) =
 (| True, (fun _ -> dm_return _ x) |)
 
let pdm_bind (a b:Type)
  (wp1:hist #event a) (wp2:a -> hist #event b)
  (f:pdm a wp1) 
  (g:(x:a) -> pdm b (wp2 x)) :
  pdm b (hist_bind wp1 wp2) =
  (| new_pre' f g, 
     (fun _ -> 
       lemma1 f g;
       lemma_return_of_implies_respects (get_fun f);
       let f'' = refine_dm (get_fun f) (fun x -> x `respects` (get_fun f)) in
       dm_bind _ _ _ _ f'' (fun x -> 
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
