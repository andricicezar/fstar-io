module DM7

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open Hist
open DM

let pdm (a:Type) (wp:hist a) = 
  pre : pure_pre { forall p h. wp p h ==> pre } & (squash pre -> dm a wp)

let get_pre #a #w (t : pdm a w) : Pure pure_pre (requires True) (ensures fun r -> forall post hist. w post hist ==> r) =
  let (| pre , f |) = t in pre

let get_fun #a #w (t : pdm a w) : Pure (dm a w) (requires get_pre t) (ensures fun _ -> True) =
  let (| pre, f |) = t in f ()

let pdm_return (a:Type) (x:a) : pdm a (hist_return x) =
 (| True, (fun _ -> dm_return _ x) |)

let hist_post_return (lt:trace) (x:'a) : hist_post 'a = fun lt' x' -> x == x' /\ lt == lt'

(** the behavior of f can differ based on the history in iio **)
let exists_trace (x:'a) (f:io 'a) =
  exists lt. forall h. theta f (hist_post_return lt x) h

let lemma_empty_traces_are_equal () :
  Lemma (forall (t1 t2:trace). t1 == [] /\ t2 == [] ==> t1 == t2) = ()

let emptyTrace : trace = []

let lemma_theta_step cmd arg k r h klt x:
  Lemma (requires (
    let e = convert_call_to_event cmd arg r in
    x `return_of` (k r) /\ x `return_of` (Call cmd arg k) /\
    theta (k r) (hist_post_return klt x) (e::h)))
    (ensures (
      let e = convert_call_to_event cmd arg r in
      theta (Call cmd arg k) (hist_post_return (e::klt) x) h)) = 
    let e = convert_call_to_event cmd arg r in
    let p = (hist_post_return (e::klt) x) in
    // fun lt' x' -> x == x' /\ lt == lt'
    calc (==) {
      theta (Call cmd arg k) p h;
      == { _ by (compute ())}
      hist_bind (io_wps cmd arg) (fun r -> theta (k r)) p h;
      == {}
      (io_wps cmd arg) (hist_post_bind h (fun r -> theta (k r)) p) h;
      == {_ by (compute ())}
      io_pre cmd arg h /\ (forall r. (hist_post_bind h (fun r -> theta (k r)) p) [convert_call_to_event cmd arg r] r);
      == {}
      io_pre cmd arg h /\ (forall r. (fun r -> theta (k r)) r (hist_post_shift p [convert_call_to_event cmd arg r]) (List.rev [convert_call_to_event cmd arg r] @ h));
      == {_ by (compute ())}
      io_pre cmd arg h /\ (forall r. theta (k r) (hist_post_shift p [convert_call_to_event cmd arg r]) (convert_call_to_event cmd arg r :: h));
    };
    admit ()

let rec lemma (x:'a) (f:io 'a) : 
  Lemma
    (requires (x `return_of` f))
    (ensures (exists_trace x f)) =
  match f with
  | Return _ -> begin
    lemma_empty_traces_are_equal ();

    assert (exists lt. forall h. hist_return #event x (hist_post_return lt x) h) 
    by (witness (`emptyTrace))
  end 
  | Call cmd arg k -> begin
    assert (exists r. (x `return_of` (k r)));
    eliminate exists r. (x `return_of` (k r)) returns (exists_trace x f) with _. begin
      assert (x `return_of` (k r));
      lemma x (k r);
      assert (exists lt. (forall h. theta (k r) (hist_post_return lt x) h)) by (assumption ());
      eliminate exists klt. (forall h. theta (k r) (hist_post_return klt x) h) returns (exists_trace x f) with _. begin
        let e = convert_call_to_event cmd arg r in
        introduce exists lt. (forall h. theta f (hist_post_return lt x) h) with (e::klt) and begin
          introduce forall h. (theta f (hist_post_return (e::klt) x) h) with begin 
            eliminate forall h'. theta (k r) (hist_post_return klt x) h' with (e::h);
            lemma_theta_step cmd arg k r h klt x
          end
        end
      end
    end
  end

(** this is to complicated for io, but may be needed for iio: 
let rec trace_of (lt:trace) (m:io 'a) (x:'a) =
  match lt, m with
  | [], Return x' -> x == x'
  | [], Call cmd arg k -> (forall h. io_wps cmd arg (fun lt r -> lt == []) h) /\ (forall r. trace_of lt (k r) x)
  | e::es, Call cmd arg k -> 
          // either this is a silent call so we skip
          ((forall h. io_wps cmd arg (fun lt r -> lt == []) h) /\ (forall r. trace_of lt (k r) x)) \/
          // either this call has an event on the local trace
          (let (| cmd', arg', res' |) = destruct_event e in 
            (cmd' == cmd /\ arg == arg' /\ (trace_of es (k res') x)))
  | _, _ -> False **)
let rec trace_of (lt:trace) (m:io 'a) (x:'a) =
  match lt, m with
  | [], Return x' -> x == x'
  | e::es, Call cmd arg k -> 
     (let (| cmd', arg', res' |) = destruct_event e in 
          (cmd' == cmd /\ arg == arg' /\ (trace_of es (k res') x)))
  | _, _ -> False

(** maybe worth thinking about a way to avoid using a different function: 
let exact_2 x y = fun x' y' -> x == x' /\ y == y'

let rec lemma_more_general_law m p h : 
  Lemma 
    (requires theta m p h) 
    (ensures (forall lt x. theta m (exact_2 lt x) h ==> p lt x)) = () **)
  
let rec lemma_theta_result_implies_post m p h : 
  Lemma 
    (requires theta m p h) 
    (ensures (forall x lt. trace_of lt m x ==> p lt x)) =
  introduce forall lt x. trace_of lt m x ==> p lt x with begin
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

let lemma_hist_bind_implies_wp2_0
  (wp1:hist 'a) (wp2:'a -> hist 'b)
  (m:dm 'a wp1) 
  p h x :
  Lemma 
    (requires (hist_bind wp1 wp2 p h /\ x `return_of` m))
    (ensures (exists lt. wp2 x (fun lt' r' -> p (lt @ lt') r') (List.rev lt @ h))) by (
      ExtraTactics.blowup ();
      bump_nth 2;
      ExtraTactics.rewrite_lemma 9 12; 
      let lem = ExtraTactics.get_binder 11 in
      let bx = ExtraTactics.get_binder 7 in
      tadmit ();
      dump "H"
    ) = 
  lemma_theta_result_implies_post m (fun lt r -> wp2 r (fun lt' r' -> p (lt @ lt') r') (rev lt @ h)) h

let lemma_hist_bind_implies_wp2
  (wp1:hist 'a) (wp2:'a -> hist 'b)
  (m:pdm 'a wp1) 
  p h x :
  Lemma 
    (requires (hist_bind wp1 wp2 p h /\ x `return_of` (get_fun m)))
    (ensures (exists lt. wp2 x p (List.rev lt @ h))) =
  lemma_hist_bind_implies_wp2_0 wp1 wp2 (get_fun m) p h x

let glue_lemma (wp:'a -> hist 'b) (pre:Type0) : Lemma
  (requires ((forall p h x. wp x p h ==> pre) /\ 
             (forall p h x. exists lt. wp x p (List.rev lt @ h))))
  (ensures pre) by (
    ExtraTactics.blowup ();
    dump "h"
  )= admit ()

let pdm_bind (a b:Type)
  (wp1:hist a) (wp2:a -> hist b)
  (f:pdm a wp1) 
  (g:(x:a) -> pdm b (wp2 x)) :
  pdm b (hist_bind wp1 wp2) =
  Classical.forall_intro_3 (Classical.move_requires_3 (lemma_hist_bind_implies_wp2 wp1 wp2 f));
  assert (forall p h x. (hist_bind wp1 wp2 p h /\ x `return_of` (get_fun f)) ==>
            (exists lt. wp2 x p (List.rev lt @ h)));
  assert (forall p h x. wp2 x p h ==> get_pre (g x));
  assume ((forall p h x. exists lt. wp2 x p (List.rev lt @ h)) ==> (forall p h x. wp2 x p h));
  assert (forall p h x. hist_bind wp1 wp2 p h /\ x `return_of` (get_fun f) ==> get_pre (g x));
  (| (get_pre f /\ (forall x. x `return_of` (get_fun f) ==> get_pre (g x))), 
     (fun _ -> dm_bind a b wp1 wp2 (get_fun f) (fun x -> 
       get_fun (g x))) |)

let pdm_subcomp (a:Type) (wp1:hist a) (wp2:hist a) (f:pdm a wp1) :
  Pure (pdm a wp2)
    (requires (
      (wp2 `hist_ord` wp1)))
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
  pdm a
    (hist_if_then_else wp1 wp2 b)

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
  assume (forall (p:hist_post a) h. wp_lift_pure_hist #a w p h ==> as_requires w);
  admit ();
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
