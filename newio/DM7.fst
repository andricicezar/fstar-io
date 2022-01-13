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

(** the behavior of f can differ based on the history in iio **)
let exists_trace_of (x:'a) (m:io 'a) =
  exists lt. trace_of lt m x

let rec lemma_return_of_implies_exists_trace_of (x:'a) (m:io 'a) : 
  Lemma
    (requires (x `return_of` m))
    (ensures (exists_trace_of x m)) =
  match m with
  | Return _ -> assert (trace_of [] m x)
  | Call cmd arg k -> begin
    eliminate exists r. (x `return_of` (k r)) returns (exists_trace_of x m) with _. begin
      lemma_return_of_implies_exists_trace_of x (k r);
      assert (exists klt. trace_of klt (k r) x) by (assumption ());
      eliminate exists klt. trace_of klt (k r) x returns (exists_trace_of x m) with _. begin
        let e = convert_call_to_event cmd arg r in
        introduce exists lt. (trace_of lt m x) with (e::klt) and begin
          assert (trace_of (e::klt) m x)
        end
      end
    end
  end

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
    (ensures (exists lt. wp2 x (fun lt' r' -> p (lt @ lt') r') (List.rev lt @ h))) =
  lemma_theta_result_implies_post m (fun lt r -> wp2 r (fun lt' r' -> p (lt @ lt') r') (rev lt @ h)) h;
  lemma_return_of_implies_exists_trace_of x m

let lemma_hist_bind_implies_wp2
  (wp1:hist 'a) (wp2:'a -> hist 'b)
  (m:pdm 'a wp1) 
  p h x :
  Lemma 
    (requires (hist_bind wp1 wp2 p h /\ x `return_of` (get_fun m)))
    (ensures (exists lt. wp2 x  (fun lt' r' -> p (lt @ lt') r') (List.rev lt @ h))) =
  lemma_hist_bind_implies_wp2_0 wp1 wp2 (get_fun m) p h x

let pdm_bind (a b:Type)
  (wp1:hist a) (wp2:a -> hist b)
  (f:pdm a wp1) 
  (g:(x:a) -> pdm b (wp2 x)) :
  pdm b (hist_bind wp1 wp2) =
  Classical.forall_intro_3 (Classical.move_requires_3 (lemma_hist_bind_implies_wp2 wp1 wp2 f));
  (| (get_pre f /\ (forall x. x `return_of` (get_fun f) ==> get_pre (g x))), 
     (fun _ -> dm_bind a b wp1 wp2 (get_fun f) (fun x -> get_fun (g x))) 
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

let lemma_another #a #event w :
  Lemma (forall (p:hist_post #event a) h. wp_lift_pure_hist w p h ==> as_requires w) =
    assert (forall (p:hist_post #event a) x. p [] x ==> True) ;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity w ;
    assert (forall (p:hist_post #event a). w (fun x -> p [] x) ==> w (fun _ -> True))

let lift_pure_pdm (a : Type) 
  (w : pure_wp a)
  (f:(eqtype_as_type unit -> PURE a w)) : 
  pdm a (wp_lift_pure_hist w) =
  lemma_another #a #event w;
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
