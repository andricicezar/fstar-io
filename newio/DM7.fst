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

let pdm_return (a:Type) (x:a) : pdm a (hist_return x) =
 (| True, (fun _ -> dm_return _ x) |)

let pdm_bind (a b:Type)
  (wp1:hist a) (wp2:a -> hist b)
  (f:pdm a wp1) 
  (g:(x:a) -> pdm b (wp2 x)) :
  pdm b (hist_bind wp1 wp2) =
  let (| fpre, f |) = f in
  (| fpre, (fun _ -> dm_bind a b wp1 wp2 (f _) (fun x -> 
    let (| gpre, g |) = g x in 
    g _)) |)

let pdm_subcomp (a:Type) (wp1:hist a) (wp2:hist a) (f:pdm a wp1) :
  Pure (pdm a wp2)
    (requires (
      (wp2 `hist_ord` wp1)))
    (ensures fun _ -> True) =
  fun ((| pre, pres |)) -> dm_subcomp a wp1 wp2 (f (| pre, pres |))

  
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
  (f:(eqtype_as_type unit -> PURE a w))
  (pre : pure_pre { forall p h. (wp_lift_pure_hist w) p h ==> pre })
  (spre:squash pre) : 
  dm a (wp_lift_pure_hist w) =
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    assume (pre == as_requires w);
    let r = f () in
    let r' = dm_return _ r in
    dm_subcomp _ _ _ r'

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
  IOwp?.reflect (fun _ -> io_call cmd argz)

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
