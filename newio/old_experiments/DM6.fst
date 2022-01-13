module DM6

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open Hist
open DM

(** The idea for this file is to make the DM partial by asking for the pre-condition
    of wp. Then, to prove the bind, I think a equivalent hist_bind is needed. I am not
    sure what properties this new hist_bind should have. **)

let pdm (a:Type) (wp:hist a) = 
  (post:hist_post a) & (squash (exists h. wp post h) -> dm a wp)

let pdm_return (a:Type) (x:a) : pdm a (hist_return x) =
  (| (fun lt r -> r == x /\ lt == []), (fun _ -> dm_return _ x) |)

let lemma_hist_bind_1 (wp1 : hist 'a) (wp2 : 'a -> hist 'b) (p2:hist_post 'b) (h:trace) :
  Lemma (hist_bind wp1 wp2 p2 h ==> (exists p1. (wp1 p1 h))) = ()

let lemma_hist_bind_2 (wp1 : hist 'a) (wp2 : 'a -> hist 'b) (p2:hist_post 'b) (h:trace) :
  Lemma (hist_bind wp1 wp2 p2 h /\ (forall (p1:hist_post 'a) x (lt:trace). (wp1 p1 h /\ p1 lt x) ==> wp2 x p2 (List.rev lt @ h))) = ()

let pdm_bind (a b:Type)
  (wp1:hist a) (wp2:a -> hist b)
  (f:pdm a wp1) 
  (g:(x:a) -> pdm b (wp2 x))
  (post:hist_post b)
  (pre:squash (exists h. hist_bind wp1 wp2 post h)) :
  Tot (dm b (hist_bind wp1 wp2)) =
  let (| p1, f |) = f in
  Classical.forall_intro (lemma_hist_bind_1 wp1 wp2 post);
  assert ((forall h. hist_bind wp1 wp2 post h ==> (exists p1. wp1 p1 h)) ==> (exists h. wp1 p1 h) );
  let f' = f _ in
  //assert (exists h. wp1 p1 h);
  admit ();
  dm_bind a b wp1 wp2 (f _) (fun (x:a) -> 
    assume (exists lt. p1 x lt);
    Classical.forall_intro (lemma_hist_bind_2 wp1 wp2 post);
    (** the f returned an x, therefore it exists a lt s.t. the following prop should be valid **)
    let (| p2, g |) = g x in
    g _)

unfold
let hist_bind_v2 (wp1 : hist 'a) (wp2 : 'a -> hist 'b) : hist 'b =
  fun p2 h -> (forall (p1:hist_post 'a). wp1 p1 h /\ (forall (lt:trace) r. p1 lt r ==> (wp2 r p2 (List.rev lt @ h))))

let lemma_hist_bind_implies_hist_bind_v2 (wp1 : hist 'a) (wp2 : 'a -> hist 'b) :
  Lemma (hist_bind wp1 wp2 `hist_ord` hist_bind_v2 wp1 wp2) = admit ()

let pdm_bind_v2_0 (a b:Type)
  (wp1:hist a) (wp2:a -> hist b)
  (f:pdm a wp1) 
  (g:(x:a) -> pdm b (wp2 x))
  (pre:squash (hist_as_requires (hist_bind_v2 wp1 wp2))) :
  Tot (dm b (hist_bind_v2 wp1 wp2)) =
  lemma_hist_bind_v2_1 wp1 wp2;
  dm_bind a b wp1 wp2 (f _) (fun (x:a) -> 
    (** the f returned an x, therefore it exists a lt s.t. the following prop should be valid **)
    assume (exists lt. forall p1 h. wp1 p1 h /\ p1 lt x);
    assert (hist_as_requires (wp2 x));
    g x _)

let pdm_bind_v2 (a b:Type)
  (wp1:hist a) (wp2:(x:a) -> hist b)
  (f:pdm a wp1) 
  (g:(x:a) -> pdm b (wp2 x)) :
  pdm b (hist_bind_v2 wp1 wp2) =
  pdm_bind_v2_0 a b wp1 wp2 f g 

let pdm_subcomp (a:Type) (wp1:hist a) (wp2:hist a) (f:pdm a wp1) :
  Pure (pdm a wp2)
    (requires (
      (wp2 `hist_ord` wp1)))
    (ensures fun _ -> True) =
  fun _ -> dm_subcomp a wp1 wp2 (f ())
  
let pdm_bind (a b:Type)
  (wp1:hist a) (wp2:(x:a) -> hist b)
  (f:pdm a wp1) 
  (g:(x:a) -> pdm b (wp2 x)) :
  pdm b (hist_bind wp1 wp2) =
  lemma_hist_bind_implies_hist_bind_v2 wp1 wp2;
  assert ((hist_bind wp1 wp2) `hist_ord` (hist_bind_v2 wp1 wp2)); 
  pdm_subcomp _ (hist_bind_v2 wp1 wp2) (hist_bind wp1 wp2) (pdm_bind_v2 a b wp1 wp2 f g) 

  
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

let lift_pure_pdm0 (a : Type) (w : pure_wp a) (f:(eqtype_as_type unit -> PURE a w)) :
  pdm a (wp_lift_pure_hist w) =
  fun (pre:squash (hist_as_requires (wp_lift_pure_hist w))) ->
    assert (hist_as_requires (wp_lift_pure_hist #a w) ==>
        as_requires w) by (
        norm [delta_only [`%wp_lift_pure_hist; `%hist_as_requires;`%as_requires]];
        let impl = implies_intro () in
        let impl = instantiate impl (`([])) in
        assumption ()
    );
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    let r = f () in
    let r' = dm_return _ r in
    dm_subcomp _ _ _ r'

let lift_pure_pdm (a : Type) (w : pure_wp a) (f:(eqtype_as_type unit -> PURE a w)) :
  pdm a (wp_lift_pure_hist w) =
    lift_pure_pdm0 a w f

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
