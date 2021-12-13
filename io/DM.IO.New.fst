module DM.IO.New

open FStar.List.Tot.Base
open FStar.Tactics
open ExtraTactics

open Common
open Free
open Free.IO
open Free.IO.Call
open Hist

(** TODO:
- [ ] define as io_sig, io_spec that is a struct { pre: ...; post: ...; }
- [ ] define hist as Theo: hist a = hist_post a -> hist_pre a
- [ ] prove bind
- [ ] extract the 3 relevant files: the free monad, the hist monad, a sig file, and this one with the DM effect.
- [ ] write a test file
**)

(** The postcondition for an io computation is defined over the
result (type: a) and local trace (type: trace).
The local trace represents the events that happend during the
computation. Local trace is in chronological order.

We also have the history (type: trace) which represents the
events that happend until the beginning of the io computation.
The history is in reverse chronology order.

At the end of an io computation, the trace will be
(reverse of local trace) appended to the history. **)

let rec is_open (fd:file_descr) (h: trace) :
  Tot bool =
  match h with
  | [] -> false
  | h :: tail -> match h with
               | EOpenfile _ (Inl fd') ->
                   if fd = fd' then true
                   else is_open fd tail
               | EClose fd' _ ->
                    if fd = fd' then false
                    else is_open fd tail
               | _ -> is_open fd tail


unfold
let op_pre (cmd:io_cmds) (arg:io_args cmd) (h:trace) : Type0 =
  match cmd with
  | Openfile -> True
  | Read -> is_open arg h
  | Close -> is_open arg h

(** Inspierd from Kenji's thesis (2.4.5) **)
let rec io_theta #a
  (m : io a) : hist a =
  match m with
  | Return x -> hist_return a x
  | Call cmd arg fnc ->
    hist_bind
      (res cmd)
      a
      (fun h p -> op_pre cmd arg h /\ (forall r. p r [convert_call_to_event cmd arg r]))
      (fun r -> io_theta (fnc r))

unfold
let stronger_wp #a (w1 w2 : hist a) : Type0 =
  forall (post : hist_post a) (hist : trace). w1 hist post ==> w2 hist post

// The Dijkstra Monad
let dm (a:Type) (wp:hist a) =
  (m:(io a){wp `stronger_wp` io_theta m})

let dm_return (a : Type) (x : a) : dm a (hist_return a x) =
  io_return a x

let lemma_dm_bind a b w wf (m : dm a w) (f : (x:a) -> dm b (wf x)) (post : hist_post b) (hist : trace) :
  Lemma
    (requires hist_bind _ _ w wf hist post)
    (ensures io_theta (io_bind _ _ m f) hist post) = admit ()

let dm_bind
  (a b : Type)
  (wp_v : hist a)
  (wp_f: a -> hist b)
  (v : dm a wp_v)
  (f : (x:a -> dm b (wp_f x))) :
  Tot (dm b (hist_bind _ _ wp_v wp_f)) =
  Classical.forall_intro_2 (Classical.move_requires_2 (lemma_dm_bind a b wp_v wp_f v f));
  io_bind _ _ v f

let dm_subcomp (a:Type) (wp1 wp2: hist a) (f : dm a wp1) :
  Pure (dm a wp2)
    (requires hist_ord wp2 wp1)
    (ensures fun _ -> True) =
  f

let dm_if_then_else
  (a : Type)
  (wp1 wp2: hist a)
  (f : dm a wp1)
  (g : dm a wp2) (b : bool) :
  Tot Type =
  dm a (hist_if_then_else wp1 wp2 b)

total
reifiable
reflectable
layered_effect {
  IOwp : a:Type -> wp : hist a -> Effect
  with
       repr       = dm 
     ; return     = dm_return
     ; bind       = dm_bind

     ; subcomp      = dm_subcomp
     ; if_then_else = dm_if_then_else
}

let elim_pure #a #w (f : unit -> PURE a w) :
  Pure
    a
    (requires w (fun _ -> True))
    (ensures fun r -> forall post. w post ==> post r)
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall () ;
  f ()

unfold
let hist_lift #a (w : pure_wp a) : hist a =
  fun hist post -> w (fun x -> post x [])

(** inspired from Alg **)
let lift_pure_dm (a : Type) (w : pure_wp a) (f:(eqtype_as_type unit -> PURE a w)) :
  Pure (dm a (hist_lift w)) (requires w (fun _ -> True)) (ensures fun _ -> True) =
  let r = elim_pure #a #w f in
  let r' : dm a (hist_return _ r) = dm_return a r in
  dm_subcomp _ (hist_return _ r) (hist_lift w) r'

sub_effect PURE ~> IOwp = lift_pure_dm

effect IO
  (a:Type)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  IOwp a (fun (h:trace) (p:hist_post a) ->
    pre h /\ (forall res lt. post h res lt ==>  p res lt))

let static_cmd
  (cmd : io_cmds)
  (argz : io_args cmd) :
  IO (io_resm cmd)
    (requires (fun h -> op_pre cmd argz h))
    (ensures (fun h r lt ->
        lt == [convert_call_to_event cmd argz r])) =
  IOwp?.reflect(io_call cmd argz)

let testStatic2 () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  let fd = static_cmd Openfile "../Makefile" in
  if Inl? fd then (** test if Openfile was successful **)
    let msg = static_cmd Read (Inl?.v fd) in
    let _ = static_cmd Close (Inl?.v fd) in
    ()
  else ()

let testStatic3 (fd:file_descr) : IO unit (fun h -> is_open fd h) (fun h r lt -> ~(is_open fd (apply_changes h lt))) =
  let _ = static_cmd Close fd in
  ()
