module DM.IO

open FStar.Tactics
open ExtraTactics

open Common
open Free.IO
open Exnhist

(** The postcondition for an io computation is defined over the
result (type: a + exn) and local trace (type: trace).
The local trace represents the events that happend during the
computation. Local trace is in chronological order.

We also have the history (type: trace) which represents the
events that happend until the beggining of the io computation.
The history is reverse chronology order.

At the end of an io computation, the trace will be
(reverse of local trace) appended to the history. **)

let rec io_interpretation #a
  (m : io a)
  (p : exnhist_post a) : Type0 =
  match m with
  | Return x -> p (Inl x) []
  | Call Throw exn _ -> p (Inr exn) []
  | Call cmd args fnc -> (
    forall res. (
      io_interpretation (fnc res) (gen_post p cmd args res)))


// REFINED COMPUTATION MONAD (repr)
let io_irepr (a:Type) (wp:exnhist a) =
  // TODO: more intuition about this? why does this look like a
  // reader monad?
  h:trace -> post:exnhist_post a ->
    Pure (io a)
      (requires (wp h post))
      (ensures (fun (m:io a) -> io_interpretation m post))

let io_ireturn (a : Type) (x : a) : io_irepr a (exnhist_return a x) =
  fun _ _ -> io_return a x

let io_ibind
  (a b : Type)
  (wp_v : exnhist a)
  (wp_f: a -> exnhist b)
  (v : io_irepr a wp_v)
  (f : (x:a -> io_irepr b (wp_f x))) :
  Tot (io_irepr b (exnhist_bind _ _ wp_v wp_f)) =
  fun h p ->
    let t = (io_bind a b
        (v h (compute_post a b h wp_f p))
        (fun x ->
          assume (wp_f x h p);
           f x h p)) in
    assume (io_interpretation t p);
    t

unfold
let isubcomp (a:Type) (wp1 wp2: exnhist a) (f : io_irepr a wp1) :
  Pure (io_irepr a wp2)
    (requires exnhist_ord wp2 wp1)
    (ensures fun _ -> True) =
  f

unfold
let i_if_then_else
  (a : Type)
  (wp1 wp2: exnhist a)
  (f : io_irepr a wp1)
  (g : io_irepr a wp2) (b : bool) :
  Tot Type =
  io_irepr a (exnhist_if_then_else wp1 wp2 b)

total
reifiable
reflectable
layered_effect {
  IOwp : a:Type -> wp : exnhist a -> Effect
  with
       repr       = io_irepr
     ; return     = io_ireturn
     ; bind       = io_ibind

     ; subcomp      = isubcomp
     ; if_then_else = i_if_then_else
}

let lift_pure_iowp
  (a:Type)
  (wp:pure_wp a)
  (f:(eqtype_as_type unit -> PURE a wp)) :
  Tot (io_irepr a (fun h p -> wp (fun r -> p (Inl r) [])))
  = fun h p -> let r = elim_pure f (fun r -> p (Inl r) []) in io_return _ r

sub_effect PURE ~> IOwp = lift_pure_iowp

effect IO
  (a:Type)
  (pi : monitorable_prop)
  (pre : trace -> Type0)
  (post : trace -> maybe a -> trace -> Type0) =
  IOwp a (fun (h:trace) (p:exnhist_post a) ->
    enforced_globally pi h /\
    pre h /\
    (forall res lt. (
      enforced_globally pi (apply_changes h lt) /\
      post h res lt ==>  p res lt)))

let throw (#a:Type) (e:exn) : IOwp a (fun h p -> p (Inr e) []) =
  IOwp?.reflect(fun _ _ -> Call Throw e Return)

let f () : IOwp unit (fun h p -> False ==> p (Inr Contract_failure) []) =
  if false then ()
  else throw Contract_failure

let lemma (cmd:io_cmds) :
  Lemma (maybe (_io_res cmd) == io_sig.res cmd) = ()

let static_cmd
  (cmd : io_cmds)
  (pi : monitorable_prop)
  (argz : base_args cmd) :
  IOwp
    (_io_res cmd)
    (fun h p ->
      (** precondition **)
      pi h (| cmd, argz |) /\

      (forall r lt. (
      (** postcondition **)
        lt == [convert_call_to_event cmd argz r] /\
        enforced_locally pi h lt)
       ==>  p r lt)) =
  IOwp?.reflect (fun _ _ ->
    Call cmd argz (fun (r:(maybe (_io_res cmd))) ->
      match r with
      | Inl r' -> Return r'
      | Inr err -> (Call Throw err Return) <: io (_io_res cmd)))
