module IO.Effect

open FStar.Tactics
open ExtraTactics

open Common
open IO.Free

(** The postcondition for an io computation is defined over the
result (type: a + exn) and local trace (type: trace).
The local trace represents the events that happend during the
computation. Local trace is in chronological order.

We also have the history (type: trace) which represents the
events that happend until the beggining of the io computation.
The history is reverse chronology order.

At the end of an io computation, the trace will be
(reverse of local trace) appended to the history. **)

let io_post a = maybe a -> lt:trace -> Type0  // local_trace (from old to new)
let io_wpty a = h:trace -> io_post a -> Type0  // past_events (from new to old; reversed compared with local_trace)

unfold
let io_return_wp (a:Type) (x:a) : io_wpty a =
  fun _ p -> p (Inl x) []

unfold
let compute_post (a b:Type) (h:trace) (kw : a -> io_wpty b) (p:io_post b)
  : io_post a =
      (fun result local_trace ->
        match result with
        | Inl result -> (
            kw result
            ((List.rev local_trace) @ h)
            (fun result' local_trace' ->
                p result' (local_trace @ local_trace')))
        | Inr err -> p (Inr err) local_trace)

unfold
let io_bind_wp (a:Type) (b:Type) (w : io_wpty a) (kw : a -> io_wpty b) : io_wpty b =
  fun h p ->
    w h (compute_post a b h kw p)

let gen_post #a (post:io_post a) (e:event) =
  fun x local_trace -> post x (e :: local_trace)

let rec io_interpretation #a
  (m : io a)
  (p : io_post a) : Type0 =
  match m with
  | Return x -> p (Inl x) []
  | Throw err -> p (Inr err) []
  | Call cmd args fnc -> (
    forall res. (
      let e : event = convert_call_to_event cmd args res in
      io_interpretation (fnc res) (gen_post p e)))


// REFINED COMPUTATION MONAD (repr)
let io_irepr (a:Type) (wp:io_wpty a) =
  // TODO: more intuition about this? why does this look like a
  // reader monad?
  h:trace -> post:io_post a ->
    Pure (io a)
      (requires (wp h post))
      (ensures (fun (m:io a) -> io_interpretation m post))

let io_ireturn (a : Type) (x : a) : io_irepr a (io_return_wp a x) =
  fun _ _ -> io_return a x

unfold
val io_wpty_ord (#a : Type) : io_wpty a -> io_wpty a -> Type0
let io_wpty_ord wp1 wp2 = forall h p. wp1 h p ==> wp2 h p

let io_ibind (a b : Type) (wp_v : io_wpty a) (wp_f: a -> io_wpty b) (v : io_irepr a wp_v)
  (f : (x:a -> io_irepr b (wp_f x))) : io_irepr b (io_bind_wp _ _ wp_v wp_f) =
  fun h p ->
    let t = (io_bind a b
        (v h (compute_post a b h wp_f p))
        (fun x ->
          assume (wp_f x h p);
           f x h p)) in
    assume (io_interpretation t p);
    t

unfold
let isubcomp (a:Type) (wp1 wp2: io_wpty a) (f : io_irepr a wp1) :
  Pure (io_irepr a wp2) (requires io_wpty_ord wp2 wp1) (ensures fun _ -> True) = f

unfold
let wp_if_then_else (#a:Type) (wp1 wp2:io_wpty a) (b:bool) : io_wpty a =
  fun h p -> (b ==> wp1 h p) /\ ((~b) ==> wp2 h p)

unfold
let i_if_then_else (a : Type) (wp1 wp2: io_wpty a) (f : io_irepr a wp1) (g : io_irepr a wp2) (b : bool) : Type =
  io_irepr a (wp_if_then_else wp1 wp2 b)

total
reifiable
reflectable
layered_effect {
  IOwp : a:Type -> wp : io_wpty a -> Effect
  with
       repr       = io_irepr
     ; return     = io_ireturn
     ; bind       = io_ibind

     ; subcomp      = isubcomp
     ; if_then_else = i_if_then_else
}

let lift_pure_iowp (a:Type) (wp:pure_wp a) (f:(eqtype_as_type unit -> PURE a wp)) :
  Tot (io_irepr a (fun h p -> wp (fun r -> p (Inl r) [])))
  = fun h p -> let r = elim_pure f (fun r -> p (Inl r) []) in io_return _ r

sub_effect PURE ~> IOwp = lift_pure_iowp

let throw (#a:Type) (err:exn) : IOwp a (fun _ p -> p (Inr err) []) =
  IOwp?.reflect(fun _ _ -> io_throw a err)

let static_cmd
  (pi : monitorable_prop)
  (cmd : io_cmds)
  (argz : io_args cmd) :
  IOwp
    (res cmd)
    (fun h p ->
      (** precondition **)
      pi h (| cmd, argz |) /\
      (forall (r:io_resm cmd) lt. (
      (** postcondition **)
        ~(Inr? r /\ Inr?.v r == Contract_failure) /\
        lt == [convert_call_to_event cmd argz r] /\
        enforced_locally pi h lt) ==>  p r lt)) =
  IOwp?.reflect(fun _ _ -> io_call cmd argz)
 
effect IO
  (a:Type)
  (pi : monitorable_prop)
  (pre : trace -> Type0)
  (post : trace -> maybe a -> trace -> Type0) =
  IOwp a (fun (h:trace) (p:io_post a) ->
    enforced_globally pi h /\
    pre h /\
    (forall res lt. (
      enforced_globally pi (apply_changes h lt) /\
      post h res lt ==>  p res lt)))

// let fd = static_cmd pi Openfile "../Makefile"
