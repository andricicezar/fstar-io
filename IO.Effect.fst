module IO.Effect

open FStar.Tactics
open ExtraTactics

open Common
open IO.Free

let io_post a = maybe a -> events_trace -> Type0  // local_events (from old to new)
let io_wpty a = events_trace -> io_post a -> Type0  // past_events (from new to old; reversed compared with local_events)

unfold
let io_return_wp (a:Type) (x:a) : io_wpty a =
  fun past_events p -> p (Inl x) []

unfold
let compute_post (a b:Type) (past_events:events_trace) (kw : a -> io_wpty b) (p:io_post b)
  : io_post a =
      (fun result local_events -> 
        match result with
        | Inl result -> (
            kw result
            ((List.rev local_events) @ past_events) 
            (fun result' local_events' -> 
                p result' (local_events @ local_events')))
        | Inr err -> p (Inr err) local_events)

unfold
let io_bind_wp (a:Type) (b:Type) (w : io_wpty a) (kw : a -> io_wpty b) : io_wpty b =
  fun past_events p -> 
    w past_events (compute_post a b past_events kw p)

unfold let gen_post #a (post:io_post a) (event:io_event) = 
  fun x local_events -> post x (event :: local_events)

unfold let convert_call_to_event (cmd:io_cmds) (args:args cmd) (res:resm cmd) =
  match cmd with
  | Openfile -> EOpenfile args res
  | Read -> ERead args res
  | Close -> EClose args res

// It is weird that this interpretation knows about
// contract failure. Somebody will be able to throw this errors
// manually so, I don't think this is the best place to do them.
// Probably it will be better to refine the output of the `io_all`
// than to modify the interpretation here.
let rec io_interpretation #a
  (m : io a) 
  (p : io_post a) : Type0 = 
  match m with
  | Return x -> p (Inl x) []
  | Throw err -> p (Inr err) []
  | Cont (Call cmd args fnc) -> (
    forall res. (Inr? res ==>  ~(Inr?.v res == GIO_pi_failed \/ Inr?.v res == GIO_default_check_failed)) ==> (
      FStar.WellFounded.axiom1 fnc res;
      let event : io_event = convert_call_to_event cmd args res in
      io_interpretation (fnc res) (gen_post p event)))


// REFINED COMPUTATION MONAD (repr)
let io_irepr (a:Type) (wp:io_wpty a) =
  h:events_trace -> post:io_post a ->
    Pure (io a)
      (requires (wp h post))
      (ensures (fun (t:io a) -> io_interpretation t post))

let io_ireturn (a : Type) (x : a) : io_irepr a (io_return_wp a x) =
  fun _ _ -> io_return a x

let w = io_wpty

unfold
val w_ord (#a : Type) : w a -> w a -> Type0
let w_ord wp1 wp2 = forall h p. wp1 h p ==> wp2 h p

unfold
let apply_changes (old_state local_trace:events_trace) = (List.rev local_trace) @ old_state


let io_ibind (a b : Type) (wp_v : w a) (wp_f: a -> w b) (v : io_irepr a wp_v)
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
let isubcomp (a:Type) (wp1 wp2: w a) (f : io_irepr a wp1) :
  Pure (io_irepr a wp2) (requires w_ord wp2 wp1) (ensures fun _ -> True) = f

unfold
let wp_if_then_else (#a:Type) (wp1 wp2:w a) (b:bool) : w a =
  fun h p -> (b ==> wp1 h p) /\ ((~b) ==> wp2 h p)

unfold
let i_if_then_else (a : Type) (wp1 wp2 : w a) (f : io_irepr a wp1) (g : io_irepr a wp2) (b : bool) : Type =
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
  Pure (io_irepr a (fun s0 p -> wp (fun r -> p (Inl r) []))) (requires True)
                    (ensures (fun _ -> True))
  = fun s0 p -> let r = elim_pure f (fun r -> p (Inl r) []) in io_return _ r

sub_effect PURE ~> IOwp = lift_pure_iowp
  
effect IO
  (a:Type)
  (pre : events_trace -> Type0)
  (post : events_trace -> maybe a -> events_trace -> Type0) =
  IOwp a (fun (h:events_trace) (p:io_post a) ->
    pre h /\ (forall res le. post h res le ==>  p res le))

let rec is_open (fd:file_descr) (past_events: events_trace) :
  Tot bool =
  match past_events with
  | [] -> false
  | h :: tail -> match h with
               | EOpenfile _ (Inl fd') ->
                   if fd = fd' then true
                   else is_open fd tail
               | EClose fd' _ -> 
                    if fd = fd' then false
                    else is_open fd tail
               | _ -> is_open fd tail

val default_check : monitorable_prop
let default_check (state:events_trace) (action:action_type) =
  match action with
  | (| Openfile, fnm |) -> true
  | (| Read, fd |) -> is_open fd state
  | (| Close, fd |) -> is_open fd state

let static_cmd
  (cmd : io_cmds)
  (argz : io_args cmd) :
  IO (res cmd)
    (requires (fun h -> default_check h (| cmd, argz |)))
    (ensures (fun h r local_trace ->
      (match r with
      | Inr GIO_pi_failed -> False
      | Inr GIO_default_check_failed -> False
      | _ -> True) /\
      local_trace == [convert_call_to_event cmd argz r]
      /\ enforced_locally default_check h local_trace
  )) by (compute ()) =
  IOwp?.reflect(fun _ _ -> io_all cmd argz)
