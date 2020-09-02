module IOStHist

open FStar.Tactics

open Common
open FStar.Exn
open FStar.ST
include IO.Free
include IOHist
include ExtraTactics

// Extraction hack
val hh : ref events_trace
let hh = ST.alloc []

let get_history () = !hh
let update_history (event) =
  hh := event :: !hh
  
// UTILS
let rec is_open (fd:file_descr) (past_events: events_trace) :
  Tot bool =
  match past_events with
  | [] -> false
  | h :: tail -> match h with
               | EOpenfile _ (Inl fd') -> if fd = fd' then true
                                   else is_open fd tail
               | EClose fd' _ -> if fd = fd' then false
                                  else is_open fd tail
               | _ -> is_open fd tail

type action_type = (cmd : io_cmds) & (args cmd)

// UNREFINED COMPUTATION MONAD

type iost a = events_trace -> io (events_trace * a)

unfold
let iost_return (a:Type) (x:a) : iost a = fun s -> io_return (events_trace * a) (s, x)
  
unfold
let iost_throw (a:Type) (x:exn) : iost a = fun s -> io_throw (events_trace * a) x
  
unfold
let iost_bind (a:Type) (b:Type) (l : iost a) (k : a -> iost b) : iost b =
  fun s -> io_bind (events_trace * a)
                (events_trace * b)
                (l s)
                (fun (s', x) -> k x s')

// SPEC MONAD

let iosthist_post a = maybe (s1:events_trace * a) -> (le:events_trace) -> Type0  // local_events (from old to new)
let iosthist_wpty a = (s0:events_trace) -> iosthist_post a -> Type0

unfold let iosthist_return_wp (a:Type) (x:a) : iosthist_wpty a =
  fun s0 p -> p (Inl (s0, x)) []

unfold
let compute_post (a b:Type) (kw : a -> iosthist_wpty b) (p:iosthist_post b)
  : iosthist_post a =
      (fun result local_events ->
        match result with
        | Inl v -> let (s1, r) = v in
            kw r s1
            (fun r' local_events' ->
                p r' (local_events @ local_events'))
        | Inr err -> p (Inr err) local_events)

unfold
let iosthist_bind_wp (a b:Type) (w : iosthist_wpty a) (kw : a -> iosthist_wpty b) : iosthist_wpty b =
  fun s0 p -> w s0 (compute_post a b kw p)

// THETA

let iosthist_interpretation #a (m : iost a) (s0 : events_trace) (p : iosthist_post a) : Type0 =
  iohist_interpretation (m s0) s0 (fun r le -> p r le)

// REFINED COMPUTATION MONAD (repr)
let irepr (a:Type) (wp:iosthist_wpty a) =
  post:iosthist_post a -> h:events_trace ->
    Pure (io (events_trace * a))
      (requires (wp h post))
      (ensures (fun (t:io (events_trace * a)) -> iohist_interpretation t h post))

// let irepr (a:Type) (wp:iosthist_wpty a) =
//   h:events_trace ->
//     PURE (io (events_trace * a))
//       (fun (purepost:io (events_trace * a) -> Type0) ->
//         forall (post:iosthist_post a).
//         wp h post /\
//         (forall (t:io (events_trace * a)). (iohist_interpretation t h post) ==> purepost t))

let ireturn (a : Type) (x : a) : irepr a (iosthist_return_wp a x) =
  fun _ s0 -> io_return (events_trace * a) (s0, x)

let w = iosthist_wpty

unfold
val w_ord (#a : Type) : w a -> w a -> Type0
let w_ord wp1 wp2 = forall h p. wp1 h p ==> wp2 h p

let ibind (a b : Type) (wp_v : w a) (wp_f: a -> w b) (v : irepr a wp_v)
  (f : (x:a -> irepr b (wp_f x))) : irepr b (iosthist_bind_wp _ _ wp_v wp_f) =
  fun p s0 -> 
    let t = (io_bind (events_trace * a) (events_trace * b)
        (v (compute_post a b wp_f p) s0)
        (fun (s1, x) ->
          assume (wp_f x s1 p);
           f x p s1)) in
    assume (iohist_interpretation t s0 p);
    t

unfold
let isubcomp (a:Type) (wp1 wp2: w a) (f : irepr a wp1) :
  Pure (irepr a wp2) (requires w_ord wp2 wp1) (ensures fun _ -> True) = f

unfold
let wp_if_then_else (#a:Type) (wp1 wp2:w a) (b:bool) : w a =
  fun h p -> (b ==> wp1 h p) /\ ((~b) ==> wp2 h p)

unfold
let i_if_then_else (a : Type) (wp1 wp2 : w a) (f : irepr a wp1) (g : irepr a wp2) (b : bool) : Type =
  irepr a (wp_if_then_else wp1 wp2 b)

/// IOST is the IO monad but a state passing history (materialize past_events).
total
reifiable
reflectable
layered_effect {
  IOStHistwp : a:Type -> wp : iosthist_wpty a -> Effect
  with
       repr       = irepr
     ; return     = ireturn
     ; bind       = ibind

     ; subcomp      = isubcomp
     ; if_then_else = i_if_then_else
}


let lift_pure_iosthistwp (a:Type) (wp:pure_wp a) (f:(eqtype_as_type unit -> PURE a wp)) :
  Pure (irepr a (fun s0 p -> wp (fun r -> p (Inl (s0, r)) []))) (requires True)
                    (ensures (fun _ -> True))
  = fun p s0 -> let r = elim_pure f (fun r -> p (Inl (s0, r)) []) in io_return _ (s0, r)

sub_effect PURE ~> IOStHistwp = lift_pure_iosthistwp

// given a initial state, returns that state modified and a result
// let iost_update (event:io_event) : iost unit =
//   (fun s0 -> io_return _ (event :: s0, ()))
// let iost_get () : iost events_trace =
//   (fun s0 -> io_return _ (s0, s0))

effect IOStHist
  (a:Type)
  (pre : events_trace -> Type0)
  (post : events_trace -> maybe (events_trace * a) -> events_trace -> Type0) =
  IOStHistwp a (fun (s0:events_trace) (p:iosthist_post a) ->
    pre s0 /\ (forall res le. post s0 res le ==>  p res le))


exception Contract_failure

let get () : IOStHistwp events_trace (fun s0 p -> p (Inl (s0, s0)) []) =
  IOStHistwp?.reflect(fun _ s0 -> io_return (events_trace * events_trace) (s0, s0))
  
let throw (err:exn) : IOStHistwp events_trace (fun s0 p -> p (Inr err) []) =
  IOStHistwp?.reflect(fun _ s0 -> io_throw _ err)

// type iost a = events_trace -> io (events_trace * a)
  
// DEFINE THE PRIMITIVES
type check_type = (state:events_trace) -> (action:action_type) -> Tot bool

val default_check : check_type
let default_check (state:events_trace) (action:action_type) =
  match action with
  | (| Openfile, fnm |) -> true
  | (| Read, fd |) -> is_open fd state
  | (| Close, fd |) -> is_open fd state

unfold
let apply_changes (old_state local_trace:events_trace) = (List.rev local_trace) @ old_state

unfold let convert_event_to_action (event:io_event) : action_type =
  match event with
  | EOpenfile args _ -> (| Openfile, args |)
  | ERead args _ -> (| Read, args |)
  | EClose args _ -> (| Close, args |)


let rec enforced_globally (check : (events_trace -> action_type -> bool)) (h : events_trace) : bool =
  match h with
  | [] -> true
  | h  ::  t ->
       let action = convert_event_to_action h in
       if check t action then
         enforced_globally (check) t
       else false

let rec enforced_locally (check : (events_trace -> action_type -> bool)) (acc : events_trace) (l : events_trace) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | h  ::  t ->
       let action = convert_event_to_action h in
       if check acc action then
         enforced_locally (check) (h::acc) t
       else false

let some_wp (cmd : io_cmds) (argz: args cmd) = (fun s0 p -> 
  // precondition
  (default_check s0 (| cmd, argz |)) /\
  (forall (result:maybe (events_trace * (res cmd))) local_trace.
      (match result with
      | Inl v -> let (s1, r) = v in (
          local_trace == [convert_call_to_event cmd argz (Inl r)] /\
          s1 == (apply_changes s0 local_trace)) /\
          enforced_locally default_check s0 local_trace
      | Inr _ -> True) ==>  p result local_trace))

let ioo_bind #a #b = io_bind a b

let static_cmd
  (cmd : io_cmds)
  (argz : args cmd) :
  IOStHistwp (res cmd) (some_wp cmd argz)
  by (
    let cmd' = match List.Tot.nth (cur_binders ()) 0 with
    | Some x -> x | None -> fail "verification condition changed" in
    destruct (binder_to_term cmd');
    iterAll(fun () ->
      ignore(intro ());
      rewrite_eqs_from_context ();
      compute ()
    )
  ) =
  IOStHistwp?.reflect(fun p (s0:events_trace) -> 
      ((io_all cmd argz) `ioo_bind` 
      (fun r -> io_return _ (s0, r))) `ioo_bind`
      (fun (s0, rez) -> io_return _ ((convert_call_to_event cmd argz (Inl rez)) :: s0, rez))
  )

let pi_static_cmd
  (cmd : io_cmds)
  (pi_check : check_type)
  (argz : args cmd) :
  IOStHist (res cmd)
    (requires (fun s0 ->
      default_check s0 (| cmd, argz |) &&
      pi_check s0 (| cmd, argz |)))
    (ensures (fun s0 (result:maybe (events_trace * (res cmd))) local_trace ->
      (match result with
      | Inl v -> let (s1, r) = v in (
          local_trace == [convert_call_to_event cmd argz (Inl r)] /\
          s1 == (apply_changes s0 local_trace) /\
          enforced_locally default_check s0 local_trace /\
          enforced_locally pi_check s0 local_trace)
      | Inr _ -> True))) =
  static_cmd cmd argz

exception GIO_default_check_failed
exception GIO_pi_check_failed

let mixed_cmd
  (cmd : io_cmds)
  (pi_check : check_type)
  (argz : args cmd) :
  IOStHist (res cmd)
    (requires (fun s0 -> default_check s0 (| cmd, argz |)))
    (ensures (fun s0 (result:maybe (events_trace * (res cmd))) local_trace ->
      (match result with
      | Inl v -> let (s1, r) = v in (
          local_trace == [convert_call_to_event cmd argz (Inl r)] /\
          s1 == (apply_changes s0 local_trace) /\
          enforced_locally default_check s0 local_trace /\
          enforced_locally pi_check s0 local_trace)
      | Inr _ -> True))) =
  let s0 = get () in
  let action = (| cmd, argz |) in
  match pi_check s0 action with
  | true -> pi_static_cmd cmd pi_check argz
  | false -> throw GIO_pi_check_failed

let dynamic_cmd
  (cmd : io_cmds)
  (pi_check : check_type)
  (argz : args cmd) :
  IOStHist (res cmd)
    (requires (fun s0 -> True))
    (ensures (fun s0 (result:maybe (events_trace * (res cmd))) local_trace ->
      (match result with
      | Inl v -> let (s1, r) = v in (
          local_trace == [convert_call_to_event cmd argz (Inl r)] /\
          s1 == (apply_changes s0 local_trace) /\
          enforced_locally default_check s0 local_trace /\
          enforced_locally pi_check s0 local_trace)
      | Inr _ -> True))) =
  let s0 = get () in
  let action = (| cmd, argz |) in
  match default_check s0 action with
  | true -> mixed_cmd cmd pi_check argz
  | false -> throw GIO_default_check_failed

effect GIO
  (a:Type)
  (pi_check : check_type) =
  IOStHist a
    (requires (fun s0 ->
      enforced_globally default_check s0 &&
      enforced_globally pi_check s0))
    (ensures (fun s0 (result) local_trace ->
      (match result with
      | Inl v -> let (s1, r) = v in (
          s1 == (apply_changes s0 local_trace) /\
          enforced_globally (default_check) s1 /\
          enforced_globally (pi_check) s1)
      | Inr _ -> True)))

val to_runtime_check : (#t1:Type) -> (#t2:Type) -> pre:(t1->events_trace->Type0) -> post:(t1->events_trace->maybe (events_trace * t2)->events_trace->Type0) ->
  ((x:t1) -> IOStHist t2 (pre x) (post x)) -> 
  Tot ((x:t1) -> IOStHist t2 (fun _ -> True) (fun s0 result le ->
    post x s0 result le /\
    // this is trying to enforce the pre condition, but this is not enough
    // I suppose a match on result is needed and checked if it was a contract_failure or not
    (match result with
    | Inr Contract_failure -> le == []
    | _ -> pre x s0)))



val enforce : (#t1:Type) -> (#t2:Type) -> pre:(t1->events_trace->Type0) -> post:(t1->events_trace->maybe (events_trace * t2)->events_trace->Type0) ->
  (pi_check:check_type) -> ((x:t1) -> IOStHist t2 (pre x) (post x)) -> 
  Tot ((x:t1) -> IOStHist t2 (pre x) (fun s0 result le ->
    post x s0 result le /\
    (match result with
    | Inl v -> let (s1, r) = v in (
        s1 == (apply_changes s0 le) /\
        // this one does not make sense
        enforced_globally (pi_check) s1)
    | Inr _ -> True)))
    

type set_of_traces = events_trace -> Type0

val include_in : set_of_traces -> set_of_traces -> Type0
let include_in s1 s2 = forall t. s1 t ==>  s2 t

let rec behavior #a
  (m : io a) : set_of_traces =
  match m with
  | Return x -> fun t -> t == []
  | Throw err -> fun t -> t == []
  | Cont t -> begin
    match t with
    | Call cmd args fnc -> (fun t' -> 
      (exists res t. (
         FStar.WellFounded.axiom1 fnc res;
         (behavior (fnc res) t) /\
         t' == ((convert_call_to_event cmd args res)::t))))
  end

let include_in_trans #a #b #c () : Lemma (
  forall (t1:io a) (t2:io b) (t3:io c). behavior t1 `include_in` behavior t2 /\ behavior t2 `include_in` behavior t3 ==>
    behavior t1 `include_in` behavior t3) = ()

let rec iost_to_io #t2 (tree : io (events_trace * t2)) : 
  Pure (io t2)
    (requires True)
    (ensures (fun (res:io t2) -> True)) =
      // behavior res `include_in` behavior tree)) =
  match tree with
  | Return (s1, r) -> Return r
  | Throw r -> Throw r
  | Cont (Call cmd argz fnc) ->
  //   io_bind (events_trace * t2) t2
  //     (Cont (Call cmd argz fnc))
  //     (fun (_, r) -> io_return _ r)

     Cont (Call cmd argz (fun res -> 
       WellFounded.axiom1 fnc res;
       iost_to_io (fnc res)))
