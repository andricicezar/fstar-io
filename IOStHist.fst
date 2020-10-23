module IOStHist

open FStar.Tactics

open Common
open FStar.Exn
include IO.Free
include IOHist

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
  iohist_interpretation (m s0) (fun r le -> p r le)

// REFINED COMPUTATION MONAD (repr)
let irepr (a:Type) (wp:iosthist_wpty a) =
  post:iosthist_post a -> h:events_trace ->
    Pure (io (events_trace * a))
      (requires (wp h post))
      (ensures (fun (t:io (events_trace * a)) -> iohist_interpretation t post))

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
    assume (iohist_interpretation t p);
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

let ioo_bind #a #b = io_bind a b

let unsafe_cmd
  (cmd : io_cmds)
  (argz : args cmd) :
  IOStHist (res cmd) 
    (requires (fun _ -> True))
    (ensures (fun s0 result local_trace ->
      match result with
      | Inl v -> let (s1, r) = v in (
          local_trace == [convert_call_to_event cmd argz (Inl r)] /\
          s1 == (apply_changes s0 local_trace))
      | Inr err ->
          local_trace == [convert_call_to_event cmd argz (Inr err)]))
  by (
    let cmd' = match List.Tot.nth (cur_binders ()) 0 with
    | Some x -> x | None -> fail "verification condition changed" in
    destruct (binder_to_term cmd');
    iterAll(fun () ->
      ignore(intro ());
      rewrite_eqs_from_context ();
      compute ()
    )) =
  IOStHistwp?.reflect(fun p (s0:events_trace) ->
      ((io_all cmd argz) `ioo_bind` 
      (fun r -> io_return _ (s0, r))) `ioo_bind`
      (fun (s0, rez) -> io_return _ ((convert_call_to_event cmd argz (Inl rez)) :: s0, rez))
  )

let static_cmd
  (cmd : io_cmds)
  (argz : args cmd) :
  IOStHist (res cmd)
    (requires (fun s0 -> default_check s0 (| cmd, argz |)))
    (ensures (fun s0 result local_trace ->
      (match result with
      | Inl v -> let (s1, r) = v in (
         local_trace == [convert_call_to_event cmd argz (Inl r)] /\
         s1 == (apply_changes s0 local_trace))
      | Inr err ->
         local_trace == [convert_call_to_event cmd argz (Inr err)])
      /\  enforced_locally default_check s0 local_trace)) =
  unsafe_cmd cmd argz

let pi_static_cmd
  (cmd : io_cmds)
  (pi_check : check_type)
  (argz : args cmd) :
  IOStHist (res cmd)
    (requires (fun s0 ->
      default_check s0 (| cmd, argz |) &&
      pi_check s0 (| cmd, argz |)))
    (ensures (fun s0 result local_trace ->
      (match result with
      | Inl v -> let (s1, r) = v in (
         local_trace == [convert_call_to_event cmd argz (Inl r)] /\
         s1 == (apply_changes s0 local_trace))
      | Inr err ->
         local_trace == [convert_call_to_event cmd argz (Inr err)])
      /\ enforced_locally default_check s0 local_trace
      /\ enforced_locally pi_check s0 local_trace)) =
  static_cmd cmd argz

exception GIO_default_check_failed
exception GIO_pi_check_failed

let mixed_cmd
  (cmd : io_cmds)
  (pi_check : check_type)
  (argz : args cmd) :
  IOStHist (res cmd)
    (requires (fun s0 -> default_check s0 (| cmd, argz |)))
    (ensures (fun s0 result local_trace ->
      (match result with
      | Inl v -> let (s1, r) = v in (
         local_trace == [convert_call_to_event cmd argz (Inl r)] /\
         s1 == (apply_changes s0 local_trace))
      | Inr err ->
         local_trace == [convert_call_to_event cmd argz (Inr err)] \/
         local_trace == [])
      /\ enforced_locally default_check s0 local_trace
      /\ enforced_locally pi_check s0 local_trace)) =
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
    (ensures (fun s0 result local_trace ->
      (match result with
      | Inl v -> let (s1, r) = v in (
         local_trace == [convert_call_to_event cmd argz (Inl r)] /\
         s1 == (apply_changes s0 local_trace))
      | Inr err ->
         local_trace == [convert_call_to_event cmd argz (Inr err)] \/
         local_trace == [])
      /\ enforced_locally default_check s0 local_trace
      /\ enforced_locally pi_check s0 local_trace)) = 
  let s0 = get () in
  let action = (| cmd, argz |) in
  match default_check s0 action with
  | true -> mixed_cmd cmd pi_check argz
  | false -> throw GIO_default_check_failed

let gio_pre (pi_check : check_type) (s0:events_trace) : Type0 =
  enforced_globally default_check s0 &&
  enforced_globally pi_check s0

let gio_post 
  #a 
  (pi_check : check_type)
  (s0:events_trace)
  (result:maybe (events_trace * a))
  (local_trace:events_trace) :
  Tot Type0 =
  enforced_globally (default_check) (apply_changes s0 local_trace) /\
  enforced_globally (pi_check) (apply_changes s0 local_trace) /\
  (match result with
  | Inl v -> let (s1, r) = v in s1 == (apply_changes s0 local_trace)
  | Inr _ -> True)

effect GIO
  (a:Type)
  (pi_check : check_type) =
  IOStHist a
    (requires (gio_pre pi_check))
    (ensures (gio_post pi_check))

effect M4wp
  (a:Type)
  (pi_check : check_type) 
  (post : events_trace -> maybe (events_trace * a) -> events_trace -> Type0) =
  IOStHist a
    (requires (gio_pre pi_check))
    (ensures (fun h r le -> gio_post pi_check h r le /\ post h r le))

let iost_to_io #t2 (tree : io (events_trace * t2)) : io t2 =
  io_bind (events_trace * t2) t2
    tree
    (fun r -> io_return _ (cdr r))
