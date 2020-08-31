module IOStHist

open FStar.Tactics
open ExtraTactics
open FStar.Exn
open FStar.ST

open Common
open IO.Free
open IOHist

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

unfold let convert_event_to_action (event:io_event) : action_type = 
  match event with
  | EOpenfile args _ -> (| Openfile, args |)
  | ERead args _ -> (| Read, args |)
  | EClose args _ -> (| Close, args |)

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

let iosthist_post a = maybe (s1:events_trace * a) -> (le:events_trace) -> Type0  // local_events (from old to new)
let iosthist_wpty a = (s0:events_trace) -> iosthist_post a -> Type0  

unfold let iosthist_return_wp (a:Type) (x:a) : iosthist_wpty a =
  fun s0 p -> p (Inl (s0, x)) []

unfold
let iosthist_bind_wp (_ : range) (a:Type) (b:Type) (w : iosthist_wpty a) (kw : a -> iosthist_wpty b) : iosthist_wpty b =
  fun s0 p -> 
    w s0 
      (fun result local_events -> 
        match result with
        | Inl v -> let (s1, r) = v in
            kw r s1
            (fun r' local_events' -> 
                p r' (local_events @ local_events'))
        | Inr err -> p (Inr err) local_events)

let iosthist_interpretation #a (m : iost a) (s0 : events_trace) (p : iosthist_post a) : Type0 =
  iohist_interpretation (m s0) s0 (fun r le -> p r le) 

// IOST is the IO monad but a state passing history (materialize past_events).
total
reifiable
reflectable
new_effect {
  IOStHistwp : a:Type -> Effect
  with 
       repr       = iost
     ; return     = iost_return
     ; bind       = iost_bind

     ; wp_type    = iosthist_wpty
     ; return_wp  = iosthist_return_wp
     ; bind_wp    = iosthist_bind_wp

     ; interp     = iosthist_interpretation
}


// given a initial state, returns that state modified and a result
let iost_update (event:io_event) : iost unit =
  (fun s0 -> io_return _ (event :: s0, ()))
let iost_get () : iost events_trace =
  (fun s0 -> io_return _ (s0, s0))

let update (event:io_event) : IOStHistwp unit 
  (fun s0 p -> p (Inl ((event :: s0), ())) []) by (compute ()) =
  IOStHistwp?.reflect (
    fun s0 -> io_return _ (event :: s0, ()))

let get () : IOStHistwp events_trace
  (fun s0 p -> p (Inl (s0, s0)) []) = 
  IOStHistwp?.reflect (
    fun s0 -> io_return _ (s0, s0))

let raise #a (err:exn) : IOStHistwp a
  (fun s0 p -> p (Inr err) []) =
  IOStHistwp?.reflect (
    fun s0 -> io_throw _ err)

effect IOStHist
  (a:Type)
  (pre : events_trace -> Type0)
  (post : events_trace -> maybe (events_trace * a) -> events_trace -> Type0) =
  IOStHistwp a (fun (s0:events_trace) (p:iosthist_post a) ->
    pre s0 /\ (forall res le. post s0 res le ==>  p res le))

exception Contract_failure

let lift_io_iost #a (m:io a) : iost a =
  fun s0 ->
    io_bind a (events_trace * a) m (fun x -> io_return (events_trace * a) (s0, x))

  
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

let rec fold_left (check : (events_trace -> action_type -> bool)) (h : events_trace) : bool =
  match h with
  | [] -> true
  | h  ::  t -> 
       let action = convert_event_to_action h in
       if check t action then 
         fold_left (check) t
       else false

let bind #a #b = iost_bind a b

let static_cmd
  (cmd : io_cmds)
  (argz : args cmd) :
  IOStHist (res cmd)
    (requires (fun s0 -> default_check s0 (| cmd, argz |)))
    (ensures (fun s0 (result:maybe (events_trace * (res cmd))) local_trace ->
      (match result with
      | Inl v -> let (s1, r) = v in (
          local_trace == [convert_call_to_event cmd argz (Inl r)] /\
          s1 == (apply_changes s0 local_trace)
      )
      | Inr _ -> True)))
  by (
    let cm' = match List.Tot.nth (cur_binders ()) 0 with
    | Some x -> x | None -> fail "adsF" in
    destruct (binder_to_term cm');
    iterAll(fun () ->
      ignore(intro ());
      rewrite_eqs_from_context ();
      compute ()
    )
  )=
  let rez = IOStHist?.reflect(lift_io_iost #(res cmd) (io_all cmd argz)) in 
  update (convert_call_to_event cmd argz (Inl rez));
  rez

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
          s1 == (apply_changes s0 local_trace))
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
          s1 == (apply_changes s0 local_trace))
      | Inr _ -> True))) =
  let s0 = IOStHist?.reflect (iost_get ()) in
  let action = (| cmd, argz |) in
  match pi_check s0 action with
  | true -> pi_static_cmd cmd pi_check argz
  | false -> IOStHist?.reflect(iost_throw (res cmd) GIO_pi_check_failed)

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
          s1 == (apply_changes s0 local_trace))
      | Inr _ -> True))) by (explode (); bump_nth 2; dump "h") =
  let s0 = get () in
  let action = (| cmd, argz |) in
  match default_check s0 action with
  | true -> mixed_cmd cmd pi_check argz 
  | false -> raise GIO_default_check_failed

effect GIO
  (a:Type)
  (pi_check : check_type) =
  IOStHist a 
    (requires (fun s0 -> 
      fold_left default_check s0 &&
      fold_left pi_check s0))
    (ensures (fun s0 (result) local_trace ->
      (match result with
      | Inl v -> let (s1, r) = v in (
          s1 == (apply_changes s0 local_trace) /\
          fold_left (default_check) s1 /\
          fold_left (pi_check) s1)
      | Inr _ -> True)))


let read (fd:file_descr) :
  IOStHist string
    (requires (fun past_history -> is_open fd past_history))
    (ensures (fun _ _ _ -> True))
  
