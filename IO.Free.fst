module IO.Free

open Common
include Free

type cmds = | Openfile | Read | Close | Throw | GetTrace

(** Wish: It would be nice to define exn on top of free, and after
that to define io on top of exn, but we use this big cmds with
refeniments, therefore we have to make a monolith **)

(** This steps are observable and produce events **)
let _obs_cmds x = x = Openfile || x = Read || x = Close

(** Silent steps refer to the impossibility of an observer to see
them. **)
let _tau_cmds x = not (_obs_cmds x)

type obs_cmds = x:cmds{_obs_cmds x}
type tau_cmds = x:cmds{_tau_cmds x}

(** the io free monad does not contain the GetTrace step **)
type io_cmds = x:cmds{_obs_cmds x || x = Throw}

unfold let io_args (cmd:io_cmds) : Type =
  match cmd with
  | Openfile -> string
  | Read -> file_descr
  | Close -> file_descr
  | Throw -> exn

unfold let io_res (cmd:io_cmds) : Type =
  match cmd with
  | Openfile -> file_descr
  | Read -> string
  | Close -> unit
  | Throw -> unit

(** The IO primitives have no reason to throw
`Contract_failure`, because they do not enforce any policy.
In practice, a primitive can throw any error, but I think
this is an assumption we can make to have more precise specification.
`Contract_failure` is an exception defined in `Common.fst` **)
let io_resm (cmd:io_cmds) =
  r:(maybe (io_res cmd))
    {~(Inr? r /\ Inr?.v r == Contract_failure)}

let io_sig : op_sig io_cmds = { args = io_args; res = io_resm; }

noeq
type event =
  | EOpenfile : a:io_args Openfile -> (r:io_resm Openfile) -> event
  | ERead     : a:io_args Read     -> (r:io_resm Read)     -> event
  | EClose    : a:io_args Close    -> (r:io_resm Close)    -> event

type trace = list event

type internal_cmds = x:cmds{x = GetTrace}

(** We only need GetTrace because we assume that our actions are
updating the trace for us. Therefore, at extraction, our actions
should be linked with wrapped primitives that initialize a
trace on the heap (?) and updates it with events.
GetTrace will be linked with a function that returns the reference
to the trace from the heap. **)

(** Is our assumption limiting how the IO effect can be used?
 What if somebody wants to use only the IO effect? Then,
at extraction, they have to be careful to link it directly with the
primitives, and not with the wrapped version, otherwise, they will
suffer a performance penalty. **)
let internal_res (x:internal_cmds) =
  match x with
  | GetTrace -> list event
let internal_resm (x:internal_cmds) = maybe (internal_res x)

let internal_sig : op_sig internal_cmds = {
  args = (fun (x:internal_cmds) -> match x with
    | GetTrace -> unit) ;
  res = internal_resm
}

let all_sig = add_sig cmds io_sig internal_sig

let args (cmd:cmds) : Type = all_sig.args cmd
let res (cmd:cmds)  : Type =
  if cmd = GetTrace then internal_res cmd
  else io_res cmd

let resm (cmd:cmds) : (x:Type{x == all_sig.res cmd}) =
  admit ();
  maybe (res cmd)

type io a = free io_cmds io_sig (maybe a)
let io_return (a:Type) (x:a) : io a =
  free_return io_cmds io_sig (maybe a) (Inl x)
let io_throw (a:Type) (x:exn) : io a =
  free_return io_cmds io_sig (maybe a) (Inr x)

let rec io_try_catch_finnaly
  (a b:Type)
  (try_block:io a)
  (catch_block:exn -> io b)
  (finnaly:a -> io b) :
  Tot (io b) =
  match try_block with
  | Return (Inl x) -> finnaly x
  | Return (Inr err) -> catch_block err
  | Call cmd argz fnc ->
      Call cmd argz (fun res ->
        io_try_catch_finnaly a b (fnc res) catch_block finnaly)

let io_bind (a:Type) (b:Type) l k : io b =
  io_try_catch_finnaly a b l (io_throw b) k

let io_call (cmd:io_cmds) (arg:io_args cmd) : io (io_res cmd) =
  Call cmd arg (fun (v:io_resm cmd) ->
    match v with
    | Inl x -> io_return (io_res cmd) x
    | Inr err -> io_throw (io_res cmd) err)

// THE IIO FREE MONAD
type iio a = free cmds all_sig (maybe a)
let iio_return (a:Type) (x:a) : iio a =
  free_return cmds all_sig (maybe a) (Inl x)
let iio_throw (a:Type) (x:exn) : iio a =
  free_return cmds all_sig (maybe a) (Inr x)

let rec iio_try_catch_finnaly
  (a b:Type)
  (try_block:iio a)
  (catch_block:exn -> iio b)
  (finnaly:a -> iio b) :
  Tot (iio b) =
  match try_block with
  | Return (Inl x) -> finnaly x
  | Return (Inr err) -> catch_block err
  | Call cmd argz fnc ->
      Call cmd argz (fun res ->
        iio_try_catch_finnaly a b (fnc res) catch_block finnaly)

let iio_bind (a:Type) (b:Type) l k : iio b =
  iio_try_catch_finnaly a b l (iio_throw b) k

let iio_call (cmd:cmds) (arg:args cmd) : iio (res cmd) =
  Call cmd arg (fun (v:(maybe (res cmd))) ->
    match v with
    | Inl x -> iio_return (res cmd) x
    | Inr err -> iio_throw (res cmd) err)

// OTHER TYPES & UTILS
type action_type = (cmd : io_cmds) & (args cmd)

type monitorable_prop = (history:trace) -> (action:action_type) -> Tot bool

let convert_event_to_action (e:event) : action_type =
  match e with
  | EOpenfile arg _ -> (| Openfile, arg |)
  | ERead arg _ -> (| Read, arg |)
  | EClose arg _ -> (| Close, arg |)

let convert_call_to_event
  (cmd:obs_cmds)
  (arg:io_args cmd)
  (r:io_resm cmd) =
  match cmd with
  | Openfile -> EOpenfile arg r
  | Read -> ERead arg r
  | Close -> EClose arg r

let rec enforced_locally
  (check : monitorable_prop)
  (h l: trace) :
  Tot bool (decreases l) =
  match l with
  | [] -> true
  | hd  ::  t ->
    let action = convert_event_to_action hd in
    if check h action then enforced_locally (check) (hd::h) t
    else false

(** enforced_globally could be written as:
`enforced_locally check [] h` but fstar can not prove as easily that
form **)
let rec enforced_globally (check : monitorable_prop) (h : trace) : Tot bool =
  match h with
  | [] -> true
  | h  ::  t ->
    let action = convert_event_to_action h in
    if check t action then enforced_globally (check) t
    else false

let rev_append_rev_append () : Lemma (
  forall (h le1 le2:trace).
    ((List.rev le2) @ (List.rev le1) @ h) ==
      ((List.rev (le1@le2)) @ h))
   by (FStar.Tactics.Derived.l_to_r [`List.append_assoc;`List.rev_append])
      = ()

unfold
let apply_changes (history local_events:trace) : Tot trace =
  (List.rev local_events) @ history
