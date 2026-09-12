module Free.IO

open Common
include Free

type cmds = | Openfile | Read | Close | Throw | GetTrace

(** Wish: It would be nice to define exn on top of free, and after
that to define io on top of exn, but we use this big cmds with
refeniments, therefore we have to make a monolith **)

(** the io free monad does not contain the GetTrace step **)
let _io_cmds x : bool = x = Openfile || x = Read || x = Close
type io_cmds = x:cmds{_io_cmds x}

let _base_cmds x : bool = _io_cmds x || x = Throw
type base_cmds = x:cmds{_base_cmds x}

let base_args (cmd:base_cmds) : Type =
  match cmd with
  | Openfile -> string
  | Read -> file_descr
  | Close -> file_descr
  | Throw -> exn

let _io_res (cmd:io_cmds) : Type =
  match cmd with
  | Openfile -> file_descr
  | Read -> string
  | Close -> unit

let base_res (cmd:base_cmds) : Type =
  match cmd with
  | Throw -> False
  | _ -> maybe (_io_res cmd)

let io_sig : op_sig base_cmds = { args = base_args; res = base_res; }

noeq
type event =
  | EOpenfile : a:base_args Openfile -> (r:base_res Openfile) -> event
  | ERead     : a:base_args Read     -> (r:base_res Read)     -> event
  | EClose    : a:base_args Close    -> (r:base_res Close)    -> event
  | EThrow    : a:base_args Throw    -> event

type trace = list event

type inst_cmds = x:cmds{x = GetTrace}

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
let inst_res (x:inst_cmds) =
  match x with
  | GetTrace -> list event

let inst_sig : op_sig inst_cmds = {
  args = (fun (x:inst_cmds) -> match x with
    | GetTrace -> unit) ;
  res = inst_res
}

let iio_sig = add_sig cmds io_sig inst_sig

let args (cmd:cmds) : Type = iio_sig.args cmd
let res (cmd:cmds)  : (x:Type{x == iio_sig.res cmd}) =
  admit ();
  if cmd = GetTrace then inst_res cmd
  else base_res cmd

type io a = free base_cmds io_sig a
let io_return (a:Type) (x:a) : io a =
  free_return base_cmds io_sig a x

let rec io_try_catch_finnaly
  (a b:Type)
  (try_block:io a)
  (catch_block:exn -> io b)
  (finnaly:a -> io b) :
  Tot (io b) =
  match try_block with
  | Return x -> finnaly x
  (** Cezar: we can replace the node Throw directly with the catch_block.
      This is a nice solution because it implies that in the tree a 
      node Throw is a 'leaf' (except, it is followed by a `Return False`
      node). This simplifies how we do the interpretation later where,
      if we meet a Throw node, then we know the computation ended. **)
  | Call Throw err fnc -> catch_block err
  | Call cmd argz fnc ->
      Call cmd argz (fun res ->
        io_try_catch_finnaly a b (fnc res) catch_block finnaly)

let io_bind (a:Type) (b:Type) l k : io b =
  io_try_catch_finnaly a b l (fun err -> Call Throw err Return) k

let io_call (cmd:base_cmds) (arg:base_args cmd) : io (base_res cmd) =
  Call cmd arg Return

// THE IIO FREE MONAD
type iio a = free cmds iio_sig a
let iio_return (a:Type) (x:a) : iio a =
  free_return cmds iio_sig a x

let rec iio_try_catch_finnaly
  (a b:Type)
  (try_block:iio a)
  (catch_block:exn -> iio b)
  (finnaly:a -> iio b) :
  Tot (iio b) =
  match try_block with
  | Return x -> finnaly x
  | Call Throw err fnc -> catch_block err
  | Call cmd argz fnc ->
      Call cmd argz (fun res ->
        iio_try_catch_finnaly a b (fnc res) catch_block finnaly)

let iio_bind (a:Type) (b:Type) l k : iio b =
  iio_try_catch_finnaly a b l (fun err -> Call Throw err Return) k

let iio_call (cmd:cmds) (arg:args cmd) : iio (res cmd) =
  Call cmd arg Return

// OTHER TYPES & UTILS
type action_type = (cmd : base_cmds) & (args cmd)

type monitorable_prop = (history:trace) -> (action:action_type) -> Tot bool

let convert_event_to_action (e:event) : action_type =
  match e with
  | EOpenfile arg _ -> (| Openfile, arg |)
  | ERead arg _ -> (| Read, arg |)
  | EClose arg _ -> (| Close, arg |)
  | EThrow arg -> (| Throw, arg |)

let convert_call_to_event
  (cmd:io_cmds)
  (arg:base_args cmd)
  (r:base_res cmd) =
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
