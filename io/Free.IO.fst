module Free.IO

open FStar.List.Tot.Base

open Common
open Free

type cmds = | Openfile | Read | Close | GetTrace

(** Wish: It would be nice to define exn on top of free, and after
that to define io on top of exn, but we use this big cmds with
refeniments, therefore we have to make a monolith **)

(** the io free monad does not contain the GetTrace step **)
let _io_cmds x : bool = x = Openfile || x = Read || x = Close
type io_cmds = x:cmds{_io_cmds x}

unfold let io_args (cmd:io_cmds) : Type =
  match cmd with
  | Openfile -> string
  | Read -> file_descr
  | Close -> file_descr

unfold let io_res (cmd:io_cmds) : Type =
  match cmd with
  | Openfile -> file_descr
  | Read -> string
  | Close -> unit

let io_resm (cmd:io_cmds) = maybe (io_res cmd)

let io_sig : op_sig io_cmds = { args = io_args; res = io_resm; }

noeq
type event =
  | EOpenfile : a:io_args Openfile -> (r:io_resm Openfile) -> event
  | ERead     : a:io_args Read     -> (r:io_resm Read)     -> event
  | EClose    : a:io_args Close    -> (r:io_resm Close)    -> event

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
  else io_resm cmd

type io a = free io_cmds io_sig a
let io_return (a:Type) (x:a) : io a =
  free_return io_cmds io_sig a x

let io_bind (a:Type) (b:Type) l k : io b =
  free_bind io_cmds io_sig a b l k

let io_call (cmd:io_cmds) (arg:io_args cmd) : io (io_resm cmd) =
  Call cmd arg Return

// THE IIO FREE MONAD
type iio a = free cmds iio_sig a
let iio_return (a:Type) (x:a) : iio a =
  free_return cmds iio_sig a x

let iio_bind (a:Type) (b:Type) l k : iio b =
  free_bind cmds iio_sig a b l k

let iio_call (cmd:cmds) (arg:args cmd) : iio (res cmd) =
  Call cmd arg Return

// OTHER TYPES & UTILS
type action_type = (cmd : io_cmds) & (args cmd)

type monitorable_prop = (history:trace) -> (action:action_type) -> Tot bool

let convert_event_to_action (e:event) : action_type =
  match e with
  | EOpenfile arg _ -> (| Openfile, arg |)
  | ERead arg _ -> (| Read, arg |)
  | EClose arg _ -> (| Close, arg |)

let convert_call_to_event
  (cmd:io_cmds)
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
