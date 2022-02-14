module Free.Sig

open FStar.List.Tot.Base

open Free

assume val file_descr : eqtype

type cmds =
  | Requires
  | Openfile
  | Read
  | Close
  | GetTrace

let _req_cmds (x:cmds) : bool = x = Requires
type req_cmds : Type0 = x:cmds{_req_cmds x} 
unfold let req_args (x:req_cmds) : Type = pure_pre 
unfold let req_res (x:req_cmds) (pre:req_args x) : Type = squash pre
(** fails here because universe problems **)
let req_sig : op_sig req_cmds = { args = req_args; res = req_res; }

(** the io free monad does not contain the GetTrace step **)
let _io_cmds x : bool = x = Openfile || x = Read || x = Close
type io_cmds : Type0 = x:cmds{_io_cmds x}

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

let io_resm (cmd:io_cmds) (arg:io_args cmd) = option (io_res cmd)

let io_sig : op_sig io_cmds = { args = io_args; res = io_resm; }


type pio_cmds : Type = x:cmds{_io_cmds x || _req_cmds x}
#set-options "--print_universes"
let pio_sig : op_sig pio_cmds = add_sig cmds #_io_cmds #_req_cmds io_sig req_sig

noeq
type event =
  | EOpenfile : a:io_sig.args Openfile -> (r:io_sig.res Openfile a) -> event
  | ERead     : a:io_sig.args Read     -> (r:io_sig.res Read a)     -> event
  | EClose    : a:io_sig.args Close    -> (r:io_sig.res Close a)    -> event

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
let inst_arg (x:inst_cmds) = 
  match x with
  | GetTrace -> unit

let inst_res (x:inst_cmds) (arg:inst_arg x) =
  match x with
  | GetTrace -> list event

let inst_sig : op_sig inst_cmds = { args = inst_arg; res = inst_res }

type iio_cmds : Type = x:cmds{_io_cmds x || x = GetTrace}
let iio_sig : op_sig iio_cmds = add_sig cmds io_sig inst_sig

type io a = free io_cmds io_sig a
let io_return (x:'a) : io 'a =
  free_return io_cmds io_sig 'a x

let io_bind (#a:Type) (#b:Type) l k : io b =
  free_bind io_cmds io_sig a b l k

// THE IIO FREE MONAD
type iio a = free iio_cmds iio_sig a
let iio_return (x:'a) : iio 'a =
  free_return iio_cmds iio_sig 'a x

let iio_bind (#a:Type) (#b:Type) l k : iio b =
  free_bind iio_cmds iio_sig a b l k

// OTHER TYPES & UTILS
type action_type = (cmd : io_cmds) & (io_sig.args cmd)

type monitorable_prop = (history:trace) -> (action:action_type) -> Tot bool

let convert_event_to_action (e:event) : action_type =
  match e with
  | EOpenfile arg _ -> (| Openfile, arg |)
  | ERead arg _ -> (| Read, arg |)
  | EClose arg _ -> (| Close, arg |)

let convert_call_to_event
  (cmd:io_cmds)
  (arg:io_args cmd)
  (r:io_resm cmd arg) =
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

let rev_append_rev_append () : Lemma (
  forall (h le1 le2:trace).
    ((List.rev le2) @ (List.rev le1) @ h) ==
      ((List.rev (le1@le2)) @ h))
   by (FStar.Tactics.Derived.l_to_r [`List.append_assoc;`List.rev_append])
      = ()

unfold
let apply_changes (history local_events:trace) : Tot trace =
  (List.rev local_events) @ history

let destruct_event (e:event) : ( cmd:io_cmds & (arg:io_args cmd) & io_resm cmd arg )  =
  match e with
  | EOpenfile arg res -> (| Openfile, arg, res |)
  | ERead arg res -> (| Read, arg, res |)
  | EClose arg res -> (| Close, arg, res |)


let rec is_open (fd:file_descr) (h:trace) : bool =
  match h with
  | [] -> false
  | h :: tail -> match h with
               | EOpenfile _ (Some fd') ->
                   if fd = fd' then true
                   else is_open fd tail
               | EClose fd' _ ->
                    if fd = fd' then false
                    else is_open fd tail
               | _ -> is_open fd tail

unfold let io_pre (cmd:io_cmds) (arg:io_args cmd) (h:trace) : Type0 =
  match cmd with
  | Openfile -> True
  | Read -> is_open arg h
  | Close -> is_open arg h

(** This file is replaced during linking with a file that contains the real
implementation of the commands. **)
let io_call (cmd:io_cmds) (arg:io_sig.args cmd) : io (iio_sig.res cmd arg) =
  Call cmd arg Return

(** Since we can lift from io to iio, `iio_call` should be used only for 
`GetTrace`. **)
let iio_call (cmd:iio_cmds) (arg:iio_sig.args cmd) : iio (iio_sig.res cmd arg) =
  Call cmd arg Return
