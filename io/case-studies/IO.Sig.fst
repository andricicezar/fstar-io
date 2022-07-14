module IO.Sig

open FStar.List.Tot.Base

open Common
include Types
include Free
include Hist

type cmds =
  (* files *)
  | Openfile 
  (* file descriptors *)
  | Read 
  | Write
  | Close
  (* sockets *)
  | Socket
  | Setsockopt
  | Bind
  | SetNonblock
  | Listen
  | Accept
  | Select
  (* instrumentation *)
  | GetTrace

(** the io free monad does not contain the GetTrace step **)
let _io_cmds x : bool = 
  x = Openfile || x = Read || x = Write || x = Close || 
  x = Socket || x = Setsockopt || x = Bind || x = SetNonblock ||
  x = Listen || x = Accept || x = Select
type io_cmds = x:cmds{_io_cmds x}

unfold let io_args (cmd:io_cmds) : Type =
  match cmd with
  | Openfile -> string * (list open_flag) * zfile_perm
  | Read -> file_descr * UInt8.t
  | Write -> file_descr * Bytes.bytes
  | Close -> file_descr
  | Socket -> unit
  | Setsockopt -> file_descr * socket_bool_option * bool
  | Bind -> file_descr * string * UInt8.t
  | SetNonblock -> file_descr
  | Listen -> file_descr * UInt8.t
  | Accept -> file_descr
  | Select -> lfds * lfds * lfds * UInt8.t

unfold let io_res (cmd:io_cmds) : Type =
  match cmd with
  | Openfile -> file_descr
  | Read -> Bytes.bytes * UInt8.t
  | Write -> unit
  | Close -> unit
  | Socket -> file_descr
  | Setsockopt -> unit
  | Bind -> unit
  | SetNonblock -> unit
  | Listen -> unit
  | Accept -> file_descr
  | Select -> lfds * lfds * lfds 

let io_resm (cmd:io_cmds) = either (io_res cmd) exn

unfold
let io_resm' (cmd:io_cmds) (arg:io_args cmd) = io_resm cmd

unfold
let io_sig : op_sig io_cmds = { args = io_args; res = io_resm'; }

noeq
type event =
  | EOpenfile : a:io_sig.args Openfile -> (r:io_sig.res Openfile a) -> event
  | ERead     : a:io_sig.args Read     -> (r:io_sig.res Read a)     -> event
  | EWrite     : a:io_sig.args Write     -> (r:io_sig.res Write a)     -> event
  | EClose    : a:io_sig.args Close    -> (r:io_sig.res Close a)    -> event
  | ESocket     : a:io_sig.args Socket     -> (r:io_sig.res Socket a)     -> event
  | ESetsockopt     : a:io_sig.args Setsockopt     -> (r:io_sig.res Setsockopt a)     -> event
  | EBind     : a:io_sig.args Bind     -> (r:io_sig.res Bind a)     -> event
  | ESetNonblock     : a:io_sig.args SetNonblock     -> (r:io_sig.res SetNonblock a)     -> event
  | EListen     : a:io_sig.args Listen     -> (r:io_sig.res Listen a)     -> event
  | EAccept     : a:io_sig.args Accept     -> (r:io_sig.res Accept a)     -> event
  | ESelect     : a:io_sig.args Select     -> (r:io_sig.res Select a)     -> event

let hist = Hist.hist #event

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
let inst_args (cmd:inst_cmds) =
  match cmd with
  | GetTrace -> unit

let inst_res (cmd:inst_cmds) (arg:inst_args cmd) =
  match cmd with
  | GetTrace -> list event

let inst_sig : op_sig inst_cmds = {
  args = inst_args;
  res = inst_res;
}

let _iio_cmds (cmd:cmds) : bool = _io_cmds cmd || cmd = GetTrace
type iio_cmds = cmd:cmds{_iio_cmds cmd}
let iio_sig : op_sig iio_cmds = add_sig cmds io_sig inst_sig

type io a = free io_cmds io_sig (trace -> trace -> Type0) a
let io_return (x:'a) : io 'a =
  free_return io_cmds io_sig _ 'a x

let io_bind (#a:Type) (#b:Type) l k : io b =
  free_bind io_cmds io_sig _ a b l k

// THE IIO FREE MONAD
type iio a = free cmds iio_sig (trace -> trace -> Type0) a
let iio_return (x:'a) : iio 'a =
  free_return cmds iio_sig _ 'a x

let iio_bind (#a:Type) (#b:Type) l k : iio b =
  free_bind cmds iio_sig _ a b l k

let convert_call_to_event
  (cmd:io_cmds)
  (arg:io_sig.args cmd)
  (r:io_sig.res cmd arg) =
  match cmd with
  | Openfile -> EOpenfile arg r
  | Read     -> ERead arg r
  | Write -> EWrite arg r
  | Close -> EClose arg r
  | Socket -> ESocket arg r
  | Setsockopt -> ESetsockopt arg r
  | Bind -> EBind arg r
  | SetNonblock -> ESetNonblock arg r
  | Listen -> EListen arg r
  | Accept -> EAccept arg r
  | Select -> ESelect arg r

// OTHER TYPES & UTILS
unfold
let apply_changes (history local_events:trace) : Tot trace =
  (List.rev local_events) @ history

let destruct_event (e:event) : ( cmd:io_cmds & (arg:io_sig.args cmd) & io_sig.res cmd arg )  =
  match e with
  | EOpenfile arg res -> (| Openfile, arg, res |)
  | ERead arg res -> (| Read, arg, res |)
  | EWrite arg res -> (| Write, arg, res |)
  | EClose arg res -> (| Close, arg, res |)
  | ESocket arg res -> (| Socket, arg, res |)
  | ESetsockopt arg res -> (| Setsockopt, arg, res |)
  | EBind arg res -> (| Bind, arg, res |)
  | ESetNonblock arg res -> (| SetNonblock, arg, res |)
  | EListen arg res -> (| Listen, arg, res |)
  | EAccept arg res -> (| Accept, arg, res |)
  | ESelect arg res -> (| Select, arg, res |)

let rec is_open (fd:file_descr) (h:trace) : bool =
  match h with
  | [] -> false
  | h :: tail -> match h with
               | EOpenfile _ fd' ->
                   if Inl? fd' && Inl?.v fd' = fd then true
                   else is_open fd tail
               | EClose fd' _ ->
                    if fd = fd' then false
                    else is_open fd tail
               | _ -> is_open fd tail

unfold let io_pre (cmd:io_cmds) (arg:io_args cmd) (h:trace) : Type0 =
  match cmd with
  | _ -> True

unfold let iio_wps (cmd:iio_cmds) (arg:iio_sig.args cmd) : hist (iio_sig.res cmd arg) = fun p h ->
  match cmd with
  | GetTrace -> p [] h
  | _ -> io_pre cmd arg h /\ (forall (r:iio_sig.res cmd arg). p [convert_call_to_event cmd arg r] r)
