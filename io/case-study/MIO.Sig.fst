module MIO.Sig

open FStar.List.Tot.Base

include CommonUtils
include UnixTypes
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
type io_cmds : Type = x:cmds{_io_cmds x}

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

let io_resm (cmd:io_cmds) (arg:io_args cmd) = resexn (io_res cmd)

unfold
let io_resm' (cmd:io_cmds) (arg:io_args cmd) = r:(io_resm cmd arg){~(r == Inr Contract_failure)}

unfold
let io_sig : op_sig io_cmds = { args = io_args; res = io_resm'; }

noeq
type event =
  | EOpenfile : caller:bool -> a:io_sig.args Openfile -> (r:io_sig.res Openfile a) -> event
  | ERead     : caller:bool -> a:io_sig.args Read     -> (r:io_sig.res Read a)     -> event
  | EWrite     : caller:bool -> a:io_sig.args Write     -> (r:io_sig.res Write a)     -> event
  | EClose    : caller:bool -> a:io_sig.args Close    -> (r:io_sig.res Close a)    -> event
  | ESocket     : caller:bool -> a:io_sig.args Socket     -> (r:io_sig.res Socket a)     -> event
  | ESetsockopt     : caller:bool -> a:io_sig.args Setsockopt     -> (r:io_sig.res Setsockopt a)     -> event
  | EBind     : caller:bool -> a:io_sig.args Bind     -> (r:io_sig.res Bind a)     -> event
  | ESetNonblock     : caller:bool -> a:io_sig.args SetNonblock     -> (r:io_sig.res SetNonblock a)     -> event
  | EListen     : caller:bool -> a:io_sig.args Listen     -> (r:io_sig.res Listen a)     -> event
  | EAccept     : caller:bool -> a:io_sig.args Accept     -> (r:io_sig.res Accept a)     -> event
  | ESelect     : caller:bool -> a:io_sig.args Select     -> (r:io_sig.res Select a)     -> event

type trace = list event

type m_cmds = x:cmds{x = GetTrace}

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
let m_args (cmd:m_cmds) =
  match cmd with
  | GetTrace -> unit

let m_res (cmd:m_cmds) (arg:m_args cmd) =
  match cmd with
  | GetTrace -> trace 

let m_sig : op_sig m_cmds = {
  args = m_args;
  res = m_res;
}

let _mio_cmds (cmd:cmds) : bool = _io_cmds cmd || cmd = GetTrace
type mio_cmds = cmd:cmds{_mio_cmds cmd}
let mio_sig : op_sig mio_cmds = add_sig cmds io_sig m_sig

// THE MIO FREE MONAD
type mio (a:Type) = free cmds mio_sig a

let mio_return (x:'a) : mio 'a =
  free_return cmds mio_sig 'a x

let mio_bind (#a:Type) (#b:Type) l k : mio b =
  free_bind cmds mio_sig a b l k

let convert_call_to_event
  (caller:bool)
  (cmd:io_cmds)
  (arg:io_sig.args cmd)
  (r:io_sig.res cmd arg) =
  match cmd with
  | Openfile -> EOpenfile caller arg r
  | Read     -> ERead caller arg r
  | Write -> EWrite caller arg r
  | Close -> EClose caller arg r
  | Socket -> ESocket caller arg r
  | Setsockopt -> ESetsockopt caller arg r
  | Bind -> EBind caller arg r
  | SetNonblock -> ESetNonblock caller arg r
  | Listen -> EListen caller arg r
  | Accept -> EAccept caller arg r
  | Select -> ESelect caller arg r

// OTHER TYPES & UTILS
unfold
let apply_changes (history local_events:trace) : Tot trace =
  (List.rev local_events) @ history

let destruct_event (e:event) : ( bool & cmd:io_cmds & (arg:io_sig.args cmd) & io_sig.res cmd arg )  =
  match e with
  | EOpenfile caller arg res -> (| caller, Openfile, arg, res |)
  | ERead caller arg res -> (| caller, Read, arg, res |)
  | EWrite caller arg res -> (| caller, Write, arg, res |)
  | EClose caller arg res -> (| caller, Close, arg, res |)
  | ESocket caller arg res -> (| caller, Socket, arg, res |)
  | ESetsockopt caller arg res -> (| caller, Setsockopt, arg, res |)
  | EBind caller arg res -> (| caller, Bind, arg, res |)
  | ESetNonblock caller arg res -> (| caller, SetNonblock, arg, res |)
  | EListen caller arg res -> (| caller, Listen, arg, res |)
  | EAccept caller arg res -> (| caller, Accept, arg, res |)
  | ESelect caller arg res -> (| caller, Select, arg, res |)
let rec is_open (fd:file_descr) (h:trace) : bool =
  match h with
  | [] -> false
  | h :: tail -> match h with
               | EOpenfile _ _ (Inl fd') ->
                   if fd = fd' then true
                   else is_open fd tail
               | EClose _ fd' _ ->
                    if fd = fd' then false
                    else is_open fd tail
               | _ -> is_open fd tail

unfold let io_pre (cmd:io_cmds) (arg:io_args cmd) (h:trace) : Type0 =
  True
  (**
  match cmd with
  | Openfile -> True
  | Read -> is_open arg h
  | Write -> let (fd, _):(file_descr*string) = arg in is_open fd h
  | Close -> is_open arg h**)

unfold let mio_wps (caller:bool) (cmd:mio_cmds) (arg:mio_sig.args cmd) : hist (mio_sig.res cmd arg) = fun p h ->
  match cmd with
  | GetTrace -> p [] h
  | _ -> io_pre cmd arg h /\ (forall (r:mio_sig.res cmd arg). p [convert_call_to_event caller cmd arg r] r)
