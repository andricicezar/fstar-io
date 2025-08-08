module MIO.Sig

open FStar.List.Tot.Base
open FStar.Ghost

include CommonUtils
include UnixTypes
include Free
include Hist

type mio_ops =
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
  | Access
  | Stat
  (* instrumentation *)
  | GetTrace
  | GetST

(** the io free monad does not contain the GetTrace step **)
let _io_ops x : bool = 
  x = Openfile || x = Read || x = Write || x = Close || 
  x = Socket || x = Setsockopt || x = Bind || x = SetNonblock ||
  x = Listen || x = Accept || x = Select || x = Access || x = Stat
type io_ops : Type = x:mio_ops{_io_ops x}

unfold let io_args (op:io_ops) : Type =
  match op with
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
  | Access -> string * list access_permission
  | Stat -> string

unfold let io_res (op:io_ops) : Type =
  match op with
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
  | Access -> unit
  | Stat -> stats

let io_resm (op:io_ops) (arg:io_args op) = resexn (io_res op)

unfold
let io_resm' (op:io_ops) (arg:io_args op) = r:(io_resm op arg){~(r == Inr Contract_failure)}

unfold
let io_sig : op_sig io_ops = { args = io_args; res = io_resm'; }

noeq
type event =
  | EOpenfile      : caller -> a:io_sig.args Openfile      -> (r:io_sig.res Openfile a)     -> event
  | ERead          : caller -> a:io_sig.args Read          -> (r:io_sig.res Read a)         -> event
  | EWrite         : caller -> a:io_sig.args Write         -> (r:io_sig.res Write a)        -> event
  | EClose         : caller -> a:io_sig.args Close         -> (r:io_sig.res Close a)        -> event
  | ESocket        : caller -> a:io_sig.args Socket        -> (r:io_sig.res Socket a)       -> event
  | ESetsockopt    : caller -> a:io_sig.args Setsockopt    -> (r:io_sig.res Setsockopt a)   -> event
  | EBind          : caller -> a:io_sig.args Bind          -> (r:io_sig.res Bind a)         -> event
  | ESetNonblock   : caller -> a:io_sig.args SetNonblock   -> (r:io_sig.res SetNonblock a)  -> event
  | EListen        : caller -> a:io_sig.args Listen        -> (r:io_sig.res Listen a)       -> event
  | EAccept        : caller -> a:io_sig.args Accept        -> (r:io_sig.res Accept a)       -> event
  | ESelect        : caller -> a:io_sig.args Select        -> (r:io_sig.res Select a)       -> event
  | EAccess        : caller -> a:io_sig.args Access        -> (r:io_sig.res Access a)       -> event
  | EStat          : caller -> a:io_sig.args Stat          -> (r:io_sig.res Stat a)         -> event

type trace = list event

type m_ops = x:mio_ops{x = GetTrace || x = GetST}

(** We only need GetTrace because we assume that our actions are
updating the trace for us. Therefore, at extraction, our actions
should be linked with wrapped primitives that initialize a
trace on the heap (?) and updates it with events.
GetTrace will be linked with a function that returns the reference
to the trace from the heap. **)

(* Monitoring state. *)
[@@erasable]
noeq
type mstate = {
  typ : Type0;
  abstracts : typ -> trace -> Type0;
}

type mst_updater (mst:mstate) : Type0 =
  s0:mst.typ -> e:event -> h : Ghost.erased trace ->
  Pure mst.typ
       (requires mst.abstracts s0 h)
       (ensures fun s1 -> mst.abstracts s1 (e::h))

noeq
type mst_impl (mst:mstate) = {
  init : (init : mst.typ{mst.abstracts init []});
  update : mst_updater mst;
}

(** Is our assumption limiting how the IO effect can be used?
 What if somebody wants to use only the IO effect? Then,
at extraction, they have to be careful to link it directly with the
primitives, and not with the wrapped version, otherwise, they will
suffer a performance penalty. **)
let m_args (op:m_ops) =
  match op with
  | GetTrace -> unit
  | GetST -> unit

let m_res (mst:mstate) (op:m_ops) (arg:m_args op) =
  match op with
  | GetTrace -> erased trace 
  | GetST -> mst.typ

let m_sig (mst:mstate) : op_sig m_ops = {
  args = m_args;
  res = m_res mst;
}

let mio_sig (mst:mstate) : op_sig mio_ops = add_sig mio_ops io_sig (m_sig mst)

// THE MIO FREE MONAD
type mio (mst:mstate) (a:Type) = free mio_ops (mio_sig mst) a

let mio_return #mst (x:'a) : mio mst 'a =
  free_return mio_ops (mio_sig mst) 'a x

let mio_bind #mst (#a:Type) (#b:Type) l k : mio mst b =
  free_bind mio_ops (mio_sig mst) a b l k

let convert_call_to_event
  caller
  (op:io_ops)
  (arg:io_sig.args op)
  (r:io_sig.res op arg) =
  match op with
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
  | Access -> EAccess caller arg r
  | Stat -> EStat caller arg r

// OTHER TYPES & UTILS
unfold
let apply_changes (history local_events:trace) : Tot trace =
  (List.rev local_events) @ history

unfold type event_data =
  caller & op:io_ops & arg:(io_sig.args op) & io_sig.res op arg

let mk_event (x : event_data) : event =
  let (| caller, e, arg, res |) = x in
  match e with
  | Openfile -> EOpenfile caller arg res
  | Read -> ERead caller arg res
  | Write -> EWrite caller arg res
  | Close -> EClose caller arg res
  | Socket -> ESocket caller arg res
  | Setsockopt -> ESetsockopt caller arg res
  | Bind -> EBind caller arg res
  | SetNonblock -> ESetNonblock caller arg res
  | Listen -> EListen caller arg res
  | Accept -> EAccept caller arg res
  | Select -> ESelect caller arg res
  | Access -> EAccess caller arg res
  | Stat -> EStat caller arg res


let destruct_event (e:event) : d: event_data { e == mk_event d } =
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
  | EAccess caller arg res -> (| caller, Access, arg, res |)
  | EStat caller arg res -> (| caller, Stat, arg, res |)

unfold let io_pre (op:io_ops) (arg:io_args op) (h:trace) : Type0 =
  True
  (**
  match op with
  | Openfile -> True
  | Read -> is_open arg h
  | Write -> let (fd, _):(file_descr*string) = arg in is_open fd h
  | Close -> is_open arg h**)

unfold let io_post (op:io_ops) (arg:io_args op) (res : io_sig.res op arg) : Type0 =
  match op with
  | Read -> Inl? res ==> Bytes.length (fst #Bytes.bytes #UInt8.t (Inl?.v res)) < UInt8.v (snd #file_descr #UInt8.t arg)
  | _ -> True

unfold let mio_wps #mst caller (op:mio_ops) (arg:(mio_sig mst).args op) : hist ((mio_sig mst).res op arg) =
  fun (p : hist_post ((mio_sig mst).res op arg)) h ->
  match op with
  | GetTrace ->
    let p : hist_post (Ghost.erased trace) = p in // need some handholding
    p [] (Ghost.hide h)
  | GetST -> forall (s:mst.typ). s `mst.abstracts` h ==> p [] s // any concrete state modelling the trace
  | _ -> io_pre op arg h /\ (forall (r:(mio_sig mst).res op arg). io_post op arg r ==> p [convert_call_to_event caller op arg r] r)
