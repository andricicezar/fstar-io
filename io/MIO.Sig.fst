module MIO.Sig

open FStar.List.Tot.Base

include CommonUtils
include Free
include Hist

type cmds = | Openfile | Read | Close | Write | GetTrace | GetST

(** the io free monad does not contain the GetTrace/GetST steps **)
let _io_cmds x : bool = x = Openfile || x = Read || x = Close || x = Write
type io_cmds : Type = x:cmds{_io_cmds x}

unfold let io_args (cmd:io_cmds) : Type =
  match cmd with
  | Openfile -> string
  | Read -> file_descr
  | Write -> file_descr * string
  | Close -> file_descr

unfold let io_res (cmd:io_cmds) : Type =
  match cmd with
  | Openfile -> file_descr
  | Read -> string
  | Write -> unit 
  | Close -> unit

unfold
let io_resm (cmd:io_cmds) (arg:io_args cmd) = resexn (io_res cmd)

unfold
let io_resm' (cmd:io_cmds) (arg:io_args cmd) = r:(io_resm cmd arg){~(r == Inr Contract_failure)}

unfold
let io_sig : op_sig io_cmds = { args = io_args; res = io_resm'; }

noeq
type event =
  | EOpenfile : caller -> a:io_sig.args Openfile -> (r:io_sig.res Openfile a) -> event
  | ERead     : caller -> a:io_sig.args Read     -> (r:io_sig.res Read a)     -> event
  | EWrite    : caller -> a:io_sig.args Write    -> (r:io_sig.res Write a)    -> event
  | EClose    : caller -> a:io_sig.args Close    -> (r:io_sig.res Close a)    -> event

type trace = list event

type m_cmds = x:cmds{x = GetTrace || x = GetST}

(** We only need GetTrace/GetST because we assume that our actions are
updating the trace for us. Therefore, at extraction, our actions
should be linked with wrapped primitives that initialize a
trace on the heap (?) and updates it with events.
GetTrace will be linked with a function that returns the reference
to the trace from the heap. **)

(* Monitoring state. *)
[@@erasable]
noeq
type mst = {
  cst : Type0;
  models : cst -> trace -> Type0;
}

(** Is our assumption limiting how the IO effect can be used?
 What if somebody wants to use only the IO effect? Then,
at extraction, they have to be careful to link it directly with the
primitives, and not with the wrapped version, otherwise, they will
suffer a performance penalty. **)
let m_args (mst:mst) (cmd:m_cmds) =
  match cmd with
  | GetTrace -> unit
  | GetST -> unit

let m_res (mst:mst) (cmd:m_cmds) (arg:m_args mst cmd) =
  match cmd with
  | GetTrace -> Ghost.erased trace 
  | GetST -> mst.cst

let m_sig (mst:mst): op_sig m_cmds = {
  args = m_args mst;
  res = m_res mst;
}

let _mio_cmds (cmd:cmds) : bool = _io_cmds cmd || cmd = GetTrace || cmd = GetST
type mio_cmds = cmd:cmds{_mio_cmds cmd}
let mio_sig (mst:mst) : op_sig mio_cmds = add_sig cmds io_sig (m_sig mst)

// THE IIO FREE MONAD
type mio (mst:mst) (a:Type) = free cmds (mio_sig mst) a

let mio_return #st (x:'a) : mio st 'a =
  free_return cmds (mio_sig st) 'a x

let mio_bind #st (#a:Type) (#b:Type) l k : mio st b =
  free_bind cmds (mio_sig st) a b l k

let convert_call_to_event
  caller
  (cmd:io_cmds)
  (arg:io_sig.args cmd)
  (r:io_sig.res cmd arg) =
  match cmd with
  | Openfile -> EOpenfile caller arg r
  | Read     -> ERead caller arg r
  | Write    -> EWrite caller arg r
  | Close    -> EClose caller arg r

// OTHER TYPES & UTILS
unfold
let apply_changes (history local_events:trace) : Tot trace =
  (List.rev local_events) @ history

let destruct_event (e:event) : ( caller & cmd:io_cmds & (arg:io_sig.args cmd) & io_sig.res cmd arg )  =
  match e with
  | EOpenfile caller arg res -> (| caller, Openfile, arg, res |)
  | ERead caller arg res -> (| caller, Read, arg, res |)
  | EWrite caller arg res -> (| caller, Write, arg, res |)
  | EClose caller arg res -> (| caller, Close, arg, res |)

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

unfold let io_post (cmd:io_cmds) (arg:io_args cmd) (res : io_sig.res cmd arg) : Type0 =
  match cmd with
  | Read -> Inl? res ==> Bytes.length (fst #Bytes.bytes #UInt8.t (Inl?.v res)) < UInt8.v (snd #file_descr #UInt8.t arg)
  | _ -> True

unfold let mio_wps #mst caller (cmd:mio_cmds) (arg:(mio_sig mst).args cmd) : hist ((mio_sig mst).res cmd arg) =
  fun (p : hist_post ((mio_sig mst).res cmd arg)) h ->
  match cmd with
  | GetTrace ->
    let p : hist_post (Ghost.erased trace) = p in // need some handholding
    p [] (Ghost.hide h)
  | GetST -> forall (x:mst.cst). mst.models x h ==> p [] x // any concrete state modelling the trace
  | _ -> io_pre cmd arg h /\ (forall (r:(mio_sig mst).res cmd arg). io_post cmd arg r ==> p [convert_call_to_event caller cmd arg r] r)
