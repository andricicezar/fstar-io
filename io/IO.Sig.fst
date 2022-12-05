module IO.Sig

open FStar.List.Tot.Base

include CommonUtils
include Free
include Hist

type cmds = | Openfile | Read | Close | GetTrace

(** the io free monad does not contain the GetTrace step **)
let _io_cmds x : bool = x = Openfile || x = Read || x = Close
type io_cmds : Type = x:cmds{_io_cmds x}

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

let io_resm (cmd:io_cmds) (arg:io_args cmd) = resexn (io_res cmd)

unfold
let io_resm' (cmd:io_cmds) (arg:io_args cmd) = r:(io_resm cmd arg){~(r == Inr Contract_failure)}

unfold
let io_sig : op_sig io_cmds = { args = io_args; res = io_resm'; }

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

type io a = free io_cmds io_sig a
let io_return (x:'a) : io 'a =
  free_return io_cmds io_sig 'a x

let io_bind (#a:Type) (#b:Type) l k : io b =
  free_bind io_cmds io_sig a b l k

// THE IIO FREE MONAD
type iio (a:Type) = free cmds iio_sig a

let iio_return (x:'a) : iio 'a =
  free_return cmds iio_sig 'a x

let iio_bind (#a:Type) (#b:Type) l k : iio b =
  free_bind cmds iio_sig a b l k

let convert_call_to_event
  (cmd:io_cmds)
  (arg:io_sig.args cmd)
  (r:io_sig.res cmd arg) =
  match cmd with
  | Openfile -> EOpenfile arg r
  | Read     -> ERead arg r
  | Close    -> EClose arg r

// OTHER TYPES & UTILS
unfold
let apply_changes (history local_events:trace) : Tot trace =
  (List.rev local_events) @ history

let destruct_event (e:event) : ( cmd:io_cmds & (arg:io_sig.args cmd) & io_sig.res cmd arg )  =
  match e with
  | EOpenfile arg res -> (| Openfile, arg, res |)
  | ERead arg res -> (| Read, arg, res |)
  | EClose arg res -> (| Close, arg, res |)

let rec is_open (fd:file_descr) (h:trace) : bool =
  match h with
  | [] -> false
  | h :: tail -> match h with
               | EOpenfile _ (Inl fd') ->
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

unfold let iio_wps (cmd:iio_cmds) (arg:iio_sig.args cmd) : hist (iio_sig.res cmd arg) = fun p h ->
  match cmd with
  | GetTrace -> p [] h
  | _ -> io_pre cmd arg h /\ (forall (r:iio_sig.res cmd arg). p [convert_call_to_event cmd arg r] r)
