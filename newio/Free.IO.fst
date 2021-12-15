module Free.IO

open FStar.List.Tot.Base

open Free

assume val file_descr : eqtype

type cmds = | Openfile | Read | Close | GetTrace

(** Wish: It would be nice to define exn on top of free, and after
that to define io on top of exn, but we use this big cmds with
refeniments, therefore we have to make a monolith **)

(** the io free monad does not contain the GetTrace step **)
let _io_cmds x : bool = x = Openfile || x = Read || x = Close
type io_cmds = x:cmds{_io_cmds x}

let io_args (cmd:io_cmds) : Type =
  match cmd with
  | Openfile -> string
  | Read -> file_descr
  | Close -> file_descr

let io_res (cmd:io_cmds) : Type =
  match cmd with
  | Openfile -> file_descr
  | Read -> string
  | Close -> unit

let io_resm (cmd:io_cmds) = option (io_res cmd)

let io_sig : op_sig io_cmds = { args = io_args; res = io_resm; }

noeq
type event =
  | EOpenfile : a:io_args Openfile -> (r:io_resm Openfile) -> event
  | ERead     : a:io_args Read     -> (r:io_resm Read)     -> event
  | EClose    : a:io_args Close    -> (r:io_resm Close)    -> event

let convert_call_to_event (cmd:io_cmds) (arg:io_args cmd) (r:io_resm cmd) : event =
  match cmd with
  | Openfile -> EOpenfile arg r
  | Read -> ERead arg r
  | Close -> EClose arg r

type trace = list event

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

unfold let io_pres (cmd:io_cmds) (arg:io_args cmd) (h:trace) : Type0 =
  match cmd with
  | Openfile -> True
  | Read -> is_open arg h
  | Close -> is_open arg h

unfold let io_wps (cmd:io_cmds) (arg:io_args cmd) (p:trace -> io_resm cmd -> Type0) (h:trace) : Type0 =
  match cmd with
  | _ -> io_pres cmd arg h /\ (forall r. p [convert_call_to_event cmd arg r] r)

type io a = free io_cmds io_sig a
let io_return (x:'a) : io 'a =
  free_return io_cmds io_sig 'a x

let io_bind (#a:Type) (#b:Type) l k : io b =
  free_bind io_cmds io_sig a b l k

let io_call (cmd:io_cmds) (arg:io_args cmd) : io (io_resm cmd) =
  Call cmd arg Return
