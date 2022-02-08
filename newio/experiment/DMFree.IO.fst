module DMFree.IO

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Hist
open DMFree

type cmds = | Openfile | Read | Close | GetTrace

assume val file_descr : eqtype

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

let io_resm (cmd:io_cmds) = option (io_res cmd)

let io_sig : op_sig io_cmds = { args = io_args; res = io_resm; }

noeq
type event =
  | EOpenfile : a:io_args Openfile -> (r:io_resm Openfile) -> event
  | ERead     : a:io_args Read     -> (r:io_resm Read)     -> event
  | EClose    : a:io_args Close    -> (r:io_resm Close)    -> event

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

unfold let io_pre (cmd:io_cmds) (arg:io_args cmd) (h:trace) : Type0 =
  match cmd with
  | Openfile -> True
  | Read -> is_open arg h
  | Close -> is_open arg h
  | GetTrace -> True

type action_type = (cmd : io_cmds) & (io_args cmd)

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

let destruct_event (e:event) : ( cmd:io_cmds & io_args cmd & io_resm cmd )  =
  match e with
  | EOpenfile arg res -> (| Openfile, arg, res |)
  | ERead arg res -> (| Read, arg, res |)
  | EClose arg res -> (| Close, arg, res |)

type io a = free io_cmds io_sig a
let io_return (x:'a) : io 'a =
  free_return io_cmds io_sig 'a x

let io_bind (#a:Type) (#b:Type) l k : io b =
  free_bind io_cmds io_sig a b l k

let io_call (cmd:io_cmds) (arg:io_args cmd) : io (io_resm cmd) =
  Call cmd arg Return

unfold let io_wps (cmd:io_cmds) (arg:io_args cmd) : hist #event (io_resm cmd) = fun p h ->
  match cmd with
 // | GetTrace -> p [] h
  | _ -> io_pre cmd arg h /\ (forall r. p [convert_call_to_event cmd arg r] r)

let theta #a = theta #a #io_cmds #io_sig #event io_wps
  
let dm = dm io_cmds io_sig event io_wps
let dm_return = dm_return io_cmds io_sig event io_wps
let dm_bind = dm_bind io_cmds io_sig event io_wps
let dm_subcomp = dm_subcomp io_cmds io_sig event io_wps
let dm_if_then_else = dm_if_then_else io_cmds io_sig event io_wps
