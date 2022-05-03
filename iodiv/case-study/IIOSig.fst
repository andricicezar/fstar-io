(** (Instrumented) I/O signature *)

module IIOSig

open DivFree
include Types

type lfds = list file_descr

type iio_act =
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

assume val file_descr : eqtype

let not_GetTrace x =
  match x with
  | GetTrace -> false
  | _ -> true

type io_act = ac : iio_act { not_GetTrace ac }

noeq
type event =
| EOpenfile : string * (list open_flag) * zfile_perm -> either (file_descr) exn -> event
| ERead : file_descr * UInt8.t -> either (Bytes.bytes * UInt8.t) exn -> event
| EWrite : file_descr * Bytes.bytes -> either (unit) exn -> event
| EClose : file_descr -> either (unit) exn -> event
| ESocket : unit -> either (file_descr) exn -> event
| ESetsockopt : file_descr * socket_bool_option * bool -> either (unit) exn -> event
| EBind : file_descr * string * UInt8.t -> either (unit) exn -> event
| ESetNonblock : file_descr -> either (unit) exn -> event
| EListen : file_descr * UInt8.t -> either (unit) exn -> event
| EAccept : file_descr -> either (file_descr) exn -> event
| ESelect : lfds * lfds * lfds * UInt8.t -> either (lfds * lfds * lfds ) exn -> event

let trace = list event
let history = list event // head: latest event

unfold
let iio_arg ac =
  match ac with
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
  | GetTrace -> unit

unfold
let iio_res #ac (x : iio_arg ac) =
  match ac with
  | Openfile -> either (file_descr) exn
  | Read -> either (Bytes.bytes * UInt8.t) exn
  | Write -> either (unit) exn
  | Close -> either (unit) exn
  | Socket -> either (file_descr) exn
  | Setsockopt -> either (unit) exn
  | Bind -> either (unit) exn
  | SetNonblock -> either (unit) exn
  | Listen -> either (unit) exn
  | Accept -> either (file_descr) exn
  | Select -> either (lfds * lfds * lfds ) exn
  | GetTrace -> history

let io_sig : signature = {
  act = io_act ;
  arg = iio_arg ;
  res = iio_res
}

let iio_sig : signature = {
  act = iio_act ;
  arg = iio_arg ;
  res = iio_res
}

let rec is_open (fd : file_descr) (hist : history) : bool =
  match hist with
  | [] -> false
  | EClose fd' _ :: hist' ->
    if fd = fd'
    then false
    else is_open fd hist'
  | EOpenfile s fd' :: hist' ->
    if Inl? fd' && fd = Inl?.v fd'
    then true
    else is_open fd hist'
  | e :: hist' -> is_open fd hist'
