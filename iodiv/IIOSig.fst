(** (Instrumented) I/O signature *)

module IIOSig

open DivFree

type iio_act =
| OpenFile
| Read
| Close
| GetTrace

assume val file_descr : eqtype

let not_GetTrace x =
  match x with
  | GetTrace -> false
  | _ -> true

type io_act = ac : iio_act { not_GetTrace ac }

noeq
type event =
| EOpenFile : string -> file_descr -> event
| ERead     : file_descr -> string -> event
| EClose    : file_descr -> event

let trace = list event
let history = list event // head: latest event

unfold
let iio_arg ac =
  match ac with
  | OpenFile -> string
  | Read -> file_descr
  | Close -> file_descr
  | GetTrace -> unit

unfold
let iio_res #ac (x : iio_arg ac) =
  match ac with
  | OpenFile -> file_descr
  | Read -> string
  | Close -> unit
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
  | EClose fd' :: hist' ->
    if fd = fd'
    then false
    else is_open fd hist'
  | EOpenFile s fd' :: hist' ->
    if fd = fd'
    then true
    else is_open fd hist'
  | e :: hist' -> is_open fd hist'
