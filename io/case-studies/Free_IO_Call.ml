open Prims
open Common
open FStar_Pervasives
open Free_IO

let ml_call (cmd:io_cmds) =
  match cmd with
  | Openfile -> Obj.magic (Obj.repr Unix_Star.openfile)
  | Read -> Obj.magic (Obj.repr Unix_Star.read)
  | Write -> Obj.magic (Obj.repr Unix_Star.write)
  | Close -> Obj.magic (Obj.repr Unix_Star.close)
  | Socket -> Obj.magic (Obj.repr Unix_Star.socket)
  | Setsockopt ->
      Obj.magic (Obj.repr Unix_Star.setsockopt)
  | Bind -> Obj.magic (Obj.repr Unix_Star.bind)
  | SetNonblock ->
      Obj.magic (Obj.repr Unix_Star.setnonblock)
  | Listen -> Obj.magic (Obj.repr Unix_Star.listen)
  | Accept -> Obj.magic (Obj.repr Unix_Star.accept)
  | Select -> Obj.magic (Obj.repr Unix_Star.select)

let io_call (cmd:io_cmds) argz =
  try
    let rez = ml_call cmd argz in
    Monitor.update_trace (Obj.magic cmd) (Obj.magic argz) (Obj.magic (Inl rez)); 
    io_return (Inl rez)
  with err ->
    Monitor.update_trace (Obj.magic cmd) (Obj.magic argz) (Obj.magic (Inr err));
    io_return (Inr err)

let (iio_call : inst_cmds -> Obj.t -> Obj.t iio) =
  fun cmd -> fun argz ->
  match cmd with
  | GetTrace -> iio_return (Obj.magic (Monitor.get_trace ()))
