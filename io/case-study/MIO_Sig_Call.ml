open Prims
open Common
open FStar_Pervasives
open MIO_Sig

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

let (mio_call : inst_cmds -> Obj.t -> Obj.t iio) =
  fun cmd -> fun argz ->
  match cmd with
  | GetTrace -> 
    print_string "Getting trace...\n";
    flush stdout;
    mio_return (Obj.magic (Monitor.get_trace ()))
