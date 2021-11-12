open Prims
open Common
open FStar_Pervasives
open Free_IO

let global_trace : trace ref = ref []

let ml_gettrace () : trace =
  !global_trace

let update_trace (cmd:io_cmds) (argz:Obj.t) (rez:Obj.t maybe) : Obj.t maybe =
  global_trace := (convert_call_to_event cmd argz rez) :: !global_trace;
  print_int (List.length !global_trace);
  print_newline ();
  flush stdout;
  rez

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
    let x = ml_call cmd argz in
    io_return (Obj.magic (update_trace cmd argz (Inl x)))
  with err ->
    io_return (Obj.magic (update_trace cmd argz (Inr err)))

let (iio_call : inst_cmds -> Obj.t -> Obj.t iio) =
  fun cmd -> fun argz ->
  match cmd with
  | GetTrace -> iio_return (Obj.magic (ml_gettrace ()))


