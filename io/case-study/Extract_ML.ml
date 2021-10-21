open Common
open FStar_Pervasives
open Types

let global_trace : Free_IO.trace ref = ref []

let ml_gettrace () : Free_IO.trace =
  !global_trace

let update_trace (cmd:Free_IO.io_cmds) (argz:Obj.t) (rez:Obj.t maybe) : Obj.t maybe =
  global_trace := (Free_IO.convert_call_to_event cmd argz rez) :: !global_trace;
  rez

let ml_call_cmd (cmd:Free_IO.io_cmds) =
  match cmd with
  | Free_IO.Openfile -> Obj.magic (Obj.repr Unix_Star.openfile)
  | Free_IO.Read -> Obj.magic (Obj.repr Unix_Star.read)
  | Free_IO.Write -> Obj.magic (Obj.repr Unix_Star.write)
  | Free_IO.Close -> Obj.magic (Obj.repr Unix_Star.close)
  | Free_IO.Socket -> Obj.magic (Obj.repr Unix_Star.socket)
  | Free_IO.Setsockopt ->
      Obj.magic (Obj.repr Unix_Star.setsockopt)
  | Free_IO.Bind -> Obj.magic (Obj.repr Unix_Star.bind)
  | Free_IO.SetNonblock ->
      Obj.magic (Obj.repr Unix_Star.setnonblock)
  | Free_IO.Listen -> Obj.magic (Obj.repr Unix_Star.listen)
  | Free_IO.Accept -> Obj.magic (Obj.repr Unix_Star.accept)
  | Free_IO.Select -> Obj.magic (Obj.repr Unix_Star.select)

let ml_io_cmd (cmd:Free_IO.io_cmds) (argz:Obj.t) : Obj.t maybe =
  try
    let x = ml_call_cmd cmd argz in
    update_trace cmd argz (Inl x)
  with err ->
    update_trace cmd argz (Inr err)
