module IO.Free

open Common
include Sys.Free

type io_cmds = | Openfile | Read | Close

let io_cmd_sig : cmd_sig io_cmds = { 
  args = (function
    | Openfile -> string
    | Read -> file_descr
    | Close -> file_descr) ;
  res = (function
    | Openfile -> file_descr
    | Read -> string
    | Close -> unit)
}

unfold let args (op:io_cmds) = io_cmd_sig.args op
unfold let res (op:io_cmds) = io_cmd_sig.res op
unfold let resm (op:io_cmds) = maybe (io_cmd_sig.res op)
  
type io = sys io_cmds io_cmd_sig

let io_return (a:Type) (x:a) = sys_return io_cmds io_cmd_sig a x
let io_throw (a:Type) (x:exn) = sys_throw io_cmds io_cmd_sig a x
let io_bind (a:Type) (b:Type) l k = sys_bind io_cmds io_cmd_sig a b l k

val io_openfile : args Openfile -> io (res Openfile) 
let io_openfile fnm =
  sys_perform (Call Openfile (fnm) (fun fd -> fd))

val io_read : args Read -> io (res Read)
let io_read fd =
  sys_perform (Call Read (fd) (fun msg -> msg))

val io_close : args Close -> io (res Close)
let io_close fd =
  sys_perform (Call Close (fd) (fun fd -> fd))

val io_all : (cmd:io_cmds) -> args cmd -> io (res cmd)
let io_all cmd args =
  match cmd with
  | Openfile -> io_openfile args
  | Read -> io_read args
  | Close -> io_close args
