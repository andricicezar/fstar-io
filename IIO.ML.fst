module IIO.ML

open FStar.All
open Common
open IO.Free

assume val ml_gettrace : args GetTrace -> ML (res GetTrace)
assume val ml_openfile : args Openfile -> ML (io_res Openfile)
assume val ml_read : args Read -> ML (io_res Read)
assume val ml_close : args Close -> ML (io_res Close)

val ml_io_cmds : (cmd:io_cmds) -> args cmd -> ML (io_res cmd)
let ml_io_cmds cmd args =
  match cmd with
  | Openfile -> ml_openfile args
  | Read -> ml_read args
  | Close -> ml_close args

val ml_io_all : (cmd:io_cmds) -> args cmd -> ML (io_resm cmd)
let ml_io_all cmd args =
  try_with
    (fun _ -> (Inl (ml_io_cmds cmd args)) <: io_resm cmd)
    (fun err -> (Inr err) <: io_resm cmd)


val ml_io_execute : (cmd:cmds) -> args cmd -> ML (res cmd)
let ml_io_execute cmd argz =
  match cmd with
  | GetTrace -> ml_gettrace argz
  | _ -> ml_io_all cmd argz
