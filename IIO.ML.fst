module IIO.ML

open FStar.All
open Common
open IO.Free

assume val ml_gettrace : args GetTrace -> ML (res GetTrace)
assume val ml_openfile : args Openfile -> ML (res Openfile)
assume val ml_read : args Read -> ML (res Read)
assume val ml_close : args Close -> ML (res Close)

val ml_io_all : (cmd:cmds) -> args cmd -> ML (res cmd)
let ml_io_all cmd args =
  match cmd with
  | GetTrace -> ml_gettrace args
  | Openfile -> ml_openfile args
  | Read -> ml_read args
  | Close -> ml_close args


val ml_io_execute : (cmd:cmds) -> args cmd -> ML (resm cmd)
let ml_io_execute cmd argz =
  try_with
    (fun _ -> Inl (ml_io_all cmd argz))
    (fun err -> Inr err)
