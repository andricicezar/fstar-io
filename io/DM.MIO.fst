module DM.MIO

open Free.IO
open Free.IO.Call
open DM.IO

effect MIO
  (a:Type) =
  IOwp a (fun _ p -> forall res le. p res le)

let unsafe_cmd
  (cmd : io_cmds)
  (argz : io_args cmd) :
  MIO (io_resm cmd) =
    IOwp?.reflect(fun _ _ -> io_call cmd argz)
