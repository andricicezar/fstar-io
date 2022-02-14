module DMFree.IO

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Hist
open DMFree
include Free.Sig

unfold let io_wps (cmd:io_cmds) (arg:io_args cmd) : hist #event (io_resm cmd) = fun p h ->
  match cmd with
 // | GetTrace -> p [] h
  | _ -> io_pre cmd arg h /\ (forall r. p [convert_call_to_event cmd arg r] r)

let theta #a = theta #a #io_cmds #io_sig #event io_wps
  
let dm = dm io_cmds io_sig event io_wps
let dm_return = dm_return io_cmds io_sig event io_wps
let dm_bind = dm_bind io_cmds io_sig event io_wps
let dm_subcomp = dm_subcomp io_cmds io_sig event io_wps
let dm_if_then_else = dm_if_then_else io_cmds io_sig event io_wps
