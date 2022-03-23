module DM.IIO.Primitives

open FStar.Tactics
open ExtraTactics
open FStar.Tactics.Typeclasses

open Common
open IO.Sig
open DM.IO
open DM.IIO
open TC.Checkable
open TC.Trivialize.IIOwp

val dynamic_cmd :
  (cmd : io_cmds) ->
  (d1 : checkable2 (io_pre cmd)) ->
  (arg : io_sig.args cmd) ->
  IIOwp (maybe (io_resm cmd)) 
    (fun p h ->
      (forall (r:maybe (io_sig.res cmd arg)) lt.
        (match r with
         | Inr Contract_failure -> lt == []
         | Inl r' -> lt == [convert_call_to_event cmd arg r']
         | _ -> False) ==> p lt r))
let dynamic_cmd (cmd:io_cmds) d1 = 
  trivialize 
    #_ 
    #(trivializeable_IIOwp
       (io_sig.args cmd)
       (io_resm cmd)
       (io_pre cmd)
       #d1
       (fun (argz:io_sig.args cmd) h r lt -> lt == [convert_call_to_event cmd argz r]))
  (static_cmd cmd)
