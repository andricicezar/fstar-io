module IIO.Primitives

open FStar.Tactics
open ExtraTactics
open FStar.Tactics.Typeclasses

open Common
open IO.Sig
open IO
open IIO
open TC.Checkable
open TC.Trivialize

val dynamic_cmd :
  (cmd : io_cmds) ->
  (d1 : checkable2 (io_pre cmd)) ->
  (arg : io_sig.args cmd) ->
  IIOwp (resexn (io_sig.res cmd arg)) 
    (fun p h ->
      (forall (r:resexn (io_sig.res cmd arg)) lt.
        (match r with
         | Inr Contract_failure -> ~(d1.check2 arg h) /\ lt == []
         | Inl r' -> d1.check2 arg h /\ lt == [convert_call_to_event cmd arg r']
         | _ -> False) ==> p lt r))
let dynamic_cmd (cmd:io_cmds) d1 = 
  trivialize 
    #_ 
    #(trivializeable_IOwp
       (io_sig.args cmd)
       (io_resm cmd)
       (io_pre cmd)
       #d1
       (fun (argz:io_sig.args cmd) h r lt -> lt == [convert_call_to_event cmd argz r]))
  (static_cmd cmd)
