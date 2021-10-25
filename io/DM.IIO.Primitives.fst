module DM.IIO.Primitives

open FStar.Tactics
open ExtraTactics
open DM.IIO.Tactics
open FStar.Tactics.Typeclasses

open Common
open Free.IO
open DM.IO
open DM.IIO
open TC.Trivialize.IIOwp

val dynamic_cmd :
  (cmd : io_cmds) ->
  (pi : monitorable_prop) ->
  (arg : args cmd) ->
  IIOwp (maybe (io_resm cmd)) (fun h p ->
    (forall (r:maybe (io_resm cmd)) lt.
      ((match r with
      | Inr Contract_failure -> lt == []
      | Inl r' -> lt == [convert_call_to_event cmd arg r']
      | _ -> False) /\
      enforced_locally pi h lt) ==> p r lt))
let dynamic_cmd (cmd:io_cmds) = 
  trivialize 
    #_ 
    #(trivializeable_IIOwp_2 monitorable_prop (args cmd) _
      (fun pi argz h -> pi h (| cmd, argz |))
      (fun pi argz h r lt -> 
        lt == [convert_call_to_event cmd argz r] /\ enforced_locally pi h lt))
  (static_cmd cmd)
