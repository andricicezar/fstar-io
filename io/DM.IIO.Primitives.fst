module DM.IIO.Primitives

open FStar.Tactics
open ExtraTactics
open DM.IIO.Tactics

open Common
open Free
open Free.IO
open DM.IO
open DM.IIO
open Hist

let _IIOwp_as_IIO
  (pre:'a -> trace -> bool)
  (post:'a -> trace -> (m:'b) -> trace -> Type0)
  (f:(x:'a ->
    IIOwp 'b (fun h p -> pre x h /\ (forall r lt. post x h r lt ==> p r lt))))
  (x:'a) :
  IIOwp (maybe 'b) (fun h p ->
    (~(pre x h) ==>  p (Inr Contract_failure) []) /\
    (pre x h ==>  (forall r lt. post x h r lt ==>  p (Inl r) lt)))
    by (iio_tactic ()) =
  let h = get_trace () in
  if pre x h then (Inl (f x))
  else (Inr Contract_failure)

let _IIOwp_as_IIO_2
  (pre:'a -> 'b -> trace -> bool)
  (post:'a -> 'b -> trace -> (m:'c) -> trace -> Type0)
  (f:(x:'a -> y:'b ->
    IIOwp 'c (fun h p -> pre x y h /\ (forall r lt. post x y h r lt ==> p r lt))))
  (x:'a) (y:'b) :
  IIOwp (maybe 'c) (fun h p ->
    (~(pre x y h) ==> p (Inr Contract_failure) []) /\
    (pre x y h ==> (forall r lt. post x y h r lt ==> p (Inl r) lt)))
    by (iio_tactic ()) =
  let h = get_trace () in
  if pre x y h then Inl (f x y)
  else Inr Contract_failure

let _IIOwp_as_IIO_3
  (pre:'a -> 'b -> 'c -> trace -> bool)
  (post:'a -> 'b -> 'c -> trace -> 'd -> trace -> Type0)
  (f:(x:'a -> y:'b -> z:'c ->
    IIOwp 'd (fun h p -> pre x y z h /\ (forall r lt. post x y z h r lt ==> p r lt))))
  (x:'a) (y:'b) (z:'c) :
  IIOwp (maybe 'd) (fun h p ->
    (~(pre x y z h) ==> p (Inr Contract_failure) []) /\
    (pre x y z h ==> (forall r lt. post x y z h r lt ==> p (Inl r) lt)))
    by (iio_tactic ()) =
  let h = get_trace () in
  if pre x y z h then Inl (f x y z)
  else Inr Contract_failure

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
let dynamic_cmd (cmd:io_cmds) = _IIOwp_as_IIO_2 #monitorable_prop #(args cmd)
  (fun pi (argz:args cmd) h -> pi h (| cmd, argz |))
  (fun pi (argz:args cmd) h r lt ->
      lt == [convert_call_to_event cmd argz r] /\
      enforced_locally pi h lt)
  (static_cmd cmd)
