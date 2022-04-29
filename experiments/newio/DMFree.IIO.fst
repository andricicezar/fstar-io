module DMFree.IIO

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Hist
open DMFree
include Free.Sig

let iio_wps (cmd:iio_cmds) (arg:iio_sig.args cmd) : hist #event (iio_sig.res cmd arg) =
  fun p (h:trace) ->
    match cmd with
    | GetTrace -> p [] h
    | _ -> 
      io_pre cmd arg h /\ (forall (r:iio_sig.res cmd arg). p [convert_call_to_event cmd arg r] r)

let theta #a = theta #a #iio_cmds #iio_sig #event iio_wps
  
let dm = dm iio_cmds iio_sig event iio_wps
let dm_return = dm_return iio_cmds iio_sig event iio_wps
let dm_bind = dm_bind iio_cmds iio_sig event iio_wps
let dm_subcomp = dm_subcomp iio_cmds iio_sig event iio_wps
let dm_if_then_else = dm_if_then_else iio_cmds iio_sig event iio_wps
let lift_pure_dm = lift_pure_dm iio_cmds iio_sig event iio_wps

total
reifiable
reflectable
effect {
  IOwp (a:Type) (wp : hist #event a) 
  with {
       repr       = dm
     ; return     = dm_return
     ; bind       = dm_bind 
     ; subcomp    = dm_subcomp
     ; if_then_else = dm_if_then_else
     }
}

effect IO
  (a:Type)
  (pre : trace -> Type0)
  (post : trace -> trace -> a -> Type0) =
  IOwp a 
    (fun (p:hist_post a) (h:trace) -> pre h /\ (forall lt r. post h lt r ==> p lt r)) 

sub_effect PURE ~> IOwp = lift_pure_dm
  
assume val p : prop
assume val p' : prop
assume val pure_lemma (_:unit) : Lemma p
assume val some_f (_:squash p) : IO unit (fun _ -> True) (fun _ _ _ -> True)
assume val some_f' : unit -> IO unit (requires (fun _ -> p)) (ensures fun _ _ _ -> p')

let test () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  pure_lemma ();
  some_f ()

let test'' () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  pure_lemma ();
  some_f ();
  some_f' ();
  assert p'

let static_cmd
  (cmd : io_cmds)
  (arg : iio_sig.args cmd) :
  IO (iio_sig.res cmd arg)
    (requires (fun h -> io_pre cmd arg h))
    (ensures (fun h lt r ->
        lt == [convert_call_to_event cmd arg r])) =
  IOwp?.reflect (iio_call cmd arg)

let testStatic3 (fd:file_descr) : IO unit (fun h -> is_open fd h) (fun h lt r -> ~(is_open fd (List.rev lt @ h))) =
  let _ = static_cmd Close fd in
  ()

let testStatic2 () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  let fd = static_cmd Openfile "../Makefile" in
  if Some? fd then begin (** test if Openfile was successful **)
    let msg = static_cmd Read (Some?.v fd) in
    let _ = static_cmd Close (Some?.v fd) in
    ()
  end else ()