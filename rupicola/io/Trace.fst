module Trace

(**
  Signature of the operations, and the definition of events
  and well formed traecs.

  The file should be usable both to define the Dijkstra Monad
  and the semantics of the Syntactic Language. **)

noeq
type sig (op:Type u#a) = {
  args : op -> Type u#a;
  res : (cmd:op) -> (args cmd) -> Type u#a;
}

type io_ops = | ORead | OWrite

unfold let io_args (op:io_ops) : Type =
  match op with
  | ORead -> unit
  | OWrite -> bool

unfold let io_res (op:io_ops) (_:io_args op) : Type =
  match op with
  | ORead -> option bool
  | OWrite -> option unit

type event =
| EvRead  : args:io_args ORead -> io_res ORead args -> event
| EvWrite : args:io_args OWrite -> io_res OWrite args -> event

let op_to_ev (op:io_ops) (args:io_args op) (res:io_res op args) : event =
  match op with
  | ORead -> EvRead args res
  | OWrite -> EvWrite args res

let destruct_ev (ev:event) : op:io_ops & args:io_args op & io_res op args =
  match ev with
  | EvRead a r -> (| ORead, a, r |)
  | EvWrite a r -> (| OWrite, a, r |)

let trace = list event

unfold
let io_pre (h:trace) (op:io_ops) (arg:io_args op) : Type0 =
  match op with
  | ORead -> True
  | OWrite -> True

unfold
let io_post (h:trace) (op:io_ops) (arg:io_args op) (res:io_res op arg) : Type0 =
  match op with
  | ORead -> True
  | OWrite -> True

unfold
let test_event (h:trace) (ev:event) =
  match ev with
  | EvRead v r -> io_pre h ORead v /\ io_post h ORead v r
  | EvWrite v r -> io_pre h OWrite v /\ io_post h OWrite v r

let rec well_formed_local_trace (h:trace) (lt:trace) : Tot Type0 (decreases lt) =
  match lt with
  | [] -> True
  | ev :: tl -> test_event h ev /\ well_formed_local_trace (ev::h) tl

type history = trace (** a history is a trace kept backwards **)

type local_trace (h:trace) =
  lt:trace{well_formed_local_trace h lt}

open FStar.List.Tot

let (++) (h:history) (lt:local_trace h) : history =
  List.rev lt @ h

let trans_well_formed_local_trace (h:trace) (lt:local_trace h) (lt1:local_trace (h++lt)) :
  Lemma (well_formed_local_trace h (lt @ lt1))
  [SMTPat (well_formed_local_trace h (lt @ lt1))] =
    admit ()
