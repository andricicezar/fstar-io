module Trace

(**
  Signature of the operations, and the definition of events
  and well formed traecs.

  The file should be usable both to define the Dijkstra Monad
  and the semantics of the Syntactic Language. **)

include BaseTypes

noeq
type sig (op:Type u#a) = {
  args : op -> Type u#a;
  res : (cmd:op) -> (args cmd) -> Type u#a;
}

type io_ops = | ORead | OWrite | OOpen | OClose

unfold let io_args (op:io_ops) : Type =
  match op with
  | ORead -> file_descr
  | OWrite -> file_descr * bool
  | OOpen -> bool
  | OClose -> file_descr

unfold let io_res (op:io_ops) (_:io_args op) : Type =
  match op with
  | ORead -> resexn bool
  | OWrite -> resexn unit
  | OOpen -> resexn file_descr
  | OClose -> resexn unit

type event =
| EvRead  : args:io_args ORead -> io_res ORead args -> event
| EvWrite : args:io_args OWrite -> io_res OWrite args -> event
| EvOpen  : args:io_args OOpen -> io_res OOpen args -> event
| EvClose : args:io_args OClose -> io_res OClose args -> event

let op_to_ev (op:io_ops) (args:io_args op) (res:io_res op args) : event =
  match op with
  | ORead -> EvRead args res
  | OWrite -> EvWrite args res
  | OOpen -> EvOpen args res
  | OClose -> EvClose args res

let destruct_ev (ev:event) : op:io_ops & args:io_args op & io_res op args =
  match ev with
  | EvRead a r -> (| ORead, a, r |)
  | EvWrite a r -> (| OWrite, a, r |)
  | EvOpen a r -> (| OOpen, a, r |)
  | EvClose a r -> (| OClose, a, r |)

let trace = list event

type history = trace (** a history is a trace kept backwards **)

let rec last_fd (h:history) : Tot file_descr
  (decreases h) =
  match h with
  | [] -> 0
  | (EvOpen arg (Inl fd)) :: _ -> fd
  | _ :: tl -> last_fd tl

let fresh_fd (h:history) : file_descr = (last_fd h) + 1

(** TODO: get rid of pres **)
unfold
let io_pre (h:trace) (op:io_ops) (arg:io_args op) : Type0 =
  match op with
  | ORead -> True
  | OWrite -> True
  | OOpen -> True
  | OClose -> True

unfold
let io_post (h:trace) (op:io_ops) (arg:io_args op) (res:io_res op arg) : Type0 =
  match op with
  | ORead -> True
  | OWrite -> True
  | OOpen -> True // Cezar: no post here?
  | OClose -> True

unfold
let test_event (h:trace) (ev:event) =
  match ev with
  | EvRead v r -> io_pre h ORead v /\ io_post h ORead v r
  | EvWrite v r -> io_pre h OWrite v /\ io_post h OWrite v r
  | EvOpen v r -> io_post h OOpen v r
  | EvClose v r -> io_pre h OClose v /\ io_post h OClose v r

let rec well_formed_local_trace (h:trace) (lt:trace) : Tot Type0 (decreases lt) =
  match lt with
  | [] -> True
  | ev :: tl -> test_event h ev /\ well_formed_local_trace (ev::h) tl

type event_h (t:trace) = (ev:event{test_event t ev})

type local_trace (h:trace) =
  lt:trace{well_formed_local_trace h lt}

open FStar.List.Tot

let (++) (h:history) (lt:local_trace h) : history =
  List.rev lt @ h

let trans_well_formed_local_trace (h:trace) (lt:local_trace h) (lt1:local_trace (h++lt)) :
  Lemma (well_formed_local_trace h (lt @ lt1))
  [SMTPat (well_formed_local_trace h (lt @ lt1))] =
    admit ()

let trans_well_formed_local_trace_event (h:trace) (ev:event_h h) (lt:local_trace (ev::h)) :
  Lemma (well_formed_local_trace h ([ev] @ lt))
  [SMTPat (well_formed_local_trace h ([ev] @ lt))] =
    admit ()

let singleton_event_well_formed_local_trace (h:trace) (ev:event_h h) :
  Lemma (well_formed_local_trace h [ev])
  [SMTPat (well_formed_local_trace h [ev])] =
    admit ()

let trans_history (h:history) (lt:local_trace h) (lt':local_trace (h++lt)) :
  Lemma (((h++lt)++lt') == (h++(lt @ lt')))
  [SMTPat (h++(lt @ lt'))] =
    admit ()

let trans_history' (h:history) (lt:local_trace h) (lt':local_trace (h++lt)) :
  Lemma (((h++lt)++lt') == (h++(lt @ lt')))
  [SMTPat ((h++lt)++lt')] =
    admit ()

let associative_history #h (lt1:local_trace h) (lt2:local_trace (h++lt1)) (lt3:local_trace ((h++lt1)++lt2)) :
  Lemma ((lt1 @ (lt2 @ lt3)) == ((lt1 @ lt2) @ lt3)) =
    admit ()

let as_lt (#h:history) (oev:option (event_h h)) : local_trace h =
  if Some? oev then [Some?.v oev] else []
