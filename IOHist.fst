module IOHist

open FStar.Tactics
open ExtraTactics

open Common
open IO.Free

noeq
type io_event =
    | EOpenfile : a:args Openfile -> (r:resm Openfile) -> io_event
    | ERead : a:args Read -> (r:resm Read) -> io_event
    | EClose : a:args Close -> (r:resm Close) -> io_event

type events_trace = list io_event

let iohist_post a = maybe a -> events_trace -> Type0  // local_events (from old to new)
let iohist_wpty a = events_trace -> iohist_post a -> Type0  // past_events (from new to old; reversed compared with local_events)

unfold
let iohist_return_wp (a:Type) (x:a) : iohist_wpty a =
  fun past_events p -> p (Inl x) []

unfold
let iohist_bind_wp (_ : range) (a:Type) (b:Type) (w : iohist_wpty a) (kw : a -> iohist_wpty b) : iohist_wpty b =
  fun past_events p -> 
    w past_events 
      (fun result local_events -> 
        match result with
        | Inl result -> (
            kw result
            ((List.rev local_events) @ past_events) 
            (fun result' local_events' -> 
                p result' (local_events @ local_events')))
        | Inr err -> p (Inr err) local_events)

unfold let gen_post #a (post:iohist_post a) (event:io_event) = 
  fun x local_events -> post x (event :: local_events)

unfold let convert_call_to_event (cmd:io_cmds) (args:args cmd) (res:resm cmd) =
  match cmd with
  | Openfile -> EOpenfile args res
  | Read -> ERead args res
  | Close -> EClose args res

let rec iohist_interpretation #a
  (m : io a) 
  (past_events : events_trace)
  (p : iohist_post a) : Type0 = 
  match m with
  | Return x -> p (Inl x) []
  | Throw err -> p (Inr err) []
  | Cont t -> begin
    match t with
    | Call cmd args fnc -> (forall res. (
      FStar.WellFounded.axiom1 fnc res;
      let event : io_event = convert_call_to_event cmd args res in
      iohist_interpretation (fnc res) (event :: past_events) (gen_post p event)))
  end
