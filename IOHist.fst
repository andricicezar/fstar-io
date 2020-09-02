module IOHist

open FStar.Tactics
open ExtraTactics

open Common
open IO.Free

noeq
type io_event =
    | EOpenfile : args Openfile -> resm Openfile -> io_event
    | ERead : args Read -> resm Read -> io_event
    | EClose : args Close -> resm Close -> io_event

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

type set_of_traces = events_trace -> Type0

val include_in : set_of_traces -> set_of_traces -> Type0
let include_in s1 s2 = forall t. s1 t ==>  s2 t

let rec behavior #a
  (m : io a) : set_of_traces =
  match m with
  | Return x -> fun t -> t == []
  | Throw err -> fun t -> t == []
  | Cont t -> begin
    match t with
    | Call cmd args fnc -> (fun t' -> 
      (exists res t. (
         FStar.WellFounded.axiom1 fnc res;
         (behavior (fnc res) t) /\
         t' == ((convert_call_to_event cmd args res)::t))))
  end

let l : events_trace = []
#set-options "--max_fuel 20 --max_ifuel 20"
let _ = assert ((behavior (Cont (Call Openfile "asdf" (fun x -> Return x))) [EOpenfile "asdf" (Inl 7)])) by (
  unfold_def (`behavior);
  unfold_def (`convert_call_to_event);
  witness (`(Inl 7));
  witness (`l);
  dump "h")

let code1 : io (res Close) = 
  io_bind _ _
    (io_openfile "asdf")
    io_close


exception OneExc
let _ = assert (behavior code1 [EOpenfile "asdf" (Inr OneExc)]) by (
  unfold_def (`code1);
  unfold_def (`behavior);
  unfold_def (`convert_call_to_event);
  witness (`(Inr OneExc));
  witness (`l);
  dump "h")


// let _ = assert (include_in [EOpenfile "asdf" (Inl 7); EClose 8 (Inl ())] (behavior code1)) by (
//   unfold_def (`code1);
//   unfold_def (`behavior);
//   unfold_def (`include_in);
//   unfold_def (`convert_call_to_event);
//   witness (`(Inl 7));
//   witness (`([EClose 8 (Inl ())]));
//   // witness (`(Inl ()));
//   // witness (`l);
//   dump "h")

let rec behavior' #a
  (m : io a)
  (p : set_of_traces) : Type0 =
  match m with
  | Return x -> p []
  | Throw err ->  p []
  | Cont t -> begin
    match t with
    | Call cmd args fnc -> exists res. (
         FStar.WellFounded.axiom1 fnc res;
      (behavior' (fnc res) (fun t' -> p ((convert_call_to_event cmd args res)::t'))))
      // (exists res t. (
      //    FStar.WellFounded.axiom1 fnc res;
      //    (p ((convert_call_to_event cmd args res)::t))
      //         /\ (include_in t (behavior' (fnc res))))))
  end

#set-options "--max_fuel 20 --max_ifuel 20"
let _ = assert (behavior' (Cont (Call Openfile "asdf" (fun x -> Return x))) (fun trace -> trace == [EOpenfile "asdf" (Inl 7)])) by (
  unfold_def (`behavior');
  unfold_def (`convert_call_to_event);
  witness (`(Inl 7));
  explode ();
  dump "h")

// let _ = assert (behavior' code1 (fun trace -> trace == [EOpenfile "asdf" (Inr OneExc)])) by (
//   unfold_def (`code1);
//   unfold_def (`behavior');
//   unfold_def (`convert_call_to_event);
//   witness (`(Inr OneExc));
//   witness (`l);
//   compute ();
//   dump "h")

(* total *)
(* reifiable *)
(* reflectable *)
(* new_effect { *)
(*   IOHist : a:Type -> Effect *)
(*   with  *)
(*        repr       = io *)
(*      ; return     = io_return *)
(*      ; bind       = io_bind *)

(*      ; wp_type    = iohist_wpty *)
(*      ; return_wp  = iohist_return_wp *)
(*      ; bind_wp    = iohist_bind_wp *)

(*      ; interp     = iohist_interpretation *)
(* } *)
