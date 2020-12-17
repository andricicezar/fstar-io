module IO.Free

open Common
include Free

type cmds = | Openfile | Read | Close | GetTrace

// Observable actions
type io_cmds = x:cmds{x = Openfile || x = Read || x = Close}

let io_sig : cmd_sig io_cmds = { 
  args = (fun (x:io_cmds) -> match x with
    | Openfile -> string 
    | Read -> file_descr
    | Close -> file_descr);
  res = (fun (x:io_cmds) -> match x with
    | Openfile -> file_descr
    | Read -> string
    | Close -> unit)
}

(** It is obvious that the primitives have no reason to throw 
`Contract_failure`, because they do not enforce any policy. 
In practice, a primitive can throw any error, but I think
this is an assumption we can make to have more precise specification.
`Contract_failure` is an exception defined by us in `Common.fst` **)
unfold let io_args (op:io_cmds) : Type = io_sig.args op
unfold let io_res (op:io_cmds) = io_sig.res op
unfold let io_resm (op:io_cmds) = r:(maybe (io_sig.res op)){~(Inr? r /\ Inr?.v r == Contract_failure)}

noeq
type event =
  | EOpenfile : a:io_args Openfile -> (r:io_resm Openfile) -> event
  | ERead     : a:io_args Read     -> (r:io_resm Read)     -> event
  | EClose    : a:io_args Close    -> (r:io_resm Close)    -> event

type trace = list event

// silent actions/steps
(** Silent steps refer to the impossibility of an observer to see
them. Two computations, one that uses GetTrace and does some IO, 
and another that does directly the same IO thing without playing 
with the trace, are equivalent from the observer point of view. **)
type tau_cmds = x:cmds{x = GetTrace}

(** We only need GetTrace because we assume that our actions are
updating the trace for us. Therefore, at extraction, our actions
should be linked with wrapped primitives that initialize a 
trace on the heap (?) and updates it with events. 
GetTrace will be linked with a function that returns the reference
to the trace from the heap. **)

(** Is our assumption limiting how the IO effect can be used?
 What if somebody wants to use only the IO effect? Then,
at extraction, they have to be careful to link it directly with the
primitives, and not with the wrapped version, otherwise, they will
suffer a performance penalty. **)
let tau_sig : cmd_sig tau_cmds = { 
  args = (fun (x:tau_cmds) -> match x with
    | GetTrace -> unit) ;
  res = (fun (x:tau_cmds) -> match x with
    | GetTrace -> list event)
}

let add_sig 
  (#p:cmds -> bool) 
  (#q:cmds -> bool) 
  (s1:cmd_sig (x:cmds{p x})) 
  (s2:cmd_sig (x:cmds{q x})) : 
  Tot (cmd_sig (y:cmds{p y || q y})) = {
    args = (fun (x:cmds{p x || q x}) -> if p x then s1.args x else s2.args x);
    res = (fun (x:cmds{p x || q x}) -> if p x then s1.res x else s2.res x)
  }

let all_sig = add_sig io_sig tau_sig 

unfold let args (op:cmds) : Type = all_sig.args op
unfold let res (op:cmds)  : Type = all_sig.res op
unfold let resm (op:cmds) : Type = maybe (all_sig.res op)

type io = free io_cmds io_sig
let io_return (a:Type) (x:a) : io a= free_return io_cmds io_sig a x
let io_throw (a:Type) (x:exn) : io a= free_throw io_cmds io_sig a x
let io_bind (a:Type) (b:Type) l k : io b = free_bind io_cmds io_sig a b l k

let io_call (cmd:io_cmds) (arg:io_args cmd) : io (io_res cmd) =
  free_perform (Call cmd arg (fun fd -> fd))

// THE IIO FREE MONAD
type iio = free cmds all_sig
let iio_return (a:Type) (x:a) : iio a = free_return cmds all_sig a x
let iio_throw (a:Type) (x:exn) : iio a = free_throw cmds all_sig a x
let iio_bind (a:Type) (b:Type) l k : iio b = free_bind cmds all_sig a b l k

let iio_call (cmd:cmds) (arg:args cmd) : iio (res cmd) =
  free_perform (Call cmd arg (fun fd -> fd))
  
// OTHER TYPES & UTILS
type action_type = (cmd : io_cmds) & (args cmd)

type monitorable_prop = (history:trace) -> (action:action_type) -> Tot bool

let convert_event_to_action (e:event) : action_type =
  match e with
  | EOpenfile arg _ -> (| Openfile, arg |)
  | ERead arg _ -> (| Read, arg |)
  | EClose arg _ -> (| Close, arg |)

let convert_call_to_event (cmd:io_cmds) (arg:io_args cmd) (r:io_resm cmd) =
  match cmd with
  | Openfile -> EOpenfile arg r
  | Read -> ERead arg r
  | Close -> EClose arg r

let rec enforced_locally (check : monitorable_prop) (h l: trace) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | hd  ::  t ->
    let action = convert_event_to_action hd in
    if check h action then enforced_locally (check) (hd::h) t
    else false

let rec enforced_globally (check : monitorable_prop) (h : trace) : Tot bool =
  (** enforced_locally check [] h // - fstar does not like this **)
  match h with
  | [] -> true
  | h  ::  t ->
    let action = convert_event_to_action h in
    if check t action then enforced_globally (check) t
    else false

let rev_append_rev_append () : Lemma (
  forall (h le1 le2:trace). ((List.rev le2) @ (List.rev le1) @ h) ==
     ((List.rev (le1@le2)) @ h)) =
  let aux (h le1 le2:trace) : Lemma (
    ((List.rev le2) @ (List.rev le1) @ h) ==
       ((List.rev (le1@le2)) @ h)) = begin
    List.rev_append le1 le2;
    List.append_assoc (List.rev le2) (List.rev le1) h
  end in Classical.forall_intro_3 aux

// val rev_append_rev_append_pat : h:trace -> le1:trace -> le2:trace ->
//   Lemma (requires True)
//         (ensures (((List.rev le2) @ (List.rev le1) @ h) ==
//      ((List.rev (le1@le2)) @ h))) [SMTPat (((List.rev le2) @ (List.rev le1) @ h))]
// let rev_append_rev_append_pat h le1 le2 = rev_append_rev_append ()

// val rev_nil : a:Type ->
//   Lemma (requires True)
//         (ensures (List.rev #a [] == []))
//         [SMTPat (List.rev #a [])]
// let rev_nil a = ()

unfold
let apply_changes (history local_events:trace) : Tot trace = (List.rev local_events) @ history 
