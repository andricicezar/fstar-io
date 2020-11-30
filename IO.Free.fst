module IO.Free

open Common
include Sys.Free

type cmds = | Openfile | Read | Close | GetTrace

// observable actions
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

unfold let io_args (op:io_cmds) : Type = io_sig.args op
unfold let io_res (op:io_cmds) = io_sig.res op
unfold let io_resm (op:io_cmds) = maybe (io_sig.res op)

noeq
type io_event =
    | EOpenfile : a:io_args Openfile -> (r:io_resm Openfile) -> io_event
    | ERead     : a:io_args Read     -> (r:io_resm Read)     -> io_event
    | EClose    : a:io_args Close    -> (r:io_resm Close)    -> io_event

type events_trace = list io_event

// silent actions/steps
// Silent steps refer to the impossibility of an observer to seeing them, and equivalence of computations. Two computations, one that uses GetTrace and does some IO, and another that does directly the same IO thing without playing with the trace, are equivalent from the observer point of view.
type tau_cmds = x:cmds{x = GetTrace}


let tau_sig : cmd_sig tau_cmds = { 
  args = (fun (x:tau_cmds) -> match x with
    | GetTrace -> unit ) ;
  res = (fun (x:tau_cmds) -> match x with
    | GetTrace -> list io_event)
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
unfold let res (op:cmds) = all_sig.res op
unfold let resm (op:cmds) = maybe (all_sig.res op)

type io = sys io_cmds io_sig
let io_return (a:Type) (x:a) = sys_return io_cmds io_sig a x
let io_throw (a:Type) (x:exn) = sys_throw io_cmds io_sig a x
let io_bind (a:Type) (b:Type) l k = sys_bind io_cmds io_sig a b l k

// ACTIONS
val io_openfile : io_args Openfile -> io (io_res Openfile) 
let io_openfile fnm =
  sys_perform (Call Openfile (fnm) (fun fd -> fd))

val io_read : io_args Read -> io (io_res Read)
let io_read fd =
  sys_perform (Call Read (fd) (fun msg -> msg))

val io_close : io_args Close -> io (io_res Close)
let io_close fd =
  sys_perform (Call Close (fd) (fun fd -> fd))

val io_all : (cmd:io_cmds) -> io_args cmd -> io (io_res cmd)
let io_all cmd args =
  match cmd with
  | Openfile -> io_openfile args
  | Read -> io_read args
  | Close -> io_close args

// THE IIO FREE MONAD
type iio = sys cmds all_sig
let iio_return (a:Type) (x:a) = sys_return cmds all_sig a x
let iio_throw (a:Type) (x:exn) = sys_throw cmds all_sig a x
let iio_bind (a:Type) (b:Type) l k = sys_bind cmds all_sig a b l k

// OTHER TYPES & UTILS
type action_type = (cmd : io_cmds) & (args cmd)

type monitorable_prop = (state:events_trace) -> (action:action_type) -> Tot bool

unfold let convert_event_to_action (event:io_event) : action_type =
  match event with
  | EOpenfile args _ -> (| Openfile, args |)
  | ERead args _ -> (| Read, args |)
  | EClose args _ -> (| Close, args |)

let rec enforced_locally (check : monitorable_prop) (acc : events_trace) (l : events_trace) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | h  ::  t ->
       let action = convert_event_to_action h in
       if check acc action then
         enforced_locally (check) (h::acc) t
       else false

let rec enforced_globally (check : monitorable_prop) (h : events_trace) : bool =
  match h with
  | [] -> true
  | h  ::  t ->
       let action = convert_event_to_action h in
       if check t action then
         enforced_globally (check) t
       else false

unfold
let apply_changes (old_state local_trace:events_trace) = (List.rev local_trace) @ old_state

