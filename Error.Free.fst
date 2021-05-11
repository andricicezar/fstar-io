module Error.Free

exception Contract_failure

type maybe a = either a exn

noeq
type op_sig (op:Type u#a) = {
  args : op -> Type u#a;
  res : op -> Type u#a;
}

noeq
type free (op:Type u#o) (s:op_sig op) (a:Type u#a) : Type u#(max o a) =
| Call : (l:op) -> s.args l -> cont:(s.res l -> free op s a) -> free op s a
| Return : a -> free op s a

let free_return (op:Type) (s:op_sig op) (a:Type) (x:a) : free op s a =
  Return x

(** Cezar: this file is an experiment to:

Tasks:
- [x] define Throw as an operation on the Free Monad
- [ ] update the effect observation
      (if needed, also the post-condition may change)
- [ ] define the try_catch block
- [ ] Cezar: I don't have a good intuition about how trace properties look
for programs that contain try_catch blocks. Is our pi expressive enough for
this kind of programs? **)

type io_cmds = | Openfile | Throw

unfold let io_args (cmd:io_cmds) : Type =
  match cmd with
  | Openfile -> string
  | Throw -> exn

let _io_res (cmd:io_cmds{cmd == Openfile}) : Type =
  match cmd with
  | Openfile -> int

unfold let io_res (cmd:io_cmds) : Type =
  match cmd with
  | Openfile -> maybe (_io_res cmd)
  | Throw -> False

let io_sig : op_sig io_cmds = { args = io_args; res = io_res; }

type io a = free io_cmds io_sig a

let io_return (a:Type) (x:a) : io a =
  free_return io_cmds io_sig a x

let rec io_try_catch_finnaly
  (a b:Type)
  (try_block:io a)
  (catch_block:exn -> io b)
  (finnaly:a -> io b) :
  Tot (io b) =
  match try_block with
  | Return x -> finnaly x
  (** Cezar: we can replace the node Throw directly with the catch_block.
      This is a nice solution because it implies that in the tree a 
      node Throw is a 'leaf' (except, it is followed by a `Return False`
      node). This simplifies how we do the interpretation later where,
      if we meet a Throw node, then we know the computation ended. **)
  | Call Throw err fnc -> catch_block err
  | Call cmd argz fnc ->
      Call cmd argz (fun res ->
        io_try_catch_finnaly a b (fnc res) catch_block finnaly)

let rec io_try_catch
  (#a:Type)
  (try_block:io a)
  (catch_block:exn -> io a) :
  Tot (io a) =
  match try_block with
  | Return x -> Return x
  | Call Throw err fnc -> catch_block err
  | Call cmd argz fnc ->
      Call cmd argz (fun res ->
        io_try_catch (fnc res) catch_block)

(** TODO: try to define this using io_try_catch + free_bind 
let rec io_try_catch_finnaly
  (a b:Type)
  (try_block:io a)
  (catch_block:exn -> io a)
  (finnaly:a -> io b) :
  Tot (io b) = **)

(** Cezar: is it weird that we do not use the bind of free? **)
let io_bind (a:Type) (b:Type) l k : io b =
  io_try_catch_finnaly a b l (fun err -> Call Throw err Return) k

noeq
type event =
  | EOpenfile : a:io_args Openfile -> (r:io_res Openfile) -> event

type trace = list event

// OTHER TYPES & UTILS
type action_type = (cmd : io_cmds) & (io_args cmd)

unfold let convert_event_to_action (e:event) : action_type =
  match e with
  | EOpenfile arg _ -> (| Openfile, arg |)

unfold let convert_call_to_event
  (cmd:io_cmds{Openfile == cmd})
  (arg:io_args cmd)
  (r:io_res cmd) =
  match cmd with
  | Openfile -> EOpenfile arg r

// local_trace (from old to new)
(** Cezar: Should `post` be defined over `maybe a` or `a`?
I suppose `maybe a` is more expressive, but this implies
special treatment of exceptions in the effect observation
to optionalize errors and results. **)
let hist_post a = maybe a -> lt:trace -> Type0

(** Cezar: TODO: this type-checks for some reason, but it 
    should not. it should require cmd to have a refinement **)
let gen_post #a (post:hist_post a) (cmd:io_cmds) args res =
  fun r local_trace ->
    post r (convert_call_to_event cmd args res :: local_trace)

let rec io_interpretation #a
  (m : io a)
  (p : hist_post a) : Type0 =
  match m with
  | Return x -> p (Inl x) []
  | Call Throw exn _ -> p (Inr exn) []
  | Call cmd args fnc -> (
    forall res. (
      io_interpretation (fnc res) (gen_post p cmd args res)))

let prog1 : io unit = 
  Call Throw Contract_failure Return

(** Cezar: why is this working? **)
let _ = assert (io_interpretation prog1 (fun r lt ->
  r == (Inr Contract_failure) /\ lt == []))

let prog2 : io unit =
  io_try_catch
    (Call Throw Contract_failure Return)
    (fun exn -> Return ())
  
(** Cezar: the property "the whole programs does not raise any exception"
can be checked by looking if r is Inl and not Inr.**)
let _ = assert (io_interpretation prog2 (fun r lt -> 
  r == (Inl ()) /\ lt == []))

let prog3 : io unit = 
   Call Openfile "text.txt" (fun (x:either int exn) ->
    match x with | Inl x' -> Return () | Inr err -> Call Throw err Return)

let _ = 
  assert (io_interpretation prog3 (fun r lt ->
    match r with
    | Inl r' -> exists fd. lt == [EOpenfile "text.txt" (Inl fd)]
    | Inr err -> lt == [EOpenfile "text.txt" (Inr err)])) 
      
let prog4 : io unit =
  io_try_catch
    prog3
    (fun err -> Return ())

let _ =
  assert (io_interpretation prog4 (fun r lt -> 
    r == (Inl ()) /\ (
      (exists fd. lt == [EOpenfile "text.txt" (Inl fd)]) \/
      (exists err. lt == [EOpenfile "text.txt" (Inr err)])) ))
