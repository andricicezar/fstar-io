module Error.Free

open Free
open Common

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

let gen_post #a (post:hist_post a) (cmd:io_cmds) args res =
  fun r local_trace ->
    post r (convert_call_to_event cmd args res :: local_trace)

(** Cezar: here Throw does not produce an event, should it?
I am not sure if the Catch should also appear **)
let rec io_interpretation #a
  (m : io a)
  (p : hist_post a) : Type0 =
  match m with
  | Return x -> p (Inl x) []
  | Call cmd args fnc -> (
    forall res. (
      io_interpretation (fnc res) (gen_post p cmd args res)))
type monitorable_prop = (history:trace) -> (action:action_type) -> Tot bool

let rec enforced_locally
  (check : monitorable_prop)
  (h l: trace) :
  Tot bool (decreases l) =
  match l with
  | [] -> true
  | hd  ::  t ->
    let action = convert_event_to_action hd in
    if check h action then enforced_locally (check) (hd::h) t
    else false

let rec enforced_globally (check : monitorable_prop) (h : trace) : Tot bool =
  match h with
  | [] -> true
  | h  ::  t ->
    let action = convert_event_to_action h in
    if check t action then enforced_globally (check) t
    else false

unfold
let apply_changes (history local_events:trace) : Tot trace =
  (List.rev local_events) @ history

// past_events (from new to old; reversed compared with local_trace)
let hist a = h:trace -> hist_post a -> Type0

unfold
let compute_post
  (a b:Type)
  (h:trace)
  (kw : a -> hist b)
  (p:hist_post b) :
  Tot (hist_post a) =
  (fun result local_trace ->
    match result with
    | Inl result -> (
      kw result
       ((List.rev local_trace) @ h)
       (fun result' local_trace' ->
         p result' (local_trace @ local_trace')))
    | Inr err -> p (Inr err) local_trace)

unfold
let hist_return (a:Type) (x:a) : hist a =
  fun _ p -> p (Inl x) []

unfold
let hist_bind
  (a:Type)
  (b:Type)
  (w : hist a)
  (kw : a -> hist b) :
  Tot (hist b) =
  fun h p ->
    w h (compute_post a b h kw p)

unfold
val hist_ord (#a : Type) : hist a -> hist a -> Type0
let hist_ord wp1 wp2 = forall h p. wp1 h p ==> wp2 h p

unfold
let hist_if_then_else (#a:Type) (wp1 wp2:hist a) (b:bool) : hist a =
  fun h p -> (b ==> wp1 h p) /\ ((~b) ==> wp2 h p)

// REFINED COMPUTATION MONAD (repr)
let io_irepr (a:Type) (wp:hist a) =
  h:trace -> post:hist_post a ->
    Pure (io a)
      (requires (wp h post))
      (ensures (fun (m:io a) -> io_interpretation m post))

let io_ireturn (a : Type) (x : a) : io_irepr a (hist_return a x) =
  fun _ _ -> io_return a x

let io_ibind
  (a b : Type)
  (wp_v : hist a)
  (wp_f: a -> hist b)
  (v : io_irepr a wp_v)
  (f : (x:a -> io_irepr b (wp_f x))) :
  Tot (io_irepr b (hist_bind _ _ wp_v wp_f)) =
  fun h p ->
    let t = (io_bind a b
        (v h (compute_post a b h wp_f p))
        (fun x ->
          assume (wp_f x h p);
           f x h p)) in
    assume (io_interpretation t p);
    t

unfold
let isubcomp (a:Type) (wp1 wp2: hist a) (f : io_irepr a wp1) :
  Pure (io_irepr a wp2)
    (requires hist_ord wp2 wp1)
    (ensures fun _ -> True) =
  f

unfold
let i_if_then_else
  (a : Type)
  (wp1 wp2: hist a)
  (f : io_irepr a wp1)
  (g : io_irepr a wp2) (b : bool) :
  Tot Type =
  io_irepr a (hist_if_then_else wp1 wp2 b)

total
reifiable
reflectable
layered_effect {
  IOwp : a:Type -> wp : hist a -> Effect
  with
       repr       = io_irepr
     ; return     = io_ireturn
     ; bind       = io_ibind

     ; subcomp      = isubcomp
     ; if_then_else = i_if_then_else
}

let lift_pure_iowp
  (a:Type)
  (wp:pure_wp a)
  (f:(eqtype_as_type unit -> PURE a wp)) :
  Tot (io_irepr a (fun h p -> wp (fun r -> p (Inl r) [])))
  = fun h p -> let r = elim_pure f (fun r -> p (Inl r) []) in io_return _ r

sub_effect PURE ~> IOwp = lift_pure_iowp

let throw (#a:Type) (err:exn) : IOwp a (fun _ p -> p (Inr err) []) =
  IOwp?.reflect(fun _ _ -> Call Throw err Return)

let f () : IOwp unit (fun h p -> False ==> p (Inr Contract_failure) []) =
  if false then ()
  else throw Contract_failure
