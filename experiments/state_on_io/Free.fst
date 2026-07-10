module Free

(** Sum of two command types (within one channel of the free monad).
    Commands are indexed types (Type -> Type) parameterizing the free monad.
    Note that the two summands must have the same index universe: to mix
    commands whose result types live in different universes, put them on
    different channels of the free monad below. *)
noeq
type cmd_sum (cmd1 cmd2 : Type -> Type) : Type -> Type =
| CmdL : #r:Type -> cmd1 r -> cmd_sum cmd1 cmd2 r
| CmdR : #r:Type -> cmd2 r -> cmd_sum cmd1 cmd2 r

(** The empty command type: instantiates an unused channel. *)
noeq
type empty_cmds : Type u#f -> Type u#g =

(** Sum of two event types.
    Events are plain types parameterizing the hist monad. *)
noeq
type event_sum (ev1 ev2 : Type) =
| EvL : ev1 -> event_sum ev1 ev2
| EvR : ev2 -> event_sum ev1 ev2

type caller = | Prog | Ctx

(** The free monad has two command channels with independent universes.
    Universes of a datatype are computed per constructor and joined with
    max, so Call1 and Call2 can quantify their result types at different
    universes. This allows mixing commands whose results live in different
    universes (e.g. the Type0-resulting MST commands and get_heap, whose
    result erased heap lives in Type u#1) without universe-lifting
    wrappers: each command type goes on the channel matching its index
    universe. *)
noeq
type free (cmd1 : Type u#i -> Type u#j) (cmd2 : Type u#f -> Type u#g) (a:Type u#a)
  : Type u#(max (1 + i) (max (1 + f) (max j (max g a)))) =
| Call1 : caller -> #r:Type u#i -> cmd1 r -> cont:(r -> free cmd1 cmd2 a) -> free cmd1 cmd2 a
| Call2 : caller -> #r:Type u#f -> cmd2 r -> cont:(r -> free cmd1 cmd2 a) -> free cmd1 cmd2 a
| Return : a -> free cmd1 cmd2 a

val free_return : #cmd1:(Type u#i -> Type u#j) -> #cmd2:(Type u#f -> Type u#g) -> #a:Type u#a -> x:a -> free cmd1 cmd2 a
let free_return #cmd1 #cmd2 #a (x:a) : free cmd1 cmd2 a =
  Return x

val free_bind : #cmd1:(Type u#i -> Type u#j) -> #cmd2:(Type u#f -> Type u#g) -> #a:Type u#a -> #b:Type u#b -> l:free cmd1 cmd2 a -> k:(a -> free cmd1 cmd2 b) -> free cmd1 cmd2 b
let rec free_bind
  #cmd1 #cmd2 #a #b
  (l : free cmd1 cmd2 a)
  (k : a -> free cmd1 cmd2 b) :
  free cmd1 cmd2 b =
  match l with
  | Return x -> k x
  | Call1 c op fnc ->
      Call1 c op (fun i ->
        free_bind (fnc i) k)
  | Call2 c op fnc ->
      Call2 c op (fun i ->
        free_bind (fnc i) k)

val free_map : #cmd1:(Type u#i -> Type u#j) -> #cmd2:(Type u#f -> Type u#g) -> #a:Type u#a -> #b:Type u#b -> l:free cmd1 cmd2 a -> k:(a -> b) -> Tot (free cmd1 cmd2 b)
let free_map
  #cmd1 #cmd2 #a #b
  (l : free cmd1 cmd2 a)
  (k : a -> b) :
  Tot (free cmd1 cmd2 b) =
  free_bind l (fun x -> free_return (k x))

let free_codomain_ordering
  #cmd1 #cmd2 #a
  (x:(free cmd1 cmd2 a){Call1? x \/ Call2? x}) :
  Lemma ((Call1? x ==> (forall r. Call1?.cont x r << x)) /\
         (Call2? x ==> (forall r. Call2?.cont x r << x))) = ()
