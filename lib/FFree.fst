module FFree

(** Sum of two command types.
    Commands are indexed types (Type0 -> Type) parameterizing the free monad. *)
noeq
type cmd_sum (cmd1 cmd2 : Type -> Type) : Type -> Type =
| CmdL : #r:Type -> cmd1 r -> cmd_sum cmd1 cmd2 r
| CmdR : #r:Type -> cmd2 r -> cmd_sum cmd1 cmd2 r

(** Sum of two event types.
    Events are plain types parameterizing the hist monad. *)
noeq
type event_sum (ev1 ev2 : Type) =
| EvL : ev1 -> event_sum ev1 ev2
| EvR : ev2 -> event_sum ev1 ev2

noeq
type ffree (cmd : Type u#i -> Type u#e) (a:Type u#a) : Type u#(max (1 + i) (max a e)) =
| Call : #r:Type u#i -> cmd r -> cont:(r -> ffree cmd a) -> ffree cmd a
| Return : a -> ffree cmd a

val ffree_return : #cmd:(Type u#i -> Type u#e) -> #a:Type u#a -> x:a -> ffree cmd a
let ffree_return #cmd #a (x:a) : ffree cmd a =
  Return x

val ffree_bind : #cmd:(Type u#i -> Type u#e) -> #a:Type u#a -> #b:Type u#b -> l:ffree cmd a -> k:(a -> ffree cmd b) -> ffree cmd b
let rec ffree_bind
  #cmd #a #b
  (l : ffree cmd a)
  (k : a -> ffree cmd b) :
  ffree cmd b =
  match l with
  | Return x -> k x
  | Call op fnc ->
      Call op (fun i ->
        ffree_bind (fnc i) k)

val ffree_map : #cmd:(Type u#i -> Type u#e) -> #a:Type u#a -> #b:Type u#b -> l:ffree cmd a -> k:(a -> b) -> Tot (ffree cmd b)
let ffree_map
  #cmd #a #b
  (l : ffree cmd a)
  (k : a -> b) :
  Tot (ffree cmd b) =
  ffree_bind l (fun x -> ffree_return (k x))

let ffree_codomain_ordering
  #cmd #a
  (x:(ffree cmd a){Call? x}) :
  Lemma (forall r. Call?.cont x r << x) = ()
