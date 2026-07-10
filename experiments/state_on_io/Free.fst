module Free

(** Sum of two command types.
    Commands are indexed types (Type0 -> Type) parameterizing the free monad. *)
noeq
type cmd_sum (cmd1 cmd2 : Type -> Type) : Type -> Type =
| CmdL : #r:Type -> cmd1 r -> cmd_sum cmd1 cmd2 r
| CmdR : #r:Type -> cmd2 r -> cmd_sum cmd1 cmd2 r

(** Lifts a Type0-indexed command type to an arbitrary index universe:
    the result-type index is raised with FStar.Universe.raise_t and the
    interpreter has to downgrade the result before passing it to the
    continuation. This allows summing (via cmd_sum) command types whose
    result types live in different universes. *)
noeq
type cmd_downgrade (cmd : Type u#0 -> Type u#e) : Type u#a -> Type u#(max (1 + a) e) =
| CmdDowngrade : #r:Type u#0 -> cmd r -> cmd_downgrade cmd (FStar.Universe.raise_t u#0 u#a r)

(** Sum of two event types.
    Events are plain types parameterizing the hist monad. *)
noeq
type event_sum (ev1 ev2 : Type) =
| EvL : ev1 -> event_sum ev1 ev2
| EvR : ev2 -> event_sum ev1 ev2

type caller = | Prog | Ctx

noeq
type free (cmd : Type u#i -> Type u#e) (a:Type u#a) : Type u#(max (1 + i) (max a e)) =
| Call : caller -> #r:Type u#i -> cmd r -> cont:(r -> free cmd a) -> free cmd a
| Return : a -> free cmd a

val free_return : #cmd:(Type u#i -> Type u#e) -> #a:Type u#a -> x:a -> free cmd a
let free_return #cmd #a (x:a) : free cmd a =
  Return x

val free_bind : #cmd:(Type u#i -> Type u#e) -> #a:Type u#a -> #b:Type u#b -> l:free cmd a -> k:(a -> free cmd b) -> free cmd b
let rec free_bind
  #cmd #a #b
  (l : free cmd a)
  (k : a -> free cmd b) :
  free cmd b =
  match l with
  | Return x -> k x
  | Call c op fnc ->
      Call c op (fun i ->
        free_bind (fnc i) k)

val free_map : #cmd:(Type u#i -> Type u#e) -> #a:Type u#a -> #b:Type u#b -> l:free cmd a -> k:(a -> b) -> Tot (free cmd b)
let free_map
  #cmd #a #b
  (l : free cmd a)
  (k : a -> b) :
  Tot (free cmd b) =
  free_bind l (fun x -> free_return (k x))

let free_codomain_ordering
  #cmd #a
  (x:(free cmd a){Call? x}) :
  Lemma (forall r. Call?.cont x r << x) = ()
