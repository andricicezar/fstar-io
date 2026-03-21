module Free

(** Sum of two command types.
    Commands are indexed types (Type0 -> Type) parameterizing the free monad. *)
noeq
type cmd_sum (cmd1 cmd2 : Type0 -> Type) : Type0 -> Type =
| CmdL : #r:Type0 -> cmd1 r -> cmd_sum cmd1 cmd2 r
| CmdR : #r:Type0 -> cmd2 r -> cmd_sum cmd1 cmd2 r

(** Sum of two event types.
    Events are plain types parameterizing the hist monad. *)
noeq
type event_sum (ev1 ev2 : Type) =
| EvL : ev1 -> event_sum ev1 ev2
| EvR : ev2 -> event_sum ev1 ev2

type caller = | Prog | Ctx

(** Guard as a command: carries a precondition, returns its proof.
    Guard could replace the built-in Guard constructor of free (free would
    then have only Call and Return), with guard_cmd added to the command type
    via cmd_sum. We keep Guard built-in for simplicity, since factoring it out
    would require every command type to include guard_cmd via cmd_sum, and
    DMFree's lift_pure_dm / dm_guard_return to thread the injection. *)
noeq
type guard_cmd : Type0 -> Type =
| GCmd : (pre:pure_pre) -> guard_cmd (squash pre)

noeq
type free (cmd : Type u#i -> Type u#e) (a:Type u#a) : Type u#(max (1 + i) (max a e)) =
| Call : caller -> #r:Type u#i -> cmd r -> cont:(r -> free cmd a) -> free cmd a
| Guard : (pre:pure_pre) -> cont:((squash pre) -> free cmd a) -> free cmd a
| Return : a -> free cmd a

let free_return #cmd #a (x:a) : free cmd a =
  Return x

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
  | Guard pre fnc ->
      Guard pre (fun _ ->
        free_bind (fnc ()) k)

let free_map
  #cmd #a #b
  (l : free cmd a)
  (k : a -> b) :
  Tot (free cmd b) =
  free_bind l (fun a -> free_return (k a))

let free_codomain_ordering
  #cmd #a
  (x:(free cmd a){Call? x}) :
  Lemma (forall r. Call?.cont x r << x) = ()
