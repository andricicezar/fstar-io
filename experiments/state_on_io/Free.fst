module Free

noeq
type ev_sum (ev1 ev2 : Type0 -> Type0) : Type0 -> Type u#1 =
| InEv1 : #r:Type0 -> ev1 r -> ev_sum ev1 ev2 r
| InEv2 : #r:Type0 -> ev2 r -> ev_sum ev1 ev2 r

type caller = | Prog | Ctx

noeq
type free (ev : Type u#i -> Type u#e) (a:Type u#a) : Type u#(max (1 + i) (max a e)) =
| Call : caller -> #r:Type u#i -> ev r -> cont:(r -> free ev a) -> free ev a
| PartialCall : (pre:pure_pre) -> cont:((squash pre) -> free ev a) -> free ev a
| Return : a -> free ev a

let free_return #ev #a (x:a) : free ev a =
  Return x

let rec free_bind
  #ev #a #b
  (l : free ev a)
  (k : a -> free ev b) :
  free ev b =
  match l with
  | Return x -> k x
  | Call c cmd fnc ->
      Call c cmd (fun i ->
        free_bind (fnc i) k)
  | PartialCall pre fnc ->
      PartialCall pre (fun _ ->
        free_bind (fnc ()) k)

let free_map
  #ev #a #b
  (l : free ev a)
  (k : a -> b) :
  Tot (free ev b) =
  free_bind l (fun a -> free_return (k a))

let free_codomain_ordering
  #ev #a
  (x:(free ev a){Call? x}) :
  Lemma (forall r. Call?.cont x r << x) = ()
