module Free

(** we only have bools in STLC right now **)

noeq
type free (a:Type u#a) : Type u#(max 1 a)=
| Read : cont:(bool -> free u#a a) -> free a
| Write : bool -> cont:(unit -> free u#a a) -> free a
| PartialCall : (pre:pure_pre) -> cont:((squash pre) -> free u#a a) -> free a
| Return : a -> free a

let free_return (#a:Type) (x:a) : free a =
  Return x

let rec free_bind
  (#a:Type u#a)
  (#b:Type u#b)
  (l : free a)
  (k : a -> free b) :
  free b =
  match l with
  | Return x -> k x
  | Read fnc ->
      Read (fun i ->
        free_bind #a #b (fnc i) k)
  | Write x fnc ->
      Write x (fun i ->
        free_bind #a #b (fnc i) k)
  | PartialCall pre fnc ->
      PartialCall pre (fun _ ->
        free_bind #a #b (fnc ()) k)

let free_read () : free bool =
  Read Return

let free_write (x:bool) : free unit =
  Write x Return
