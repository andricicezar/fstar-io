module IO

(** we only have bools in STLC right now **)

noeq
type io (a:Type u#a) : Type u#a =
| Read : cont:(bool -> io u#a a) -> io a
| Write : bool -> cont:(unit -> io u#a a) -> io a
//| PartialCall : (pre:pure_pre) -> cont:((squash pre) -> io u#a a) -> io a
| Return : a -> io a

let io_return (#a:Type) (x:a) : io a =
  Return x

let rec io_bind
  (#a:Type u#a)
  (#b:Type u#b)
  (l : io a)
  (k : a -> io b) :
  io b =
  match l with
  | Return x -> k x
  | Read fnc ->
      Read (fun i ->
        io_bind #a #b (fnc i) k)
  | Write x fnc ->
      Write x (fun i ->
        io_bind #a #b (fnc i) k)

let io_read () : io bool =
  Read Return

let io_write (x:bool) : io unit =
  Write x Return
