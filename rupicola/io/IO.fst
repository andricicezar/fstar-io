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

let read () : io bool =
  Read Return

let write (x:bool) : io unit =
  Write x Return

let read_wp () : hist #event bool =
  to_hist (fun _ -> True) (fun h r lt -> lt == [EvRead r])

let write_wp (b:bool) : hist #event unit =
  to_hist (fun _ -> True) (fun h r lt -> lt == [EvWrite b])

let rec theta #a (m:io a) : hist #event a =
  match m with
  | Return x -> hist_return x
  | Read k -> hist_bind (read_wp ()) (fun r -> theta (k r))
  | Write v k -> hist_bind (write_wp v) (fun r -> theta (k r))
