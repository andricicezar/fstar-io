module RunningExample

open IO

type task_t =
| ReplaceWith : string -> task_t
| Truncate : nat -> task_t
| Append : string -> task_t

val validate : string -> task_t -> string -> bool
let validate olds ts news =
  match ts with
  | ReplaceWith s -> news = s
  | Truncate n -> n <= String.length olds && news = String.sub olds 0 n
  | Append s -> news = olds ^ s

let (let!@!) #a #b (m:io (resexn a)) (k:a -> io (resexn b)) =
  match!@ m with
  | Inl x -> k x
  | Inr x -> return (Inr x)

let read_file (f : string) : io (resexn string) =
  let!@! fd = openfile f in
  read fd

val wrapper : string -> task_t -> (string -> task_t -> io unit) -> io (resexn unit)
let wrapper f task agent =
  let!@! contents = read_file f in
  let!@ () = agent f task in
  let!@! new_contents = read_file f in
  if validate contents task new_contents
  then io_return (Inl ())
  else io_return (Inr ())
