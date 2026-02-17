module RunningExample

open IO
open Metaprogram

(* The task is to append the string *)
unfold
type task_t = string

val validate : string -> task_t -> string -> bool
let validate olds ts news =
  news = olds ^ ts

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

[@expect_failure]
%splice_t[tgt_wrapper] (meta_translation "tgt_wrapper" [`ExamplesIO.utf8_encode;`wrapper])
