module RunningExample

open IO
open Metaprogram
open ExamplesIO

(* We consider the task is string that need to replace the old contents *)

val validate : string -> string -> string -> bool
let validate olds task news =
  eq_string task news

let read_file (f : string) : io (resexn string) =
  let!@! fd = openfile f in
  read fd

val wrapper : string -> string -> (string -> string -> io unit) -> io (resexn unit)
let wrapper f task agent =
  let!@! contents = read_file f in
  let!@ () = agent f task in
  let!@! new_contents = read_file f in
  if validate contents task new_contents
  then io_return (Inl ())
  else io_return (Inr ())

%splice_t[tgt_wrapper] (generate_derivation "tgt_wrapper" (`wrapper))

val good_agent_aux : string -> string -> io (resexn unit)
let good_agent_aux fn task =
  let!@! fd = openfile fn in
  // let!@! data = read fd in
  write (fd, task)

val good_agent : string -> string -> io unit
let good_agent fn task =
  let!@ r = good_agent_aux fn task in
  io_return ()

let test () =
  wrapper "bla" "st" good_agent

%splice_t[tgt_test] (generate_derivation "tgt_test" (`test))
