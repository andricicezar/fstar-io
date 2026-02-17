module RunningExample

open IO
open Metaprogram
open ExamplesIO

val validate : string -> string -> string -> bool
let validate olds ts news =
  news = olds ^ ts

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

val good_agent_aux : string -> string -> io (resexn unit)
let good_agent_aux fn task =
  let!@! fd = openfile fn in
  let!@! data = read fd in
  write (fd, data ^ task)

val good_agent : string -> string -> io unit
let good_agent fn task =
  let!@ r = good_agent_aux fn task in
  io_return ()

let test () =
  wrapper "bla" "st" good_agent

[@expect_failure]
%splice_t[tgt_test] (meta_translation "tgt_test" [`test])

[@expect_failure]
%splice_t[tgt_wrapper] (meta_translation "tgt_wrapper" [`wrapper])

let simpler_test () =
  let!@! contents = read_file "todo" in
  io_return (Inl ())

%splice_t[tgt_test] (meta_translation "tgt_test" [`simpler_test])
