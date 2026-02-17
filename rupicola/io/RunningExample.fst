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

[@expect_failure]
%splice_t[tgt_wrapper] (meta_translation "tgt_wrapper" [`wrapper])
