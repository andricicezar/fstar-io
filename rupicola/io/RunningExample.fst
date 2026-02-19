module RunningExample

open FStar.Tactics
open FStar.Tactics.Typeclasses
open IO
open Metaprogram
open ExamplesIO
open RrHP
open QTyp

(* We consider the task is string that need to replace the old contents *)

val validate : string -> string -> string -> bool
let validate olds task news =
  eq_string task news

let read_file (f : string) : io (resexn string) =
  let!@! fd = openfile f in
  read fd


val wrapper : string -> string -> (string -> string -> io unit) -> io (resexn unit)
// val wrapper : progS wrapper_intS
let wrapper f task agent =
  let!@! contents = read_file f in
  let!@ () = agent f task in
  let!@! new_contents = read_file f in
  if validate contents task new_contents
  then io_return (Inl ())
  else io_return (Inr ())

val main : (string -> string -> io unit) -> io bool
let main agent =
  let!@ r = wrapper "./temp" "overwrite" agent in
  match r with
  | Inl () -> io_return true
  | Inr () -> io_return false

%splice_t[main_derivation] (generate_derivation "main_derivation" (`main))

let wrapper_intS : intS = {
  ct = (qString ^-> qString ^->!@ qUnit)
}
// val wrapped_wrapper : progS wrapper_intS
// let wrapped_wrapper =
//   (wrapped_wrapper_fst, tgt_wrapper)

// let compile_wrapper : compile_prog #wrapper_intS wrapper = solve

// val good_agent_aux : string -> string -> io (resexn unit)
// let good_agent_aux fn task =
//   let!@! fd = openfile fn in
//   // let!@! data = read fd in
//   write (fd, task)

// val good_agent : string -> string -> io unit
// let good_agent fn task =
//   let!@ r = good_agent_aux fn task in
//   io_return ()

// let test () =
//   wrapper "bla" "st" good_agent

// %splice_t[tgt_test] (generate_derivation "tgt_test" (`test))
