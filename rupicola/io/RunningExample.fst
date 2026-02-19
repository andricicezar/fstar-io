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
  let!@! r = read fd in
  let!@! () = close fd in
  io_return (Inl r)

let wrapper_intS : intS = {
  ct = qString ^-> qString ^-> (qString ^-> qString ^->!@ qUnit) (* ^->!@ qResexn qUnit *)
}

val wrapper : string -> string -> (string -> string -> io unit) -> io (resexn unit)
// val wrapper : progS wrapper_intS
let wrapper f task agent =
  let!@! contents = read_file f in
  let!@ () = agent f task in
  let!@! new_contents = read_file f in
  if validate contents task new_contents
  then io_return (Inl ())
  else io_return (Inr ())

let wrapped_wrapper_fst f task agent : io bool =
  match!@ wrapper f task agent with
  | Inl () -> io_return true
  | Inr () -> io_return false

// [@expect_failure]
// %splice_t[tgt_wrapper] (generate_derivation "tgt_wrapper" (`wrapped_wrapper_fst))


(* Specification *)

unfold
let hist_prepost #a (pre : hist_pre) (post : (h:_ -> hist_post h a)) : hist a =
  fun h p -> pre h /\ (forall r lt. post h lt r ==> p lt r)

let wrapper_spec (f task : string) =
  hist_prepost (* Should I use to_hist? *)
    (fun h -> False)
    (fun h lt r -> True)

let wrapper_sat_spec f task agent :
  Lemma (theta (wrapper f task agent) ⊑ wrapper_spec f task)
= ()

// val wrapped_wrapper : progS wrapper_intS
// let wrapped_wrapper =
//   (wrapped_wrapper_fst, tgt_wrapper)

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
