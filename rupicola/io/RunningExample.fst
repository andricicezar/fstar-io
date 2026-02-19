module RunningExample

open FStar.Tactics
open FStar.Tactics.Typeclasses
open IO
open Metaprogram
open ExamplesIO
open RrHP
open QTyp
open QExp

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
  | Inl _ -> return true
  | Inr _ -> return false

// %splice_t[validate_derivation] (generate_derivation "validate_derivation" (`validate))
// %splice_t[read_file_derivation] (generate_derivation "read_file_derivation" (`read_file))
// %splice_t[wrapper_derivation] (generate_derivation "wrapper_derivation" (`wrapper))

%splice_t[main_derivation] (generate_derivation "main_derivation" (`main))

// [@@ (preprocess_with simplify_qType)]
// let main_derivation () : oval_quotation empty (helper_oval main)
//   by (trefl ())
//   = QLambdaProd (
//       QBindProd
//         (QAppProd
//           (QApp (QApp wrapper_derivation (QStringLit "./temp"))
//                 (QStringLit "overwrite"))
//           QVar0)
//         (QCaseProd QVar0
//           (QReturn QTrue)
//           (QReturn QFalse)))

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
