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
  let!@! r = read fd in
  let!@! () = close fd in
  io_return (Inl r)


val wrapper : string -> string -> (string -> string -> io unit) -> io (resexn unit)
// val wrapper : progS wrapper_intS
let wrapper f task agent =
  let!@! contents = read_file f in
  let!@ () = agent f task in
  let!@! new_contents = read_file f in
  if validate contents task new_contents
  then io_return (Inl ())
  else io_return (Inr ())


(* Specification *)

unfold
let hist_prepost #a (pre : hist_pre) (post : (h:_ -> hist_post h a)) : hist a =
  fun h p -> pre h /\ (forall r lt. post h lt r ==> p lt r)

unfold
let basic_spec =
  hist_prepost
    (fun h -> True)
    (fun h lt r -> True)

let openfile_sat_spec f :
  Lemma (theta_unf (openfile f) ⊑ basic_spec)
= () // At least here it works (not with regular theta so we made progress)

let read_file_sat_spec f :
  Lemma (theta_unf (read_file f) ⊑ basic_spec)
= admit ()

unfold
let wrapper_spec (f task : string) =
  hist_prepost
    (fun h -> True)
    (fun h lt r -> True)

let wrapper_sat_spec f task agent :
  Lemma (theta_unf (wrapper f task agent) ⊑ wrapper_spec f task)
  // by (norm [delta_only [`%theta_unf;`%wrapper;`%(let!@!);`%(let!@);`%io_bind]] ; (* compute () ; *) explode () ; dump "oh")
= // unfold_theta #(resexn unit)
  introduce
    forall (h: Trace.history) (p: hist_post h (resexn unit)).
      (forall (r: resexn unit) (lt: Trace.local_trace h). p lt r) ==>
      theta_unf (wrapper f task agent) h p
  with begin
    introduce
      (forall (r: resexn unit) (lt: Trace.local_trace h). p lt r) ==>
      theta_unf (wrapper f task agent) h p
    with _. begin
      admit ()
    end
  end
  // ()

// assume (forall (h: Trace.history) (p: hist_post h (resexn unit)).
//       (forall (r: resexn unit) (lt: Trace.local_trace h). auto_squash (p lt r)) ==>
//       theta (wrapper f task agent) h p)

val main : (string -> string -> io unit) -> io bool
let main agent =
  let!@ r = wrapper "./temp" "overwrite" agent in
  match r with
  | Inl _ -> return true
  | Inr _ -> return false

// %splice_t[validate_derivation] (generate_derivation "validate_derivation" (`validate))
// %splice_t[read_file_derivation] (generate_derivation "read_file_derivation" (`read_file))

// %splice_t[main_derivation] (generate_derivation "main_derivation" (`main))

%splice_t[wrapper_derivation] (generate_derivation "wrapper_derivation" (`wrapper))
[@@ (preprocess_with simplify_qType)]
let main_derivation #g : oval_quotation g (helper_oval_g #_ #g main)
  by (trefl ())
  = QLambdaProd (
      QBindProd
        (QAppProd
          (QApp (QApp wrapper_derivation (QStringLit "./temp"))
                (QStringLit "overwrite"))
          QVar0)
        (QCaseProd QVar0
          (QReturn QTrue)
          (QReturn QFalse)))

let re_int : intS = {
  ct = (qString ^-> qString ^->!@ qUnit)
}


val ps_main : progS re_int
let ps_main : progS re_int=
  (| main, main_derivation #empty |)

let pt_main = RrHP.compile_prog ps_main

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
