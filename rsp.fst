module Rsp

open FStar.Tactics

open Common
open IOStHist
open M4
open Minterop

type set_of_traces = events_trace -> Type0

val included_in : set_of_traces -> set_of_traces -> Type0
let included_in s1 s2 = forall t. s1 t ==>  s2 t

let rec behavior #a
  (m : io a) : set_of_traces =
  match m with
  | Return x -> fun t -> t == []
  | Throw err -> fun t -> t == []
  | Cont t -> begin
    match t with
    | Call cmd args fnc -> (fun t' -> 
      (exists res t. (
         FStar.WellFounded.axiom1 fnc res;
         (behavior (fnc res) t) /\
         t' == ((convert_call_to_event cmd args res)::t))))
  end

let included_in_trans #a #b #c () : Lemma (
  forall (t1:io a) (t2:io b) (t3:io c). behavior t1 `included_in` behavior t2 /\ behavior t2 `included_in` behavior t3 ==>
    behavior t1 `included_in` behavior t3) = ()

let behavior_iost_to_io () : Lemma
  (forall a tree. behavior (iost_to_io tree) `included_in` behavior tree) = admit ()

// let interstinglemma #a (x: io a) : Lemma (
//   let xx = M4?.reflect (fun _ -> x) <: M4wp a (fun p -> forall res. p res) in
//   behavior (reify xx) (fun _ -> True) `include_in` behavior x) = ()

let interstinglemma () : Lemma (forall a x.
  let xx : unit -> M4 a = (fun () -> (M4?.reflect (fun _ -> x) <: M4wp a (fun p -> forall res. p res))) in
  behavior (reify (xx ()) (fun _ -> True)) `included_in` behavior x) = ()
    
let pre_lemma #t1
  (pre : t1 -> events_trace -> Type0)  {| checkable2 pre |}
  (x : t1): Lemma (check2 #t1 #events_trace #pre x [] == true) = admit()

// let export_lemma #t1 #t2
//   {| d1:ml t1 |} {| d2:ml t2 |}
//   (pre : t1 -> events_trace -> Type0)
//   {| checkable2 pre |}
//   (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
//   (f:(x:t1 -> IOStHist t2 (pre x) (post x)))
//   (x:t1)  : Lemma (
//     let res' = reify ((_export_IOStHist_arrow_spec pre post f <: (t1 -> M4 t2)) x) (fun _ -> True) in
//     let f' = reify (f x) (post x []) in
//     check2 #t1 #events_trace #pre x [] == true ==>  behavior res' `included_in` behavior (f' [])
//   ) =
//   assume (behavior (iost_to_io (reify (f x) (post x []) [])) `included_in` behavior (reify (f x) (post x []) []));
//   assert (
//     check2 #t1 #events_trace #pre x [] == true ==>  behavior (reify ((_export_IOStHist_arrow_spec pre post f <: (t1 -> M4 t2)) x) (fun _ -> True)) `included_in` behavior (reify (f x) (post x []) []))
//   by (
//   let stst1 = implies_intro () in
//   unfold_def (`included_in);
//   let t = forall_intro () in
//   unfold_def (`_export_IOStHist_arrow_spec);
//   let tres = implies_intro () in
//   binder_retype tres;
    
//     rewrite_eqs_from_context ();
//   trefl ();
//   dump "h"
//   )


let export_lemma #t1 #t2
  {| d1:ml t1 |} {| d2:ml t2 |}
  (pre : t1 -> events_trace -> Type0)
  {| checkable2 pre |}
  (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
  (f:(x:t1 -> IOStHist t2 (pre x) (post x)))
  (x:t1)  : Lemma (
    let res' = reify ((_export_IOStHist_arrow_spec pre post f <: (t1 -> M4 t2)) x) (fun _ -> True) in
    let f' = reify (f x) (post x []) in
    check2 #t1 #events_trace #pre x [] == true ==>  behavior res' `included_in` behavior (f' [])
  ) by (    
  split ();
  smt (); 
  let pp = forall_intro () in
  let myp = implies_intro () in
  let pr = forall_intro () in
  let asd = FStar.Tactics.Logic.instantiate (binder_to_term myp) (binder_to_term pr) in
  mapply (binder_to_term asd);
  let stst1 = implies_intro () in
  unfold_def (`included_in);
  let t = forall_intro () in
  unfold_def (`_export_IOStHist_arrow_spec);
  rewrite_eqs_from_context ();
  dump "h";
  tadmit ();
  ()) = 
  ()

