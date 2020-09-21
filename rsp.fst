module Rsp

open FStar.Calc
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

let empty_set : set_of_traces = fun t -> t == []

let export_empty_set (a:Type) {| exportable a |} ()
  : Lemma (forall (x:a). behavior (io_return _ (export x)) `included_in` empty_set) = ()

let ibind_f_export 
  #t2 {| d:exportable t2 |}
  (f:io t2) :
  Lemma
    (included_in
      (behavior f)
      (behavior (io_bind t2 d.etype f (fun x -> io_return _ (export x))))) 
  by (
    explode ();
    dump "h"
  ) = 
  export_empty_set t2 ();
  ()


let iost_to_io #t2 (tree : io (events_trace * t2)) : io t2 =
  match tree with
  | Return (s1, r) -> Return r
  | Throw r -> Throw r
  | Cont (Call cmd argz fnc) ->
    io_bind (events_trace * t2) t2
      (Cont (Call cmd argz fnc))
      (fun (_, r) -> io_return _ r)

let behavior_iost_to_io () : 
  Lemma (forall (a:Type) (tree:io (events_trace * a)). 
    behavior (iost_to_io tree) `included_in` behavior tree) = admit ()



unfold let ref #a (x : io a) : M4.irepr a (fun p -> forall res. p res) = (fun _ -> x)

let _export_IOStHist_lemma #t1 #t2
  {| d1:importable t1 |}
  {| d2:exportable t2 |}
  (pre : t1 -> events_trace -> Type0)
  {| checkable2 pre |}
  (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
  (f:(x:t1 -> IOStHist t2 (pre x) (post x))) 
  (x':d1.itype) : 
  Lemma (match import x' with
    | Some x -> (
        let ef : d1.itype -> M4 d2.etype = _export_IOStHist_arrow_spec pre post f in
        let res' = reify (ef x') (fun _ -> True) in

        let f' = reify (f x) (post x []) in
        check2 #t1 #events_trace #pre x [] ==>  behavior res' `included_in` behavior (f' []))
        // TODO: prove that behavior of res is empty trace if check2 fails?
    | None -> 
       // TODO: prove that behavior of res is the empty trace if import fails?
           True)=

  match import x' with
  | Some x -> begin
    if (check2 #t1 #events_trace #pre x []) then (
        let ef : d1.itype -> M4 d2.etype = _export_IOStHist_arrow_spec pre post f in
        calc (included_in) {
            behavior (reify (ef x') (fun _ -> True));
            `included_in` {}
            behavior (reify ((_export_IOStHist_arrow_spec pre post f <: (d1.itype -> M4 d2.etype)) x') (fun _ -> True));
            `included_in` { _ by (unfold_def(`_export_IOStHist_arrow_spec); norm [delta]) }
            behavior (reify (
              (export (M4wp?.reflect (ref (iost_to_io (reify (f x) (post x []) []))) <: M4wp t2 (fun p -> forall res. p res)) <: d2.etype)) (fun _ -> True));
            == { admit () } // unfold reify
            // Cezar: is the 3rd argument correct? I suppose it should pre and post
            behavior (M4.ibind t2 d2.etype (fun p -> forall res. p res) (fun x -> m4_return_wp (d2.etype) (export x))
                (reify (M4wp?.reflect (ref (iost_to_io (reify (f x) (post x []) []))) <: M4wp t2 (fun p -> forall res. p res)))
                (fun x -> lift_pure_m4wp d2.etype (fun p -> p (export x)) (fun _ -> export x)) (fun _ -> True));
            `included_in` { _ by (unfold_def (`ibind); dump "H"); admit () }
            behavior (M4.ibind t2 d2.etype (fun p -> forall res. p res) (fun x -> m4_return_wp (d2.etype) (export x))
                (ref (iost_to_io (reify (f x) (post x []) [])))
                (fun x -> lift_pure_m4wp d2.etype (fun p -> p (export x)) (fun _ -> export x)) (fun _ -> True));
        //     `included_in` { test  (ref (iost_to_io (reify (f x) (post x []) []))) }
        //     // `included_in` { _ by (norm [iota]; dump "h") }
            == { admit () }
            behavior (iost_to_io (reify (f x) (post x []) []));
            `included_in` { behavior_iost_to_io () }
            behavior (reify (f x) (post x []) []);
        }
    ) else ()
  end
  | None -> ()


let export_IOStHist_lemma 
  #t1 {| d1:importable t1 |} 
  #t2 {| d2:exportable t2 |}
  (pre : t1 -> events_trace -> Type0) {| checkable2 pre |}
  (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
  (f:(x:t1 -> IOStHist t2 (pre x) (post x))) : 
  Lemma (forall (x':d1.itype). (
    match import x' with
    | Some x -> (
        let ef : d1.itype -> M4 d2.etype = export f in
        let res' = reify (ef x') (fun _ -> True) in

        let f' = reify (f x) (post x []) in

        check2 #t1 #events_trace #pre x [] == true ==>  behavior res' `included_in` behavior (f' []))
    | None -> True)) =
  Classical.forall_intro (_export_IOStHist_lemma #t1 #t2 pre post f)


let export_GIO_lemma 
  #t1 {| d1:importable t1 |} 
  #t2 {| d2:exportable t2 |}
  (pi:check_type)
  (f:(x:t1 -> GIO t2 pi)) : 
  Lemma (forall (x':d1.itype). (
    match import x' with
    | Some x -> (
        let ef : d1.itype -> M4 d2.etype = export f in
        let res' = reify (ef x') (fun _ -> True) in

        let f' = reify (f x) (gio_post pi []) in

        check2 #t1 #events_trace #(fun _ -> gio_pre pi) x [] == true ==>  behavior res' `included_in` behavior (f' []))
    | None -> True)) =
  Classical.forall_intro (_export_IOStHist_lemma (fun _ -> gio_pre pi) (fun _ -> gio_post pi) f)

let export_GIO_lemma' 
  #t1 {| d1:importable t1 |} 
  #t2 {| d2:exportable t2 |}
  (pi:check_type)
  (f:(x:t1 -> GIO t2 pi)) : 
  Lemma (forall (x':d1.itype). (
    match import x' with
    | Some x -> (
        let ef : d1.itype -> M4 d2.etype = _export_IOStHist_arrow_spec (fun _ -> gio_pre pi) (fun _ -> gio_post pi) f in
        let res' = reify (ef x') (fun _ -> True) in

        let f' = reify (f x) (gio_post pi []) in

        check2 #t1 #events_trace #(fun _ -> gio_pre pi) x [] == true ==>  behavior res' `included_in` behavior (f' []))
    | None -> True)) =
  Classical.forall_intro (_export_IOStHist_lemma (fun _ -> gio_pre pi) (fun _ -> gio_post pi) f)

let rsp_left 
  (a : Type) {| d1:exportable a |}
  (b : Type) {| d2:ml b |}
  (c : Type) {| d3:exportable c |}
  (pi : check_type)
  (p : ((ct:(a -> GIO b pi)) -> GIO c pi))
  (ct : (d1.etype -> M4 b)) :
  Lemma (forall (pi_as_set:set_of_traces).
    match import ct with
    | Some (ct' : (pi:check_type) -> a -> GIO b pi) -> 
        let pct : unit -> GIO c pi = fun _ -> p (ct' pi) in
        let pct' : unit -> M4 d3.etype = _export_IOStHist_arrow_spec (fun _ -> gio_pre pi) (fun _ -> gio_post pi) pct in
        behavior (reify (pct ()) (gio_post pi []) []) `included_in` pi_as_set ==> 
        behavior (reify (pct' ()) (fun _ -> True)) `included_in` pi_as_set
    | None -> False) // by (explode (); bump_nth 10; explode (); dump "h")
  = 
  match import ct with
  | Some (ct' : (pi:check_type) -> a -> GIO b pi) -> 
      let pct : unit -> GIO c pi = fun _ -> p (ct' pi) in
      export_GIO_lemma pi pct;
      let pct' : unit -> M4 d3.etype = _export_IOStHist_arrow_spec (fun _ -> gio_pre pi) (fun _ -> gio_post pi) pct in
      export_GIO_lemma' pi pct;
      calc (included_in) {
        behavior (reify (pct' ()) (fun _ -> True));
        `included_in` { _ by (dump "h") }
        behavior (reify (pct ()) (gio_post pi []) []);
        `included_in` {}
        behavior (reify (p (ct' pi)) (gio_post pi []) []);
      }
  | None -> ()
