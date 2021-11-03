module Model.Proof

open FStar.List.Tot
open FStar.Calc
open FStar.Tactics

open Free
open Free.IO
open Common
open ExtraTactics
open TC.Checkable
open TC.Trivialize.IIOwp
open DM
open Model

let simple_linking_post pi h r lt =
  (~(iio_pre pi h) ==> r == (Inr (Contract_failure)) /\ lt == []) /\
  (iio_pre pi h ==> iio_post pi h r lt)

(** p "compiled" linked with instrumented c, gives a computation in IIO,
that respects the compuation **)
let simple_linking #i #pi (p:prog_s i pi) (c:ctx_t i) : 
  IIOwp (maybe i.ret)
    (fun h p -> forall r lt. simple_linking_post pi h r lt ==> p r lt) =
  (trivialize 
    #_ 
    #(trivializeable_IIOwp _ _ 
      (fun _ h -> iio_pre pi h) 
      (fun _ h r lt -> iio_post pi h r lt))
    p) (enforce_post #i #pi (instrument #i #pi c))


(**    assert (iio_interpretation wt h (fun r lt -> iio_post pi h r lt)) by (
      norm [delta_only [`%iio_interpretation]];
      norm [delta_only [`%simple_linking_post]];
      dump "h"
    )**)

(** the difference between _IIOwp_as_IIO and compile_prog is that 
the later casts the computation to MIIO, therefore we're losing 
the interpretation of p.
TODO: show this
Problem: Aseem: IIO is a layered effect, then this will not work since layered effects can only be reasoned about using their types and this example requires reasoning that g x == f x. We can only reason with the types of the layered effects code, and here once we have g with the type as shown, we don't have access to any postcondition about its result. To recover that, we need to look at the definition of g **)
let complex_linking #i #pi p c : 
  IIOwp (maybe i.ret)
    (fun h p -> 
      (~(iio_pre pi h) ==> p (Inr (Contract_failure)) []) /\
        (iio_pre pi h ==> (forall r lt. iio_post pi h r lt ==> p r lt))) =
  admit ();
  (compile_prog p) (instrument #i #pi c)

(**
  We have to show: 
    `(Beh W) in pi`, where W = link_t (compile_prog p) c.
  Proof: We know `interp W pi`, therefore we only have to define
  a Beh that can be implied out of the interp function.

  Just a note here about the Beh function. We did not know how to
  define it when silent steps were involved. For io we had a Beh
  function, but for io+exn, not. That's why we try to do the proof
  using only the interpretation, because during the process of 
  compilation, not much is changed. 
**)

let empty_set (#a:Type) () : set_of_traces a =
  fun (t,r) -> t == []

let pi_to_set #a (pi : monitorable_prop) : set_of_traces a =
  fun (t, _) -> enforced_globally pi (List.rev t)

val included_in : set_of_traces 'a -> set_of_traces 'a -> Type0
let included_in s1 s2 =
  forall t r1. s1 (t, r1) ==>  s2 (t, r1)

(** The behavior function has to keep the history along because
the behavior of iio programs depends on it. **)
let rec behavior #a
  (m : iio a) 
  (h : trace) : set_of_traces a =
  match m with
  | Return x -> fun t -> t == ([], x)
  | Call GetTrace arg fnc -> (fun (t', r') ->
    behavior (fnc h) h (t', r'))
  | Call cmd arg fnc -> (fun (t', r') ->
      exists r t. let e = (convert_call_to_event cmd arg r) in (
       (behavior (fnc r) (e::h) (t, r')) /\
       t' == e::t))

(** I believe this lemma is true, because the event produced by the cmd is the first
event from local_trace, therefore it respects the post. **)
let lemma_pi_cont i pi (cmd:io_cmds) (arg:args cmd) (cont:((res cmd)->iio (maybe i.ret))) h :
  Lemma 
    (requires (iio_interpretation (Call cmd arg cont) h (simple_linking_post pi h)))
    (ensures (pi h (| cmd, arg |)))  = 
     (** `Call cmd arg cont` implies that the proper checks were done already and for sure
          it respects pi, therefore it is ok to run the cmd. **)
  admit ()


let rec lemma_interp_cont_interp i pi (cmd:io_cmds) (arg:args cmd) (cont:((res cmd)->iio (maybe i.ret))) h (r:res cmd) :
  Lemma 
    (requires (iio_interpretation (Call cmd arg cont) h (simple_linking_post pi h)))
    (ensures (
      let h' = (convert_call_to_event cmd arg r) :: h in
      iio_interpretation (cont r) h' (simple_linking_post pi h'))) =
  lemma_pi_cont i pi cmd arg cont h;
  let e = (convert_call_to_event cmd arg r) in
 (**  assert (
    (iio_interpretation (cont r) (e::h) (Hist.gen_post (simple_linking_post pi h) cmd arg r))
    ==> 
    (iio_interpretation (cont r) (e::h) (simple_linking_post pi (e::h)))) 
    by (
        norm [delta_only [`%Hist.gen_post]];
        norm [delta_only [`%simple_linking_post]];
        norm [delta_only [`%iio_post]];
        norm [delta_only [`%apply_changes]];
        l_to_r [`Common.rev_head_append];
        dump "H") **)
  admit ()
  
let rec lemma_beh_cont i pi (cmd:io_cmds) (arg:args cmd) (cont:((res cmd)->iio (maybe i.ret))) h (r:res cmd) :
  Lemma
    (requires (
        let e = convert_call_to_event cmd arg r in 
        (b2t(pi h (| cmd, arg |))) /\
        behavior (cont r) (e::h) `included_in` (pi_to_set pi)))
    (ensures (behavior (Call cmd arg cont) h `included_in` (pi_to_set pi))) = 
    admit ()
    
(** TODO: this function should not be here. the following two lemmas, _beh_1 and _beh
    are mutually recursive, but when I try to define them as such, F* returns a universe error **)
let lemma_interp_implies_beh' i pi (w:iio (maybe i.ret)) (h:trace) :
  Lemma 
    (requires (iio_interpretation w h (simple_linking_post pi h)))
    (ensures (behavior w h `included_in` (pi_to_set pi))) = admit ()

let lemma_interp_implies_beh_1 i pi (cmd:io_cmds) (arg:args cmd) (cont:(res cmd -> iio (maybe i.ret))) (h:trace) (r:res cmd) :
  Lemma 
    (requires (
      let e = convert_call_to_event cmd arg r in 
      iio_interpretation (cont r) (e::h) (simple_linking_post pi (e::h))))
    (ensures (
      let e = convert_call_to_event cmd arg r in 
      behavior (cont r) (e::h) `included_in` (pi_to_set pi))) =
    let e = convert_call_to_event cmd arg r in 
    lemma_interp_implies_beh' i pi (cont r) (e::h)
    
let rec lemma_interp_implies_beh i pi (w:iio (maybe i.ret)) (h:trace) :
  Lemma 
    (requires (iio_interpretation w h (simple_linking_post pi h)))
    (ensures (behavior w h `included_in` (pi_to_set pi))) =
  match w with
  | Return x -> ()
  | Call cmd arg cont -> begin
    match cmd with
    | GetTrace -> 
      lemma_interp_implies_beh i pi (cont h) h
    | _ ->
      Classical.forall_intro (Classical.move_requires 
        (lemma_interp_cont_interp i pi cmd arg cont h));
      Classical.forall_intro (Classical.move_requires (lemma_interp_implies_beh_1 i pi cmd arg cont h));
      assert (forall r. 
        let e = convert_call_to_event cmd arg r in 
        behavior (cont r) (e::h) `included_in` (pi_to_set pi));
      lemma_pi_cont i pi cmd arg cont h;
      assert (pi h (| cmd, arg |));
      Classical.forall_intro (Classical.move_requires (
        (lemma_beh_cont i pi cmd arg cont h)));
      assert (behavior w h `included_in` (pi_to_set pi))
  end
