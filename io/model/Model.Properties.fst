module Model.Properties

open FStar.List.Tot
open FStar.Calc
open FStar.Tactics

open Common
open DM
open ExtraTactics
open TC.Checkable
open TC.Trivialize.IIOwp
open Model

(** The whole program (obtained after linking) is having a specification even if it
    is erased during compilation. Because the linking from the model erases the
    post-condition, we redefine it here s.t. we presevere the post-condition. **)

let simple_linking_post pi h lt r: Type0 =
  iio_post pi h r lt

(** p "compiled" linked with instrumented c, gives a computation in IIO,
that respects the post-condition **)
let simple_linking #i #m (p:prog_s i m) (c:ctx_t i) : 
  IIO (maybe i.ret) (fun _ -> True) (fun h r lt -> simple_linking_post m.pi h lt r) =
  (trivialize 
    #_ 
    #(trivializeable_IIOwp _ _ 
      (fun _ h -> true) 
      (fun _ h r lt -> iio_post m.pi h r lt))
    p) (enforce_post #i #m (instrument #i #m c))

(**
compile_prog erases the post-condition of p and we are not able to recovere it.
Problem: Aseem: IIO is a layered effect, then this will not work since layered effects can only be reasoned about using their types and this example requires reasoning that g x == f x. We can only reason with the types of the layered effects code, and here once we have g with the type as shown, we don't have access to any postcondition about its result. To recover that, we need to look at the definition of g **)
let complex_linking #i #m p c : 
  IIOwp (maybe i.ret)
    (fun p h -> (forall r lt. iio_post m.pi h r lt ==> p lt r)) =
  admit ();
  (compile_prog p) (instrument #i #m c)

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

type set_of_traces (a:Type) = trace * a -> Type0

let empty_set (#a:Type) () : set_of_traces a =
  fun (t,r) -> t == []

let pi_to_set #a (pi : monitorable_prop) : set_of_traces a =
  fun (t, _) -> enforced_locally pi [] t

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
  | PartialCall pre k -> (fun (t', r') -> 
      exists proof. behavior (k proof) h (t', r'))
  | Call cmd arg fnc -> (fun (t', r') ->
      exists r t. let e = (convert_call_to_event cmd arg r) in (
       (behavior (fnc r) (e::h) (t, r')) /\
       t' == e::t))

(** I believe this lemma is true, because the event produced by the cmd is the first
event from local_trace, therefore it respects the post. **)
let lemma_pi_cont i pi (cmd:io_cmds) (arg:iio_sig.args cmd) (cont:((iio_sig.res cmd arg)->iio (maybe i.ret))) h :
  Lemma 
    (requires (dm_iio_theta (Call cmd arg cont) (simple_linking_post pi h) h))
    (ensures (pi cmd arg h))  = 
     (** `Call cmd arg cont` implies that the proper checks were done already and for sure
          it respects pi, therefore it is ok to run the cmd. **)
  admit ()


let rec lemma_interp_cont_interp i pi (cmd:io_cmds) (arg:iio_sig.args cmd) (cont:((iio_sig.res cmd arg)->iio (maybe i.ret))) h (r:iio_sig.res cmd arg) :
  Lemma 
    (requires (dm_iio_theta (Call cmd arg cont) (simple_linking_post pi h) h))
    (ensures (
      let h' = (convert_call_to_event cmd arg r) :: h in
      dm_iio_theta (cont r) (simple_linking_post pi h') h')) =
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
  
let rec lemma_beh_cont i (pi:monitorable_prop) (cmd:io_cmds) (arg:iio_sig.args cmd) (cont:((iio_sig.res cmd arg)->iio (maybe i.ret))) h (r:iio_sig.res cmd arg) :
  Lemma
    (requires (
        let e = convert_call_to_event cmd arg r in 
        (b2t(pi cmd arg h)) /\
        behavior (cont r) (e::h) `included_in` (pi_to_set pi)))
    (ensures (behavior (Call cmd arg cont) h `included_in` (pi_to_set pi))) = 
    admit ()
    
(** TODO: this function should not be here. the following two lemmas, _beh_1 and _beh
    are mutually recursive, but when I try to define them as such, F* returns a universe error **)
let lemma_interp_implies_beh' i pi (w:iio (maybe i.ret)) (h:trace) :
  Lemma 
    (requires (dm_iio_theta w (simple_linking_post pi h) h))
    (ensures (behavior w h `included_in` (pi_to_set pi))) = admit ()

let lemma_interp_implies_beh_1 i pi (cmd:io_cmds) (arg:iio_sig.args cmd) (cont:(iio_sig.res cmd arg -> iio (maybe i.ret))) (h:trace) (r:iio_sig.res cmd arg) :
  Lemma 
    (requires (
      let e = convert_call_to_event cmd arg r in 
      dm_iio_theta (cont r) (simple_linking_post pi (e::h)) (e::h)))
    (ensures (
      let e = convert_call_to_event cmd arg r in 
      behavior (cont r) (e::h) `included_in` (pi_to_set pi))) =
    let e = convert_call_to_event cmd arg r in 
    lemma_interp_implies_beh' i pi (cont r) (e::h)
    
let rec lemma_interp_implies_beh i pi (w:iio (maybe i.ret)) (h:trace) :
  Lemma 
    (requires (dm_iio_theta w (simple_linking_post pi h) h))
    (ensures (behavior w h `included_in` (pi_to_set pi))) =
  match w with
  | Return x -> ()
  | PartialCall pre k -> admit ()
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
      assert (pi cmd arg h);
      Classical.forall_intro (Classical.move_requires (
        (lemma_beh_cont i pi cmd arg cont h)));
      assert (behavior w h `included_in` (pi_to_set pi))
  end
