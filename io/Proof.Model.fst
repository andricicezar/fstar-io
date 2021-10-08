module Proof.Model

open FStar.List.Tot
open FStar.Calc
open FStar.Tactics


open Free.IO
open Common
open ExtraTactics
open Checkable
open DM
open Instrument

noeq type compiler = {
  interface : Type;
  set_of_traces : Type -> Type;
  monitorable_prop : Type;
  safety_prop   : (#a:Type) -> monitorable_prop -> set_of_traces a;

  res_s   : interface -> Type;
  prog_s  : interface -> monitorable_prop -> Type;
  ctx_s   : interface -> monitorable_prop -> Type;
  whole_s : interface -> monitorable_prop -> Type;
  link_s  : (#i:interface) -> (#pi:monitorable_prop) ->
            ctx_s i pi -> prog_s i pi -> Tot (whole_s i pi);

  res_t   : interface -> Type;
  prog_t  : interface -> Type;
  ctx_t   : interface -> Type;
  whole_t : interface -> Type;
  link_t  : (#i:interface) -> (#pi:monitorable_prop) ->
            ctx_t i -> prog_t i -> Tot (whole_t i);

  compile_prog  : (#i:interface) -> (#pi:monitorable_prop) ->
                  prog_s i pi -> Tot (prog_t i);
//  compile_whole : (#i:interface) -> (#pi:monitorable_prop) ->
//                  whole_s i pi -> Tot (whole_t i);
}

noeq type interface = {
  ctx_arg : Type;
  ctx_ret: Type;
  ctx_post :
    ctx_arg -> trace -> maybe ctx_ret -> trace -> Type0;
  ctx_post_c : checkable4 ctx_post;

  ret : Type;
}

(** The whole program does not need a pre-condition. 

Also, a post-condition would be useless since the system/
environment can not use it. **)

val whole_pre' : unit -> trace -> bool
let whole_pre' _ h = true 

val whole_pre : unit -> trace -> Type0
let whole_pre x h = whole_pre' x h

let whole_pre_cc : checkable2 whole_pre =
  general_is_checkable2 unit trace whole_pre'

type whole_s (i:interface) (pi:monitorable_prop) =
  x:unit -> IIO i.ret pi (whole_pre x) (fun _ _ _ -> True)
type whole_t (i:interface) = unit -> MIIO (maybe i.ret)

(** Having a pre-condition for the context is not necessary,
because the context would not know about it. 
If we set a pre-condition for the context, the pre-condition 
is more of a promise that the partial-program has to fulfil.

We make the following remarks about a context's post-condition:
* If the post-condition is only about the returned result, then
  the post-condition should be written as a refinement on the type
  of the result.
* At runtime, the post-condition is verified after the execution of
  the context is over. Therefore, a safety property stated
  in the post-condition would lose its 'safety' when checked at runtime,
  because unsafe behavior could happen before the check happens.
* a post-condition is needed. e.g.:
  if the returned value is a file descriptor and the 
  post-condition guarantees: "the returned file descriptor is open".
**)

let tpre : (i:interface) -> (i.ctx_arg -> trace -> bool) = fun i x h -> true
type ctx_t (i:interface) = i.ctx_arg -> MIO i.ctx_ret
(** The ctx_s stands for the instrumented context, therefore the
    output type is different compared to ctx_t.
    ctx_t has the output type `i.ctx_ret`, but ctx_s has `maybe i.ctx_ret`.
    This is needed to accomodate the possibility of failure during 
    instrumentation when a contract is violated. **)
type ctx_s (i:interface) (pi:monitorable_prop) =
  (x:i.ctx_arg) -> IIO (maybe i.ctx_ret) pi (fun h -> tpre i x h) (i.ctx_post x)

(** The partial program does not need a pre- or a post-condition because
    it is the starting point of the execution in this model. **)
type prog_s (i:interface) (pi:monitorable_prop) =
  ctx_s i pi -> IIO i.ret pi (fun _ -> True) (fun _ _ _ -> True)
(** prog_t can not fail since it is statically verified. The instrumentation
    of the context may return an error, but the partial program should treat
    that error **)
type prog_t (i:interface) (pi:monitorable_prop) =
  ctx_s i pi -> MIIO i.ret

let extract_local_trace (h:trace) (pi:monitorable_prop) :
  IIO trace pi
    (requires (fun h' -> True)) // suffix_of h h'))
    (ensures (fun h' r lt ->
      lt == [] /\
      h' == (apply_changes h r)))
  =
  admit ();
  let h' = get_trace () in
  suffix_of_length h h';
  let n : nat = (List.length h') - (List.length h) in
  let (lt, ht) = List.Tot.Base.splitAt n h' in
  assume (lt @ ht == h');
  assume (ht == h);
  List.Tot.Properties.rev_involutive lt;
  assert (h' == apply_changes h (List.rev lt));
  List.rev lt

(** CA: The body of this function was inlined in `instrument` but the block
if-then-else added some extra weird goals which did not make sense,
therefore a fast fix was extracting the block in a different function. **)
let enforce_post
  (#t1:Type)
  (#t2:Type)
  (post:t1 -> trace -> maybe t2 -> trace -> Type0)
  {| d4:checkable4 post |}
  (x:t1)
  (h:trace)
  (r:maybe t2)
  (lt:trace) :
  IIOwp (maybe t2) (fun _ p ->
    let b = check4 #t1 #trace #(maybe t2) #trace #post x h r lt in
    (b ==>  p r []) /\
    (~b ==>  p (Inr Contract_failure) [])) =
  if check4 #t1 #trace #(maybe t2) #trace #post x h r lt
  then r
  else (Inr Contract_failure)

let instrument
  (i  : interface)
  (pi : monitorable_prop)
  (ct : ctx_t i) :
  Tot (ctx_s i pi) =
  fun (x:i.ctx_arg) ->
    admit ();
    let h : trace = get_trace () in
    let r : maybe i.ctx_ret =
      instrument_MIIO
        (cast_io_iio ((* MIIO.*)reify (ct x) [] (fun _ _ -> True))) pi in
    let lt : trace = extract_local_trace h pi in
    enforce_post #i.ctx_arg #i.ctx_ret i.ctx_post #i.ctx_post_c x h r lt

(**
  Context: During compilation, p is wrapped in a new function
  that first does a runtime check. The runtime check verifies if the 
  history respects pi. Since the partial program is our starting
  point, the history is always empty, and the result of the runtime 
  check is always true.

  TODO: I don't know how to state that the history is always empty.
**)

(** Blocked: the assumption simplifies the compilation function, but
I don't see how we can get rid of it. In the end, it can not be guaranteed
that when the partial program starts, the history is empty. **)
let compile_prog'
  (#i  : interface)
  (#pi : monitorable_prop)
  (p  : prog_s i pi) 
  (c : ctx_s i pi) :
  MIIO i.ret by (iio_tactic ()) = 
  assume (get_trace () == []);
  p c

let compile_prog
  (#i  : interface)
  (#pi : monitorable_prop)
  (p  : prog_s i pi) :
  Tot (prog_t i pi) =
      compile_prog' p

(**
let compile_whole
  (#i  : interface)
  (#pi : monitorable_prop)
  (w  : whole_s i pi) :
  Tot (whole_t i) =
  _IIOwp_as_MIIO
    (fun _ -> iio_pre pi)
    (fun _ h r lt -> iio_post pi h r lt)
    w**)

(** the lift from "MIO to MIIO" for the context should happen
during linking. It is improper to say "should happen", because
the lift represents the assumptions: "the context uses
only the IO library which comes with instrumentation".
 **)
val link_s  : (#i:interface) -> (#pi:monitorable_prop) -> ctx_s i pi ->
              prog_s i pi -> Tot (whole_s i pi)
let link_s = (fun #i #pi c p -> (fun _ -> p c))

val link_t  : (#i:interface) -> (#pi:monitorable_prop) -> ctx_t i ->
              prog_t i pi -> Tot (whole_t i)
let link_t #i #pi c p : whole_t i = (fun _ -> p (instrument i pi c))

let test #i #pi p c : IIO (maybe i.ret) pi (fun _ -> True) (fun _ _ _ -> True) =
  (_IIOwp_as_IIO
    (fun _ -> iio_pre pi)
    (fun _ h r lt -> iio_post pi h r lt)
    p) (instrument i pi c)

let awesome
  (#i : interface)
  (#pi : monitorable_prop)
  (p : prog_s i pi)
  (c : ctx_s i pi) :
  Lemma (
      let t = (reify (p c) [] (fun r lt -> iio_post pi [] r lt)) in
     (iio_interpretation t [] (fun r lt -> iio_post pi [] r lt))
    )
  = 
   let t = (reify (p c) [] (fun r lt -> iio_post pi [] r lt)) in ()

open FStar.WellFounded

(**
  The lemma is about computation p being securely compiled.
  The lemma guarantees that computation p after being compiled
  still respects pi.

  Proof: The compilation process preserves the effect IIO and the
  pre- and post-condition until the last step, when there is a
  cast to MIIO, which does not influence the behavior of
  computation p.
  
  Just a note here about the Beh function. We did not know how to
  define it when silent steps were involved. For io we had a Beh
  function, but for io+exn, not. That's why we try to do the proof
  using only the interpretation, because during the process of 
  compilation, not much is changed. 
**)

  // IIOwp (maybe 'b) (fun h p ->
  //   (~(pre x h) ==> p (Inr Contract_failure) []) /\
  //   (pre x h ==> (forall r lt. post x h r lt ==> p (Inl r) lt)))

let interp = iio_interpretation

let lemma_secure_prog_compilation
  (#i  : interface)
  (#pi : monitorable_prop)
  (ps  : prog_s i pi)
  (cs : ctx_s i pi) : 
  IIOwp (maybe i.ret) (fun h p -> 
    (~(iio_pre pi h) ==> p (Inr (Contract_failure)) []) /\
      (iio_pre pi h ==>
        (forall r lt. iio_post pi h r lt ==> p (Inl r) lt))) =
    let pt = _IIOwp_as_IIO (fun _ h -> iio_pre pi h) (fun _ h r lt -> iio_post pi h r lt) ps in
    let wt = (**IIOwp.**)reify (pt cs) [] (fun r lt -> 
	    (~(iio_pre pi []) ==> r == (Inr Contract_failure) /\ lt == []) /\
	    (iio_pre pi [] ==> iio_post pi [] r lt)) in
     (** because (pt c) is in MIIO, we lose that it respects the interpretation **)
    assert (interp wt [] (fun r lt -> 
	    (~(iio_pre pi []) ==> r == (Inr Contract_failure) /\ lt == []) /\
	    (iio_pre pi [] ==> iio_post pi [] r lt)));
	    (**
    let pt' : ctx_s i pi -> MIIO (maybe i.ret) = pt in
    let wt' = (**MIIO.**)reify (pt' cs) [] (fun r lt -> True) in
    assume (interp wt' [] (fun r lt -> 
	    (~(iio_pre pi []) ==> r == (Inr Contract_failure) /\ lt == []) /\
	    (iio_pre pi [] ==> iio_post pi [] r lt)));

    let pt'' = compile_prog ps in
    (** this two are not equal because one is in IIOwp and the other in MIIO **)
(**    assert ((pt <: ctx_s i pi -> MIIO (maybe i.ret)) == pt') by (
           norm [delta_only[`%compile_prog;`%_IIOwp_as_MIIO]];
	   norm [iota]);**)**)
	 _ by (dump "h");
	 pt cs
  
     

let lemma_secure_prog_compilation
  (#i  : interface)
  (#pi : monitorable_prop)
  (p  : prog_s i pi)
  (c : ctx_s i pi) :
     Lemma (
     	let ws = (**IIO.**)reify (p c) [] (fun r lt -> iio_post pi [] r lt) in
     	interp ws [] (fun r lt -> iio_post pi [] r lt) ==> (
	let pt = compile_prog p in
	let wt = (**MIIO.**)reify (pt c) [] (fun r lt -> True) in
	(** the problem is that because (pt c) is in MIIO, we lose the fact that it respects
	    the interpretation **)
	interp wt [] (fun r lt -> 
	    (~(iio_pre pi []) ==> r == (Inr Contract_failure) /\ lt == []) /\
	    (iio_pre pi [] ==> iio_post pi [] r lt))
     )) =
     	let pt = compile_prog p in
	(** p is not equal with pt because of the following:
	    1. pt adds a runtime checks that calls get_trace (). we are intersted in this 
	       equality when the history is empty, therefore we should add a precondition
	       stating that
	    2. the output type of p is (t), but the output type for pt is (maybe t).
	**)
	assert (p == pt) by (
           norm [delta_only[`%compile_prog;`%_IIOwp_as_MIIO;`%_IIOwp_as_IIO]];
           norm [iota];
	   dump "h");
	()


let lemma_secure_prog_compilation
  (#i  : interface)
  (#pi : monitorable_prop)
  (p  : prog_s i pi)
  (c : ctx_s i pi) :
    Lemma (True) =
      let p'' = _IIOwp_as_IIO (fun _ -> iio_pre pi) (fun _ h r lt -> iio_post pi h r lt) p in
      let t = reify (p'' c) [] (fun r lt -> iio_post pi [] r lt) in

      let p' = compile_prog p in

      // I want to show that p' is functional extensional with p''
      // p' has a more general weakest precondition
      // p''

      // assert (p' == p'')
      //   by (
      //     norm [delta_only[`%compile_prog;`%_IIOwp_as_MIIO]];
      //     norm [iota];
      //     dump "x");
      let t' = reify (p' c) [] (fun r lt -> iio_post pi [] r lt) in
      assume (iio_interpretation t' [] (fun r lt -> iio_post pi [] r lt));
      ()

// TODO:
// should prove a lemma like this:
// pre-condition: p is in IIO
// post-condition: forall c. iio_interpretation (compile_prog p c) [] (post pi)

// TODO:
// should prove a lemma like this:
// pre-condition: p was compiled from IIO
// post-condition: iio_interpretation (reify (link_t c p) ()) [] (post pi)

// then we can define a behavior function and try to
// show that iio_interpretation implies it
// Cezar and Exe did this in previous version
