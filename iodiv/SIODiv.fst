module SIODiv

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc
open Util
open Itree

(** SIODiv

    In this file we define a simple version of the IODiv effect for I/O and
    non-termination.
    This effect is simpler in the sense that its associated effect observation
    is not strong enough to express a termination predicate.
    It supports a divergence predicate however.

*)

(** Monad instance

   Without GetTrace for now

*)

assume val file_descr : eqtype

type cmds = | Openfile | Read | Close

unfold let io_args cmd : eqtype =
  match cmd with
  | Openfile -> string
  | Read -> file_descr
  | Close -> file_descr

unfold let io_res cmd : eqtype =
  match cmd with
  | Openfile -> file_descr
  | Read -> string
  | Close -> unit

let io_op_sig : op_sig cmds = {
  args = io_args ;
  res = io_res
}

unfold
let iotree a = itree cmds io_op_sig a

unfold
let iopos = ipos cmds io_op_sig

unfold
let iochoice = ichoice cmds io_op_sig

unfold
let ioret #a (x : a) : iotree a =
  ret x

(**
  Spec with trace
  The trace contains the response of the environment, in fact it is a subset of
  positions where Tau steps are ignored.

  This specification if enough to talk about non-termination of a program
  with respect to its interaction with the environment.
*)

let trace = list (c: iochoice { c <> Tau_choice })

let rec ipos_trace (p : iopos) : trace =
  match p with
  | [] -> []
  | Tau_choice :: p -> ipos_trace p
  | Call_choice o x y :: p -> Call_choice o x y :: ipos_trace p

let rec ipos_trace_append (p q : iopos) :
  Lemma (ensures ipos_trace (p @ q) == ipos_trace p @ ipos_trace q) (decreases p)
= match p with
  | [] -> ()
  | Tau_choice :: p -> ipos_trace_append p q
  | Call_choice o x y :: p -> ipos_trace_append p q

unfold
let wpost a = trace -> option a -> Type0

let twp a = wpost a -> Type0

let wret #a (x : a) : twp a =
  fun post -> post [] (Some x)

let shift_post #a (tr : trace) (post : wpost a) : wpost a =
  fun tr' x -> post (tr @ tr') x

let wbind #a #b (w : twp a) (f : a -> twp b) : twp b =
  fun post ->
    w (fun tr v ->
      match v with
      | Some x -> f x (shift_post tr post)
      | None -> post tr None
    )

let stronger_twp #a (wp1 wp2 : twp a) : Type0 =
  forall post. wp1 post ==> wp2 post

(** Effect observation *)
let theta #a (t : iotree a) =
  fun post ->
    (forall p. isRet (t p) ==> post (ipos_trace p) (Some (ret_val (t p)))) /\
    (forall p. isEvent (t p) ==> post (ipos_trace p) None)

let iodiv a (w : twp a) =
  t: iotree a { w `stronger_twp` theta t }

let iodiv_ret a (x : a) : iodiv a (wret x) =
  ret x

let iodiv_bind a b w wf (m : iodiv a w) (f : (x:a) -> iodiv b (wf x)) : iodiv b (wbind w wf) =
  assert (forall (post : wpost a). w post ==> theta m post) ;
  assert (forall (post : wpost b) x. wf x post ==> theta (f x) post) ;

  // ret
  forall_intro (find_ret_Some_pos m []) ;
  forall_intro_2 ipos_trace_append ;
  forall_intro (find_ret_prefix_val m []) ;
  assert (forall (post : wpost b) p. wbind w wf post ==> isRet (bind m f p) ==> post (ipos_trace p) (Some (ret_val (bind m f p)))) ;

  // event.ret
  assert (forall (post : wpost b) p. wbind w wf post ==> isEvent (bind m f p) ==> Some? (find_ret m [] p) ==> post (ipos_trace p) None) ;

  // event.noret
  assert (forall (post : wpost b) p.
    wbind w wf post ==>
    isEvent (bind m f p) ==>
    None? (find_ret m [] p) ==>
    isEvent (m p)
  ) ;
  assert (forall (post : wpost b) p. wbind w wf post ==> isEvent (bind m f p) ==> None? (find_ret m [] p) ==> post (ipos_trace p) None) ;

  // event
  assert (forall (post : wpost b) p. wbind w wf post ==> isEvent (bind m f p) ==> post (ipos_trace p) None) ;

  assert (forall (post : wpost b). wbind w wf post ==> theta (bind m f) post) ;
  bind m f

let wtau #a (w : twp a) : twp a =
  fun post -> post [] None /\ w post

let iodiv_tau #a #w (m : iodiv a w) : iodiv a (wtau w) =
  tau m

let wcall #a (o : cmds) (x : io_args o) (w : io_res o -> twp a) : twp a =
  fun post -> post [] None /\ (forall y. w y (shift_post [ Call_choice o x y ] post))

let iodiv_call #a (o : cmds) (x : io_args o) #w (k : (r : io_res o) -> iodiv a (w r)) : iodiv a (wcall o x w) =
  call o x k

let rec wrepeat_trunc (w : twp unit) (n : nat) : twp unit =
  if n = 0
  then fun post -> True
  else wbind w (fun (_:unit) -> wtau (wrepeat_trunc w (n - 1)))

let wrepeat (w : twp unit) : twp unit =
  fun post -> forall n. wrepeat_trunc w n post

let rec repeat_any_ret_event_post #w (body : iodiv unit w) (pl : list iopos) p :
  Lemma
    (requires forall pp. mem pp pl ==> isRet (body pp))
    (ensures forall (post : wpost unit).
      wrepeat_trunc w (1 + length pl) post ==>
      isEvent (body p) ==>
      post (ipos_trace (flatten_sep [Tau_choice] pl @ p)) None
    )
    (decreases pl)
= match pl with
  | [] -> ()
  | pp :: pl ->
    repeat_any_ret_event_post body pl p ;
    calc (==) {
      ipos_trace (flatten_sep [Tau_choice] (pp :: pl) @ p) ;
      == {}
      ipos_trace ((pp @ Tau_choice :: flatten_sep [Tau_choice] pl) @ p) ;
      == { forall_intro_3 (append_assoc #iochoice) }
      ipos_trace (pp @ Tau_choice :: flatten_sep [Tau_choice] pl @ p) ;
      == { forall_intro_2 ipos_trace_append }
      ipos_trace pp @ ipos_trace (Tau_choice :: flatten_sep [Tau_choice] pl @ p) ;
      == {}
      ipos_trace pp @ ipos_trace (flatten_sep [Tau_choice] pl @ p) ;
    }

let rec repeat_any_ret_ret_post #w (body : iodiv unit w) (pl : list iopos) p :
  Lemma
    (requires forall pp. mem pp pl ==> isRet (body pp))
    (ensures forall (post : wpost unit).
      wrepeat_trunc w (1 + length pl) post ==>
      isRet (body p) ==>
      post (ipos_trace (flatten_sep [Tau_choice] pl @ p)) None
    )
    (decreases pl)
= match pl with
  | [] ->
    assert (forall (post : wpost unit).
      wrepeat_trunc w 1 post ==>
      isRet (body p) ==>
      wtau (wrepeat_trunc w 0) (shift_post (ipos_trace p) post)
    )
  | pp :: pl ->
    repeat_any_ret_ret_post body pl p ;
    assert (forall (post : wpost unit).
      wrepeat_trunc w (1 + length pl) post ==>
      isRet (body p) ==>
      post (ipos_trace (flatten_sep [Tau_choice] pl @ p)) None
    ) ;
    assert (forall (post : wpost unit).
      wrepeat_trunc w (1 + length pl) (shift_post (ipos_trace pp) post) ==>
      isRet (body p) ==>
      shift_post (ipos_trace pp) post (ipos_trace (flatten_sep [Tau_choice] pl @ p)) None
    ) ;
    calc (==) {
      ipos_trace (flatten_sep [Tau_choice] (pp :: pl) @ p) ;
      == {}
      ipos_trace ((pp @ Tau_choice :: flatten_sep [Tau_choice] pl) @ p) ;
      == { forall_intro_3 (append_assoc #iochoice) }
      ipos_trace (pp @ Tau_choice :: flatten_sep [Tau_choice] pl @ p) ;
      == { forall_intro_2 ipos_trace_append }
      ipos_trace pp @ ipos_trace (Tau_choice :: flatten_sep [Tau_choice] pl @ p) ;
      == {}
      ipos_trace pp @ ipos_trace (flatten_sep [Tau_choice] pl @ p) ;
    } ;
    assert (forall (post : wpost unit).
      wrepeat_trunc w (1 + length pl) (shift_post (ipos_trace pp) post) ==>
      isRet (body p) ==>
      post (ipos_trace (flatten_sep [Tau_choice] (pp :: pl) @ p)) None
    ) ;
    assert (forall (post : wpost unit).
      wrepeat_trunc w (2 + length pl) post ==>
      isRet (body p) ==>
      post (ipos_trace (flatten_sep [Tau_choice] (pp :: pl) @ p)) None
    )

let rec iodiv_repeat_proof_gen #w (body : iodiv unit w) (pl : list iopos) p :
  Lemma
    (requires forall pp. mem pp pl ==> isRet (body pp))
    (ensures forall (post : wpost unit).
      wrepeat w post ==>
      isEvent (repeat body (flatten_sep [Tau_choice] pl @ p)) ==>
      post (ipos_trace (flatten_sep [Tau_choice] pl @ p)) None
    )
    (decreases p)
= match find_ret body [] p with
  | Some ((), q) ->
    assert (isRet (body (find_ret_prefix body [] p))) ;
    find_ret_Some_pos body [] p ;
    assert (p == find_ret_prefix body [] p @ q) ;
    begin match q with
    | [] ->
      repeat_any_ret body pl p ;
      repeat_unfold_1 body ;
      assert (repeat body p == Some Tau) ;
      repeat_any_ret_ret_post body pl p ;
      assert (isRet (body p)) ;
      assert (forall (post : wpost unit). wrepeat w post ==> wrepeat_trunc w (1 + length pl) post) ;
      assert (forall (post : wpost unit).
        wrepeat w post ==>
        isEvent (repeat body p) ==>
        post (ipos_trace (flatten_sep [Tau_choice] pl @ p)) None
      )
    | Tau_choice :: r ->
      forall_intro (mem_append pl [find_ret_prefix body [] p]) ;
      assert (forall pp. mem pp (pl @ [find_ret_prefix body [] p]) ==> isRet (body pp)) ;
      assert (p == find_ret_prefix body [] p @ Tau_choice :: r) ;
      forall_intro_3 (append_assoc #iochoice) ;
      forall_intro_2 (flatten_sep_append #iochoice [Tau_choice]) ;
      assert (flatten_sep [Tau_choice] (pl @ [find_ret_prefix body [] p]) == flatten_sep [Tau_choice] pl @ flatten_sep [Tau_choice] [find_ret_prefix body [] p]) ;
      assert (flatten_sep [Tau_choice] [find_ret_prefix body [] p] == find_ret_prefix body [] p @ [Tau_choice] @ flatten_sep [Tau_choice] []) ;
      flatten_sep_nil #iochoice [Tau_choice] ;
      assert (flatten_sep [Tau_choice] pl @ p == flatten_sep [Tau_choice] (pl @ [find_ret_prefix body [] p]) @ r) ;
      find_ret_smaller body [] p ;
      iodiv_repeat_proof_gen body (pl @ [find_ret_prefix body [] p]) r
    | c :: r -> repeat_any_ret body pl p ; repeat_unfold_1 body
    end
  | None ->
    repeat_any_ret body pl p ;
    repeat_any_ret_event_post body pl p ;
    assert (forall (post : wpost unit). wrepeat w post ==> wrepeat_trunc w (1 + length pl) post) ;
    repeat_unfold_1 body ;
    assert (
      isEvent (repeat body p) ==> isEvent (body p)
    ) ;
    assert (forall (post : wpost unit).
      wrepeat w post ==>
      isEvent (repeat body p) ==>
      post (ipos_trace (flatten_sep [Tau_choice] pl @ p)) None
    )

let iodiv_repeat_proof #w (body : iodiv unit w) p :
  Lemma (forall (post : wpost unit).
    wrepeat w post ==>
    isEvent (repeat body p) ==>
    post (ipos_trace p) None
  )
= iodiv_repeat_proof_gen body [] p

let iodiv_repeat #w (body : iodiv unit w) : iodiv unit (wrepeat w) =
  forall_intro (repeat_not_ret body) ;
  forall_intro (iodiv_repeat_proof body) ;
  repeat body

// We can also "inline" the induction by asking the SMT to prove (p n ==> p (n+1)) which might work sometimes

(**

  Alternatively, we propose a definition of iodiv_repeat using an invariant.
  The invariant is relative to the predicate transformer of the body.
  It must hold for the empty list / root position because postconditions
  must be downward closed.

*)

let trace_invariant (w : twp unit) (inv : trace -> Type0) =
  inv [] /\
  (forall tr. inv tr ==> w (fun tr' v -> inv (tr @ tr') /\ Some? v))

let wrepeat_with_inv (w : twp unit) (inv : trace -> Type0) : twp unit =
  fun post -> forall tr. inv tr ==> post tr None

let invpost (inv : trace -> Type0) : wpost unit =
  fun tr v -> inv tr /\ None? v

// Maybe prove it on the effect observation directly
let rec wrepeat_inv_trunc (w : twp unit) (inv : trace -> Type0) n :
  Lemma (
    trace_invariant w inv ==>
    wrepeat_trunc w n (invpost inv)
  )
= if n = 0
  then ()
  else begin
    wrepeat_inv_trunc w inv (n - 1) ;
    assume (
      trace_invariant w inv ==>
      wrepeat_trunc w (n-1) (invpost inv) ==>
      wbind w (fun (_:unit) -> wtau (wrepeat_trunc w (n - 1))) (invpost inv)
      // ==
      // w (fun tr v ->
      //   match v with
      //   | Some x -> (fun (_:unit) -> wtau (wrepeat_trunc w (n - 1))) x (shift_post tr (invpost inv))
      //     == wtau (wrepeat_trunc w (n - 1)) (shift_post tr (invpost inv))
      //   | None -> invpost inv tr None // == inv tr
      // )
    ) ;
    assume (forall (post : wpost unit).
      wbind w (fun (_:unit) -> wtau (wrepeat_trunc w (n - 1))) post ==>
      wrepeat_trunc w n post
    ) ; // why??
    assert (
      trace_invariant w inv ==>
      wrepeat_trunc w (n-1) (invpost inv) ==>
      wrepeat_trunc w n (invpost inv)
    )
  end

// Some specifications

let diverges #a : wpost a =
  fun tr v -> None? v

// Should be p1 ==> p2 rather than ==
let rec wrepeat_trunc_ext w n (p1 p2 : wpost unit) :
  Lemma ((forall tr x. p1 tr x == p2 tr x) ==> wrepeat_trunc w n p1 == wrepeat_trunc w n p2)
= if n = 0
  then ()
  else begin
    // wrepeat_trunc_ext w (n-1) p1 p2 ;
    // assume ((forall tr x. p1 tr x == p2 tr x) ==> wbind w (fun _ -> wrepeat_trunc w (n -1)) p1 == wbind w (fun _ -> wrepeat_trunc w (n -1)) p2)
    // assert (wrepeat_trunc w n == wbind w (fun _ -> wrepeat_trunc w (n -1))) ; // Isn't this by def??
    assume ((forall tr x. p1 tr x == p2 tr x) ==> wrepeat_trunc w n p1 == wrepeat_trunc w n p2)
  end

let repeat_ret_loops () :
  Lemma (wrepeat (wret ()) diverges)
= let rec aux n :
    Lemma (wrepeat_trunc (wret ()) n diverges) [SMTPat ()]
  = if n = 0
    then ()
    else begin
      aux (n - 1) ;
      wrepeat_trunc_ext (wret ()) (n-1) (shift_post [] diverges) (diverges #unit)
    end
  in
  ()

// Much better
let repeat_ret_loops_with_inv () :
  Lemma (wrepeat_with_inv (wret ()) (fun _ -> True) diverges)
= ()

[@@allow_informative_binders]
reifiable total layered_effect {
  SIODiv : a:Type -> twp a -> Effect
  with
    repr   = iodiv ;
    return = iodiv_ret ;
    bind   = iodiv_bind
    // tau    = iodiv_tau ; // Universe problems
    // call   = iodiv_call
}