module IODiv

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc
open FStar.FunctionalExtensionality
open Util
open Stream
open Itree

(** IODiv

    In this file we define a more complete version of the IODiv effect for I/O and
    non-termination than in SIODiv.

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
let ionode = inode cmds io_op_sig

unfold
let iochoice = ichoice cmds io_op_sig

unfold
let iopostream = postream cmds io_op_sig

unfold
let ioret #a (x : a) : iotree a =
  ret x

(**
  Spec with trace
  The trace contains the response of the environment, in fact it is a subset of
  positions where Tau steps are ignored.

  For non-termination however, we make use of potentially infinite traces.
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

(** Up to tau relation on position streams *)
let embeds (p q : iopostream) =
  forall n. exists m. ipos_trace (stream_trunc q n) == ipos_trace (stream_trunc p m)

let uptotau (p q : iopostream) =
  p `embeds` q /\ q `embeds` p

let uptotau_refl (p : iopostream) :
  Lemma (p `uptotau` p)
= ()

let uptotau_sym (p q : iopostream) :
  Lemma (requires p `uptotau` q) (ensures q `uptotau` p)
= ()

let uptotau_trans (p q r : iopostream) :
  Lemma (requires p `uptotau` q /\ q `uptotau` r) (ensures p `uptotau` r)
= ()

// Could also be proved without using extensionality
let feq_uptotau (p q : iopostream) :
  Lemma
    (requires p `feq` q)
    (ensures p `uptotau` q)
= stream_ext p q

let embeds_trace_implies (pr : trace -> Type0) (p p' : iopostream) :
  Lemma
    (requires p `embeds` p' /\ (forall n. pr (ipos_trace (stream_trunc p n))))
    (ensures forall n. pr (ipos_trace (stream_trunc p' n)))
= ()

noeq
type branch a =
| Fin : tr:trace -> res:a -> branch a
| Inf : p : iopostream -> branch a

unfold
let wpost a = branch a -> Type0

let twp a = wpost a -> Type0

let wret #a (x : a) : twp a =
  fun post -> post (Fin [] x)

let rec trace_to_pos (tr : trace) : iopos =
  match tr with
  | [] -> []
    | c :: tr -> c :: trace_to_pos tr

let shift_post #a (tr : trace) (post : wpost a) : wpost a =
  fun b ->
    match b with
    | Fin tr' x -> post (Fin (tr @ tr') x)
    | Inf p -> forall (p' : iopostream). stream_prepend (trace_to_pos tr) p `uptotau` p' ==> post (Inf p')

let wbind #a #b (w : twp a) (wf : a -> twp b) : twp b =
  fun post ->
    w (fun b ->
      match b with
      | Fin tr x -> wf x (shift_post tr post)
      | Inf p -> post (Inf p)
    )

let stronger_twp #a (wp1 wp2 : twp a) : Type0 =
  forall post. wp1 post ==> wp2 post

unfold
let event_stream #a (t : iotree a) (p : iopostream) =
  forall n. isEvent (t (stream_trunc p n))

(** Effect observation *)
let theta #a (t : iotree a) =
  fun post ->
    (forall p. isRet (t p) ==> post (Fin (ipos_trace p) (ret_val (t p)))) /\
    (forall (p p' : iopostream). event_stream t p ==> p `uptotau` p' ==> post (Inf p'))

let iodiv a (w : twp a) =
  t: iotree a { w `stronger_twp` theta t }

let iodiv_ret a (x : a) : iodiv a (wret x) =
  assert (forall p. ~ (isEvent (ioret x p))) ;
  assert (forall (p : iopostream). ~ (isEvent (ioret x (stream_trunc p 0)))) ;
  ret x

let iodiv_bind_fin a b w wf (m : iodiv a w) (f : (x:a) -> iodiv b (wf x)) :
  Lemma (forall (post : wpost b) p. wbind w wf post ==> isRet (bind m f p) ==> post (Fin (ipos_trace p) (ret_val (bind m f p))))
= let aux (post : wpost b) p :
    Lemma
      (requires wbind w wf post /\ isRet (bind m f p))
      (ensures post (Fin (ipos_trace p) (ret_val (bind m f p))))
      [SMTPat ()]
    = calc (==>) {
        True ;
        ==> {}
        Some? (find_ret m [] p) == true ;
        ==> {}
        isRet (m (find_ret_prefix m [] p)) == true ;
        ==> {}
        wf (ret_val (m (find_ret_prefix m [] p))) (shift_post (ipos_trace (find_ret_prefix m [] p)) post) ;
        ==> {}
        theta (f (ret_val (m (find_ret_prefix m [] p)))) (shift_post (ipos_trace (find_ret_prefix m [] p)) post) ;
        ==> { find_ret_prefix_val m [] p }
        theta (f (find_ret_val m [] p)) (shift_post (ipos_trace (find_ret_prefix m [] p)) post) ;
        ==> { assert (isRet (f (find_ret_val m [] p) (find_ret_pos m [] p))) }
        shift_post (ipos_trace (find_ret_prefix m [] p)) post (Fin (ipos_trace (find_ret_pos m [] p)) (ret_val (f (find_ret_val m [] p) (find_ret_pos m [] p)))) ;
        ==> {}
        shift_post (ipos_trace (find_ret_prefix m [] p)) post (Fin (ipos_trace (find_ret_pos m [] p)) (ret_val (bind m f p))) ;
        ==> {}
        post (Fin (ipos_trace (find_ret_prefix m [] p) @ ipos_trace (find_ret_pos m [] p)) (ret_val (bind m f p))) ;
        ==> { forall_intro_2 ipos_trace_append }
        post (Fin (ipos_trace (find_ret_prefix m [] p @ find_ret_pos m [] p)) (ret_val (bind m f p))) ;
        ==> { find_ret_Some_pos m [] p }
        post (Fin (ipos_trace p) (ret_val (bind m f p))) ;
      }
    in ()

let finite_branch_prefix #a #b (m : iotree a) (f : a -> iotree b) (p : iopostream) :
  Lemma
    (requires
      (exists n. ~ (isEvent (m (stream_trunc p n)))) /\
      event_stream (bind m f) p
    )
    (ensures
      exists (q : iopos) (s : iopostream).
        p `feq` stream_prepend q s /\
        isRet (m q)
    )
= let n = indefinite_description_ghost_nat_min (fun n -> ~ (isEvent (m (stream_trunc p n)))) in
  // We know before n we only have events, and n is not an event: this leaves us
  // with either Some Ret, or None, we first show the latter is not possible
  match m (stream_trunc p n) with
  | None ->
    begin match find_ret m [] (stream_trunc p n) with
    | Some (x, q) ->
      find_ret_prefix_prefix_of m [] (stream_trunc p n) ;
      prefix_of_stream_trunc p n (find_ret_prefix m [] (stream_trunc p n))
    | None -> ()
    end
  | Some (Ret x) -> stream_trunc_drop n p

let event_stream_bind #a #b (m : iotree a) (f : a -> iotree b) (p : iopostream) (q : iopos) (s : iopostream) :
  Lemma
    (requires event_stream (bind m f) p /\ p `feq` stream_prepend q s /\ isRet (m q))
    (ensures event_stream (f (ret_val (m q))) s)
= let aux (p : iopostream) (q : iopos) (s : iopostream) (i : nat) :
    Lemma (event_stream (bind m f) p ==> p `feq` stream_prepend q s ==> isRet (m q) ==> isEvent (f (ret_val (m q)) (stream_trunc s i))) [SMTPat ()]
  = assert (event_stream (bind m f) p ==> isEvent (bind m f (stream_trunc p (length q + i)))) ;
    stream_trunc_ext p (stream_prepend q s) (length q + i) ;
    assert (event_stream (bind m f) p ==> p `feq` stream_prepend q s ==> isEvent (bind m f (stream_trunc (stream_prepend q s) (length q + i)))) ;
    stream_prepend_trunc_right q s (length q + i) ;
    assert (event_stream (bind m f) p ==> p `feq` stream_prepend q s ==> isEvent (bind m f (q @ stream_trunc s i))) ;
    find_ret_append m ;
    assert (isRet (m q) ==> find_ret m [] (q @ stream_trunc s i) == Some (ret_val (m q), stream_trunc s i))
  in ()

let shift_post_Inf_spe #a tr s p (post : wpost a) :
  Lemma
    (requires shift_post tr post (Inf s) /\ stream_prepend (trace_to_pos tr) s `uptotau` p)
    (ensures post (Inf p))
= ()

// let rec ipos_trace_fst_splitAt (p : iopos) (n : nat) :
//   Lemma (ipos_trace (fst (splitAt n p)) == fst (splitAt (length (ipos_trace (fst (splitAt n p)))) (ipos_trace p)))
// = match n, p with
//   | 0, _ -> ()
//   | _, [] -> ()
//   | _, Tau_choice :: p' -> ipos_trace_fst_splitAt p' (n - 1)
//   | _, x :: p' -> ipos_trace_fst_splitAt p' (n - 1)

let rec ipos_trace_firstn_eq (p q : iopos) (n : nat) :
  Ghost nat
    (requires ipos_trace p == ipos_trace q)
    (ensures fun m -> ipos_trace (firstn n p) == ipos_trace (firstn m q) /\ m <= length q)
= if n = 0
  then 0
  else begin
    match p with
    | [] -> 0
    | Tau_choice :: p' -> ipos_trace_firstn_eq p' q (n-1)
    | c :: p' ->
      begin match q with
      | Tau_choice :: q' -> 1 + ipos_trace_firstn_eq p q' n
      | c' :: q' -> 1 + ipos_trace_firstn_eq p' q' (n-1)
      end
  end

let stream_prepend_embeds (p q : iopos) (s : iopostream) :
  Lemma
    (requires ipos_trace p == ipos_trace q)
    (ensures stream_prepend p s `embeds` stream_prepend q s)
= let aux n :
    Lemma (exists m. ipos_trace (stream_trunc (stream_prepend q s) n) == ipos_trace (stream_trunc (stream_prepend p s) m)) [SMTPat ()]
  = if n <= length q
    then begin
      let m = ipos_trace_firstn_eq q p n in
      calc (==) {
        ipos_trace (stream_trunc (stream_prepend q s) n) ;
        == { stream_prepend_trunc_left q s n }
        ipos_trace (firstn n q) ;
        == {}
        ipos_trace (firstn m p) ;
        == { stream_prepend_trunc_left p s m }
        ipos_trace (stream_trunc (stream_prepend p s) m) ;
      }
    end
    else begin
      calc (==) {
        ipos_trace (stream_trunc (stream_prepend q s) n) ;
        == { stream_prepend_trunc_right q s n }
        ipos_trace (q @ stream_trunc s (n - length q)) ;
        == { forall_intro_2 ipos_trace_append }
        ipos_trace q @ ipos_trace (stream_trunc s (n - length q)) ;
        == {}
        ipos_trace p @ ipos_trace (stream_trunc s (n - length q)) ;
        == {}
        ipos_trace p @ ipos_trace (stream_trunc s ((length p + n - length q) - length p)) ;
        == { forall_intro_2 ipos_trace_append }
        ipos_trace (p @ stream_trunc s ((length p + n - length q) - length p)) ;
        == { stream_prepend_trunc_right p s (length p + n - length q) }
        ipos_trace (stream_trunc (stream_prepend p s) (length p + n - length q)) ;
      }
    end
  in ()

let stream_prepend_uptotau (p q : iopos) (s : iopostream) :
  Lemma
    (requires ipos_trace p == ipos_trace q)
    (ensures stream_prepend p s `uptotau` stream_prepend q s)
= stream_prepend_embeds p q s ; stream_prepend_embeds q p s

let rec ipos_trace_to_pos (tr : trace) :
  Lemma (ipos_trace (trace_to_pos tr) == tr)
= match tr with
  | [] -> ()
  | c :: tr' -> ipos_trace_to_pos tr'

let iodiv_bind_inf_fin_shift_post #a #b #w #wf (m : iodiv a w) (f : (x:a) -> iodiv b (wf x)) (post : wpost b) (p p' : iopostream) (q : iopos) (s : iopostream) :
  Lemma
    (requires wbind w wf post /\ event_stream (bind m f) p /\ ~ (event_stream m p) /\ p `uptotau` p' /\ p `feq` stream_prepend q s /\ isRet (m q))
    (ensures shift_post (ipos_trace q) post (Inf s))
= calc (==>) {
    True ;
    ==> {}
    theta (f (ret_val (m q))) (shift_post (ipos_trace q) post) ;
    ==> { event_stream_bind m f p q s ; assert (event_stream (f (ret_val (m q))) s) }
    forall (s' : iopostream). s `uptotau` s' ==> shift_post (ipos_trace q) post (Inf s') ;
    ==> {}
    shift_post (ipos_trace q) post (Inf s) ;
  }

let iodiv_bind_inf_fin_upto_aux (s p p' : iopostream) (q : iopos) :
  Lemma
    (requires p `feq` stream_prepend q s /\ p `uptotau` p')
    (ensures stream_prepend (trace_to_pos (ipos_trace q)) s `uptotau` p')
= feq_uptotau p (stream_prepend q s) ;
  ipos_trace_to_pos (ipos_trace q) ;
  stream_prepend_uptotau (trace_to_pos (ipos_trace q)) q s

let iodiv_bind_inf_fin a b w wf (m : iodiv a w) (f : (x:a) -> iodiv b (wf x)) :
  Lemma (forall (post : wpost b) (p p' : iopostream). wbind w wf post ==> event_stream (bind m f) p ==> ~ (event_stream m p) ==> p `uptotau` p' ==> post (Inf p'))
= let aux (post : wpost b) (p p' : iopostream) :
    Lemma
      (requires wbind w wf post /\ event_stream (bind m f) p /\ ~ (event_stream m p) /\ p `uptotau` p')
      (ensures post (Inf p'))
      [SMTPat ()]
  = finite_branch_prefix m f p ;
    assert (exists (q : iopos) (s : iopostream). p `feq` stream_prepend q s /\ isRet (m q)) ;
    // TODO Use eliminate instead?
    let q = indefinite_description_ghost iopos (fun q -> exists (s : iopostream). p `feq` stream_prepend q s /\ isRet (m q)) in
    let s = indefinite_description_ghost iopostream (fun s -> p `feq` stream_prepend q s /\ isRet (m q)) in
    assert (p `feq` stream_prepend q s) ;
    assert (isRet (m q)) ;
    iodiv_bind_inf_fin_shift_post m f post p p' q s ;
    iodiv_bind_inf_fin_upto_aux s p p' q ;
    shift_post_Inf_spe (ipos_trace q) s p' post // weird that it is needed
  in ()

let iodiv_bind a b w wf (m : iodiv a w) (f : (x:a) -> iodiv b (wf x)) : iodiv b (wbind w wf) =
  assert (forall (post : wpost a). w post ==> theta m post) ;
  assert (forall (post : wpost b) x. wf x post ==> theta (f x) post) ;

  // fin
  iodiv_bind_fin a b w wf m f ;

  // inf.fin
  iodiv_bind_inf_fin a b w wf m f ;

  // inf.inf
  assert (forall (post : wpost b) (p p' : iopostream). wbind w wf post ==> event_stream (bind m f) p ==> event_stream m p ==> p `uptotau` p' ==> post (Inf p')) ;

  // inf
  assert (forall (post : wpost b) (p p' : iopostream). wbind w wf post ==> event_stream (bind m f) p ==> p `uptotau` p' ==> post (Inf p')) ;

  assert (forall (post : wpost b). wbind w wf post ==> theta (bind m f) post) ;
  bind m f

let event_stream_tau #a (m : iotree a) (p : iopostream) :
    Lemma
      (requires event_stream (tau m) p)
      (ensures shead p == Tau_choice /\ event_stream m (stail p))
= assert (isEvent (tau m (stream_trunc p 1))) ;
  assert (shead p == Tau_choice) ;

  let aux n : Lemma (isEvent (m (stream_trunc (stail p) n))) [SMTPat ()] =
    assert (isEvent (tau m (stream_trunc p (n+1)))) ;
    stream_trunc_succ p n
  in ()

let uptotau_prepend_tau (p : iopostream) :
  Lemma (p `uptotau` stream_prepend [Tau_choice] p)
= let aux1 n :
    Lemma
      (exists m. ipos_trace (stream_trunc p n) == ipos_trace (stream_trunc (stream_prepend [Tau_choice] p) m))
      [SMTPat ()]
  = stream_prepend_trunc [Tau_choice] p (n+1) ;
    assert (stream_trunc (stream_prepend [Tau_choice] p) (n+1) == Tau_choice :: stream_trunc p n)
  in
  let aux2 n :
    Lemma
      (exists m. ipos_trace (stream_trunc p m) == ipos_trace (stream_trunc (stream_prepend [Tau_choice] p) n))
      [SMTPat ()]
  = if n = 0
    then ()
    else stream_prepend_trunc [Tau_choice] p n
  in ()

let iodiv_tau (a:Type) w (m : iodiv a w) : iodiv a w =

  // fin
  assert (forall (post : wpost a) p. w post ==> isRet (tau m p) ==> post (Fin (ipos_trace p) (ret_val (tau m p)))) ;

  // inf
  let aux_inf (post : wpost a) (p p' : iopostream) :
    Lemma
      (requires w post /\ event_stream (tau m) p /\ p `uptotau` p')
      (ensures post (Inf p'))
      [SMTPat ()]
    = event_stream_tau m p ;
      assert (forall q. stail p `uptotau` q ==> post (Inf q)) ;
      feq_head_tail p ;
      assert (p `feq` stream_prepend [shead p] (stail p)) ;
      feq_uptotau p (stream_prepend [Tau_choice] (stail p)) ;
      uptotau_prepend_tau (stail p) ;
      assert (stail p `uptotau` stream_prepend [Tau_choice] (stail p)) ;
      assert (stail p `uptotau` p')
  in

  assert (forall (post : wpost a). w post ==> theta (tau m) post) ;
  tau m

let wcall #a (o : cmds) (x : io_args o) (w : io_res o -> twp a) : twp a =
  fun post -> forall y. w y (shift_post [ Call_choice o x y ] post)

let isCall_choice (o : cmds) (x : io_args o) (t : iochoice) =
  match t with
  | Call_choice o' x' y -> o = o' && x = x'
  | _ -> false

let call_choice_res (o : cmds) (x : io_args o) (t : iochoice) :
  Pure (io_res o) (requires isCall_choice o x t) (ensures fun _ -> True)
= match t with
  | Call_choice o' x' y -> y

// Essentially the same proof as event_stream_tau
// is there some hope of factorisation?
let event_stream_call #a (o : cmds) (x : io_args o) (k : io_res o -> iotree a) (p : iopostream) :
  Lemma
    (requires event_stream (call o x k) p)
    (ensures isCall_choice o x (shead p) /\ event_stream (k (call_choice_res o x (shead p))) (stail p))
= assert (isEvent (call o x k (stream_trunc p 1))) ;
  assert (isCall_choice o x (shead p)) ;

  let aux n : Lemma (isEvent (k (call_choice_res o x (shead p)) (stream_trunc (stail p) n))) [SMTPat ()] =
    assert (isEvent (call o x k (stream_trunc p (n+1)))) ;
    stream_trunc_succ p n
  in ()

let iodiv_call #a (o : cmds) (x : io_args o) #w (k : (r : io_res o) -> iodiv a (w r)) : iodiv a (wcall o x w) =
  // fin
  assert (forall (post : wpost a) p. wcall o x w post ==> isRet (call o x k p) ==> post (Fin (ipos_trace p) (ret_val (call o x k p)))) ;

  // inf
  let aux_inf (post : wpost a) (p p' : iopostream) :
    Lemma
      (requires wcall o x w post /\ event_stream (call o x k) p /\ p `uptotau` p')
      (ensures post (Inf p'))
      [SMTPat ()]
    = event_stream_call o x k p ;
      assert (w (call_choice_res o x (shead p)) (shift_post [ Call_choice o x (call_choice_res o x (shead p)) ] post)) ;
      assert (theta (k (call_choice_res o x (shead p))) (shift_post [ Call_choice o x (call_choice_res o x (shead p)) ] post)) ;
      assert (forall q. stail p `uptotau` q ==> shift_post [ Call_choice o x (call_choice_res o x (shead p)) ] post (Inf q)) ;
      assert (shift_post [ Call_choice o x (call_choice_res o x (shead p)) ] post (Inf (stail p))) ;

      feq_head_tail p ;
      assert (stream_prepend [shead p] (stail p) `feq` p) ;
      assert (isCall_choice o x (shead p)) ;
      assert (shead p == Call_choice o x (call_choice_res o x (shead p))) ;
      assert (stream_prepend [ Call_choice o x (call_choice_res o x (shead p)) ] (stail p) `feq` p) ;
      assert (trace_to_pos [ Call_choice o x (call_choice_res o x (shead p)) ] == [ Call_choice o x (call_choice_res o x (shead p)) ]) ;
      assert (stream_prepend [ Call_choice o x (call_choice_res o x (shead p)) ] (stail p) == stream_prepend (trace_to_pos [ Call_choice o x (call_choice_res o x (shead p)) ]) (stail p)) ;
      assert (stream_prepend (trace_to_pos [ Call_choice o x (call_choice_res o x (shead p)) ]) (stail p) `feq` p) ;
      feq_uptotau (stream_prepend (trace_to_pos [ Call_choice o x (call_choice_res o x (shead p)) ]) (stail p)) p ;
      uptotau_trans (stream_prepend (trace_to_pos [ Call_choice o x (call_choice_res o x (shead p)) ]) (stail p)) p p' ;
      assert (stream_prepend (trace_to_pos [ Call_choice o x (call_choice_res o x (shead p)) ]) (stail p) `uptotau` p')
  in

  assert (forall (post : wpost a). wcall o x w post ==> theta (call o x k) post) ;
  call o x k

let rec wrepeat_trunc (w : twp unit) (n : nat) : twp unit =
  if n = 0
  then fun post -> True
  else wbind w (fun (_:unit) -> wrepeat_trunc w (n - 1))

let wrepeat (w : twp unit) : twp unit =
  fun post -> forall n. wrepeat_trunc w n post

// Somehow it should be the concatenation of a stream of finite runs of body
// or a finite number of finite runs followed by an infinite run
// might be easier to produce a colist?
// What is not clear is how to exploit finite information since we are not concluding about
// a finite prefix...
// Might be easier to go directly for a spec with invariants including some
// inv ... ==> post (Inf p)
// with the lhs talking about finite approximations potentially (forall n trunc)
// let event_stream_repeat (body : iotree unit) (p : iopostream) :
//   Lemma
//     (requires event_stream (repeat body) p)
//     (ensures

// let iodiv_repeat #w (body : iodiv unit w) : iodiv unit (wrepeat w) =
//   // fin
//   forall_intro (repeat_not_ret body) ;
//   assert (forall (post : wpost unit) p. wrepeat w post ==> isRet (repeat body p) ==> post (Fin (ipos_trace p) (ret_val (repeat body p)))) ;

//   // inf
//   assume (forall (post : wpost unit) (p p' : iopostream). wrepeat w post ==> event_stream (repeat body) p ==> p `uptotau` p' ==> post (Inf p')) ;

//   assert (forall (post : wpost unit). wrepeat w post ==> theta (repeat body) post) ;
//   repeat body

let loop_preserving (w : twp unit) (inv : trace -> Type0) =
  forall tr.
    inv tr ==>
    w (fun b ->
      match b with
      | Fin tr' x -> inv (tr @ tr')
      | Inf p -> forall n. inv (tr @ ipos_trace (stream_trunc p n))
    )

let downward_closed (inv : trace -> Type0) =
  forall tr tr'. tr `prefix_of` tr' ==> inv tr' ==> inv tr

let trace_invariant (w : twp unit) (inv : trace -> Type0) =
  inv [] /\
  downward_closed inv /\
  loop_preserving w inv

let wrepeat_inv (w : twp unit) (inv : trace -> Type0) : twp unit =
  fun post -> forall (p : iopostream). (forall n. inv (ipos_trace (stream_trunc p n))) ==> post (Inf p)

let cons_length #a (x : a) (l : list a) :
  Lemma (length (x :: l) = length l + 1)
= ()

let event_stream_repeat_one_ret_aux_ineq (p0 q' : iopos) (p : iopostream) (n : nat) :
  Lemma
    (requires stream_trunc p n == p0 @ Tau_choice :: q')
    (ensures length (p0 @ [Tau_choice]) <= n)
= calc (==) {
    n ;
    == { stream_trunc_length p n }
    length (stream_trunc p n) ;
    == {}
    length (p0 @ Tau_choice :: q') ;
    == { append_assoc p0 [Tau_choice] q' }
    length ((p0 @ [Tau_choice]) @ q') ;
    == {}
    length (p0 @ [Tau_choice]) + length q' ;
  }

let event_stream_repeat_one_ret_aux_eq (p0 : iopos) (p : iopostream) (m : nat) :
  Lemma
    (requires stream_trunc p (length (p0 @ [Tau_choice])) == p0 @ [Tau_choice])
    (ensures stream_trunc p (length (p0 @ [Tau_choice]) + m) == p0 @ Tau_choice :: (stream_trunc (stream_drop (length (p0 @ [Tau_choice])) p) m))
= stream_trunc_length p (length (p0 @ [Tau_choice])) ;
  calc (==) {
    stream_trunc p (length (p0 @ [Tau_choice]) + m) ;
    == {
      stream_trunc_drop (length (p0 @ [Tau_choice])) p ;
      stream_trunc_ext (stream_prepend (stream_trunc p (length (p0 @ [Tau_choice]))) (stream_drop (length (p0 @ [Tau_choice])) p)) p (length (p0 @ [Tau_choice]) + m)
    }
    stream_trunc (stream_prepend (stream_trunc p (length (p0 @ [Tau_choice]))) (stream_drop (length (p0 @ [Tau_choice])) p)) (length (p0 @ [Tau_choice]) + m) ;
    == {
      stream_prepend_trunc_right (stream_trunc p (length (p0 @ [Tau_choice]))) (stream_drop (length (p0 @ [Tau_choice])) p) (length (p0 @ [Tau_choice]) + m)
    }
    (stream_trunc p (length (p0 @ [Tau_choice]))) @ (stream_trunc (stream_drop (length (p0 @ [Tau_choice])) p) (length (p0 @ [Tau_choice]) + m - length (p0 @ [Tau_choice]))) ;
    == {}
    (stream_trunc p (length (p0 @ [Tau_choice]))) @ (stream_trunc (stream_drop (length (p0 @ [Tau_choice])) p) m) ;
    == {}
    (p0 @ [Tau_choice]) @ (stream_trunc (stream_drop (length (p0 @ [Tau_choice])) p) m) ;
    == { append_assoc p0 [Tau_choice] (stream_trunc (stream_drop (length (p0 @ [Tau_choice])) p) m) }
    p0 @ [Tau_choice] @ (stream_trunc (stream_drop (length (p0 @ [Tau_choice])) p) m) ;
    == {}
    p0 @ Tau_choice :: (stream_trunc (stream_drop (length (p0 @ [Tau_choice])) p) m) ;
  }

let event_stream_repeat_one_ret_aux_eq' (p0 q' : iopos) (p : iopostream) (n : nat) :
  Lemma
    (requires stream_trunc p n == p0 @ Tau_choice :: q')
    (ensures stream_trunc p (length (p0 @ [Tau_choice])) == p0 @ [Tau_choice])
= event_stream_repeat_one_ret_aux_ineq p0 q' p n ;
  calc (==) {
    stream_trunc p (length (p0 @ [Tau_choice])) ;
    == { firstn_stream_trunc_left (length (p0 @ [Tau_choice])) n p }
    firstn (length (p0 @ [Tau_choice])) (stream_trunc p n) ;
    == {}
    firstn (length (p0 @ [Tau_choice])) (p0 @ Tau_choice :: q') ;
    == { append_assoc p0 [Tau_choice] q' }
    firstn (length (p0 @ [Tau_choice])) ((p0 @ [Tau_choice]) @ q') ;
    == { firstn_append_left (length (p0 @ [Tau_choice])) (p0 @ [Tau_choice]) q' }
    firstn (length (p0 @ [Tau_choice])) (p0 @ [Tau_choice]) ;
    == { firstn_all (length (p0 @ [Tau_choice])) (p0 @ [Tau_choice]) }
    p0 @ [Tau_choice] ;
  }

let event_stream_repeat_one_ret (body : iotree unit) (p : iopostream) n q' :
  Lemma
    (requires event_stream (repeat body) p /\ find_ret body [] (stream_trunc p n) == Some ((), Tau_choice :: q'))
    (ensures event_stream (repeat body) (stream_drop (1 + length (find_ret_prefix body [] (stream_trunc p n))) p))
= find_ret_Some_pos body [] (stream_trunc p n) ;
  let aux (p0 : iopos) m :
    Lemma
      (requires isRet (body p0) /\ stream_trunc p n == p0 @ Tau_choice :: q')
      (ensures isEvent (repeat body (stream_trunc (stream_drop (1 + length p0) p) m)))
      [SMTPat ()]
  = calc (==) {
      p0 @ Tau_choice :: q' ;
      == { append_assoc p0 [Tau_choice] q' }
      (p0 @ [Tau_choice]) @ q' ;
    } ;
    event_stream_repeat_one_ret_aux_eq' p0 q' p n ;
    assert (isEvent (repeat body (stream_trunc p (length (p0 @ [Tau_choice]) + m)))) ;
    event_stream_repeat_one_ret_aux_eq p0 p m ;
    assert (isEvent (repeat body (p0 @ Tau_choice :: (stream_trunc (stream_drop (length (p0 @ [Tau_choice])) p) m)))) ;
    repeat_one_ret body ;
    assert (isEvent (repeat body (stream_trunc (stream_drop (length (p0 @ [Tau_choice])) p) m))) ;
    calc (==) {
      length (p0 @ [Tau_choice]) ;
      == { append_length p0 [Tau_choice] }
      length p0 + 1 ;
      == {}
      1 + length p0 ;
    } ;
    assert (isEvent (repeat body (stream_trunc (stream_drop (1 + length p0) p) m)))
  in ()

let repeat_inv_proof_aux_eqpos (p : iopostream) (p0 q' : iopos) (n : nat) :
  Lemma
    (requires
      n >= 1 + length p0 /\
      stream_trunc p n == p0 @ Tau_choice :: q'
    )
    (ensures q' == stream_trunc (stream_drop (1 + length p0) p) (n - 1 - length p0))
= calc (==) {
    p0 @ Tau_choice :: q' ;
    == { append_assoc p0 [Tau_choice] q' }
    (p0 @ [Tau_choice]) @ q' ;
  } ;
  calc (==) {
    q' ;
    == { stream_trunc_split_drop n p (p0 @ [Tau_choice]) q' }
    stream_trunc (stream_drop (length (p0 @ [Tau_choice])) p) (length q') ;
    == { append_length p0 [Tau_choice] }
    stream_trunc (stream_drop (length p0 + 1) p) (length q') ;
  } ;
  calc (==) {
    n ;
    == { stream_trunc_length p n }
    length (stream_trunc p n) ;
    == {}
    length ((p0 @ [Tau_choice]) @ q') ;
    == {}
    length (p0 @ [Tau_choice]) + length q' ;
    == { append_length p0 [Tau_choice] }
    length p0 + 1 + length q' ;
  }

let repeat_inv_proof_aux_smaller (body : iotree unit) (n : nat) (p : iopostream) q q' :
  Lemma
    (requires stream_trunc p n == q @ (Tau_choice :: q'))
    (ensures n >= 1 + length q)
= calc (==) {
    n ;
    == { stream_trunc_length p n }
    length (stream_trunc p n) ;
    == {}
    length (q @ (Tau_choice :: q')) ;
    == {}
    length q + length (Tau_choice :: q') ;
    == {}
    length q + length q' + 1 ;
  }

let iodiv_repeat_inv_proof_aux_inf #w (body : iodiv unit w) (inv : trace -> Type0) (tr0 : trace) (post : wpost unit) (p : iopostream) n :
  Lemma
    (requires inv tr0 /\ trace_invariant w inv /\ event_stream (repeat body) p /\ event_stream body p)
    (ensures inv (tr0 @ ipos_trace (stream_trunc p n)))
= assert (p `uptotau` p)

let rec ipos_trace_prefix_of (p q : iopos) :
  Lemma
    (requires p `prefix_of` q)
    (ensures ipos_trace p `prefix_of` ipos_trace q)
= match p with
  | [] -> ()
  | x :: p' ->
    begin match q with
    | y :: q' -> ipos_trace_prefix_of p' q'
    end

let iodiv_repeat_inv_proof_aux_overfin #w (body : iodiv unit w) (inv : trace -> Type0) (tr0 : trace) (post : wpost unit) (p : iopostream) n :
  Lemma
    (requires inv tr0 /\ trace_invariant w inv /\ event_stream (repeat body) p /\ ~ (event_stream body p) /\ find_ret body [] (stream_trunc p n) == None)
    (ensures inv (tr0 @ ipos_trace (stream_trunc p n)))
= // Similar to finite_branch_prefix
  let n0 = indefinite_description_ghost_nat_min (fun n -> ~ (isEvent (body (stream_trunc p n)))) in
  match body (stream_trunc p n0) with
  | None ->
    begin match find_ret body [] (stream_trunc p n0) with
    | Some (x, q) ->
      find_ret_prefix_prefix_of body [] (stream_trunc p n0) ;
      prefix_of_stream_trunc p n0 (find_ret_prefix body [] (stream_trunc p n0))
    | None ->
      assert (isEvent (repeat body (stream_trunc p n0))) ;
      repeat_unfold_1 body ;
      assert (isEvent (bind body (fun _ -> tau ((if length (stream_trunc p n0) = 0 then (fun _ -> loop _) else itree_cofix_unfoldn (repeat_fix body) (length (stream_trunc p n0) - 1)) ())) (stream_trunc p n0)))
    end
  | Some (Ret ()) ->
    assert (isRet (body (stream_trunc p n0))) ;
    assert (inv (tr0 @ ipos_trace (stream_trunc p n0))) ;
    if n < n0
    then begin
      stream_trunc_leq_prefix_of p n n0 ;
      ipos_trace_prefix_of (stream_trunc p n) (stream_trunc p n0) ;
      prefix_of_append_left (ipos_trace (stream_trunc p n)) (ipos_trace (stream_trunc p n0)) tr0
    end
    else begin
      find_ret_append body ;
      assert (Some? (find_ret body [] (stream_trunc p n0 @ skipn n0 (stream_trunc p n)))) ;
      calc (==) {
        stream_trunc p n ;
        == { splitAt_eq n0 (stream_trunc p n) }
        firstn n0 (stream_trunc p n) @ skipn n0 (stream_trunc p n) ;
        == { firstn_stream_trunc_left n0 n p }
        stream_trunc p n0 @ skipn n0 (stream_trunc p n) ;
      } ;
      assert (Some? (find_ret body [] (stream_trunc p n)))
    end

let rec iodiv_repeat_inv_proof_aux #w (body : iodiv unit w) (inv : trace -> Type0) (tr0 : trace) (post : wpost unit) (p : iopostream) n :
  Lemma
    (requires inv tr0 /\ trace_invariant w inv /\ event_stream (repeat body) p)
    (ensures inv (tr0 @ ipos_trace (stream_trunc p n)))
    (decreases n)
= match find_ret body [] (stream_trunc p n) with
  | Some ((), q) ->
    assert (isRet (body (find_ret_prefix body [] (stream_trunc p n)))) ;
    assert (inv (tr0 @ ipos_trace (find_ret_prefix body [] (stream_trunc p n)))) ;
    find_ret_Some_pos body [] (stream_trunc p n) ;
    assert (stream_trunc p n == (find_ret_prefix body [] (stream_trunc p n)) @ q) ;
    ipos_trace_append (find_ret_prefix body [] (stream_trunc p n)) q ;
    append_assoc tr0 (ipos_trace (find_ret_prefix body [] (stream_trunc p n))) (ipos_trace q) ;
    begin match q with
    | [] -> ()
    | Tau_choice :: q' ->
      event_stream_repeat_one_ret body p n q' ;
      repeat_inv_proof_aux_smaller body n p (find_ret_prefix body [] (stream_trunc p n)) q' ;
      iodiv_repeat_inv_proof_aux body inv (tr0 @ ipos_trace (find_ret_prefix body [] (stream_trunc p n))) post (stream_drop (1 + length (find_ret_prefix body [] (stream_trunc p n))) p) (n - 1 - length (find_ret_prefix body [] (stream_trunc p n))) ;
      repeat_inv_proof_aux_eqpos p (find_ret_prefix body [] (stream_trunc p n)) q' n ;
      assert (inv ((tr0 @ ipos_trace (find_ret_prefix body [] (stream_trunc p n))) @ ipos_trace q'))
    | c :: q' ->
      assert (isEvent (repeat body (stream_trunc p n))) ;
      repeat_unfold_1 body
    end
  | None ->
    // In case where we still haven't reached a return, we do a case
    // analysis on wheter there will ever be such a return.
    eliminate (event_stream body p) \/ ~ (event_stream body p)
    returns inv (tr0 @ ipos_trace (stream_trunc p n))
    with h. iodiv_repeat_inv_proof_aux_inf body inv tr0 post p n
    and  h. iodiv_repeat_inv_proof_aux_overfin body inv tr0 post p n

let iodiv_repeat_inv_proof #w (body : iodiv unit w) (inv : trace -> Type0) :
  Lemma
    (requires trace_invariant w inv)
    (ensures
      forall (post : wpost unit) (p p' : iopostream).
        event_stream (repeat body) p ==>
        p `uptotau` p' ==>
        (forall n. inv (ipos_trace (stream_trunc p' n)))
    )
= let aux (post : wpost unit) (p p' : iopostream) n :
    Lemma
      (requires event_stream (repeat body) p)
      (ensures inv (ipos_trace (stream_trunc p n)))
      [SMTPat ()]
  = iodiv_repeat_inv_proof_aux body inv [] post p n
  in
  forall_intro_2 (move_requires_2 (embeds_trace_implies inv))

let iodiv_repeat_with_inv #w (body : iodiv unit w) (inv : trace -> Type0) :
  Pure (iodiv unit (wrepeat_inv w inv)) (requires trace_invariant w inv) (ensures fun _ -> True)
= // fin
  forall_intro (repeat_not_ret body) ;
  assert (forall (post : wpost unit) p. wrepeat_inv w inv post ==> isRet (repeat body p) ==> post (Fin (ipos_trace p) (ret_val (repeat body p)))) ;

  // inf
  iodiv_repeat_inv_proof body inv ;
  assert (forall (post : wpost unit) (p p' : iopostream). wrepeat_inv w inv post ==> event_stream (repeat body) p ==> p `uptotau` p' ==> post (Inf p')) ;

  assert (forall (post : wpost unit). wrepeat_inv w inv post ==> theta (repeat body) post) ;
  repeat body

let iodiv_subcomp (a : Type) (w1 w2 : twp a) (m : iodiv a w1) :
  Pure (iodiv a w2) (requires w2 `stronger_twp` w1) (ensures fun _ -> True)
= m

let wite #a (w1 w2 : twp a) (b : bool) : twp a =
  fun post -> (b ==> w1 post) /\ (~ b ==> w2 post)

let iodiv_if_then_else (a : Type) (w1 w2 : twp a) (f : iodiv a w1) (g : iodiv a w2) (b : bool) : Type =
  iodiv a (wite w1 w2 b)

[@@allow_informative_binders]
reifiable total layered_effect {
  IODiv : a:Type -> w:twp a -> Effect
  with
    repr         = iodiv ;
    return       = iodiv_ret ;
    bind         = iodiv_bind ;
    subcomp      = iodiv_subcomp ;
    if_then_else = iodiv_if_then_else
    // tau          = iodiv_tau // Universe problems
    // call         = iodiv_call
}

(** Tests *)

let terminates #a : wpost a =
  fun b -> Fin? b

let diverges #a : wpost a =
  fun b -> Inf? b

let repeat_ret_loops () :
  Lemma (wrepeat_inv (wret ()) (fun _ -> True) diverges)
= ()


(** EXPERIMENT Making the effect partial *)

let piodiv a (w : twp a) =
  squash (w (fun _ -> True)) -> iodiv a w

let piodiv_ret a (x : a) : piodiv a (wret x) =
  fun _ -> iodiv_ret a x

// We use pwbind instead of wbind to get the precondition
// Is it the most conservative choice here?
let pwbind #a #b (w : twp a) (wf : a -> twp b) : twp b =
  fun post ->
    w (fun _ -> True) /\
    (forall x. wf x (fun _ -> True)) /\ // Maybe here we can assume the post holds for x? Like w (fun b -> b == Fin ? x) or so.
    wbind w wf post

let piodiv_bind a b w wf (m : piodiv a w) (f : (x:a) -> piodiv b (wf x)) : piodiv b (pwbind w wf) =
  fun h -> iodiv_bind a b w wf (m ()) (fun x -> f x ())

let piodiv_subcomp (a : Type) (w1 w2 : twp a) (m : piodiv a w1) :
  Pure (piodiv a w2) (requires w2 `stronger_twp` w1) (ensures fun _ -> True)
= m

let wlift #a (w : pure_wp a) : twp a =
  fun post -> w (fun x -> post (Fin [] x))

let wlift_unfold #a (w : pure_wp a) post :
  Lemma (wlift w post == w (fun x -> post (Fin [] x)))
= ()

let lift_pure_piodiv (a : Type) (w : pure_wp a) (f : unit -> PURE a w) : piodiv a (wlift w) =
  fun h ->
    assert (wlift w (fun _ -> True)) ;
    calc (==>) {
      wlift w (fun _ -> True) ;
      == { wlift_unfold w (fun _ -> True) }
      w (fun x -> (fun _ -> True) (Fin [] x)) ;
      == {}
      w (fun _ -> True) ;
    } ;
    assert (w (fun _ -> True)) ;
    let r = f () in
    let r' : iodiv a (wret r) = iodiv_ret a r in
    let aux (post : wpost a) : Lemma (requires wlift w post) (ensures wret r post) [SMTPat ()] =
      // wlift_unfold w post ;
      // assume (w (fun x -> post (Fin [] x))) ;
      // assume (post (Fin [] r)) ;
      // Somehow missing "validity" of w.
      admit ()
    in
    assert (forall (post : wpost a). wlift w post ==> wret r post) ;
    assume ((wlift w) `stronger_twp` (wret r)) ; // Why not?
    iodiv_subcomp _ (wret r) (wlift w) r'
