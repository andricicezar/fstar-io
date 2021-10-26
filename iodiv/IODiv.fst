module IODiv

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc
open Util
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
  forall n. exists m. ipos_trace (postream_trunc q n) == ipos_trace (postream_trunc p m)

let uptotau (p q : iopostream) =
  p `embeds` q /\ q `embeds` p

let uptotau_refl () :
  Lemma (forall p. p `uptotau` p)
= ()

let uptotau_sym () :
  Lemma (forall p q. p `uptotau` q ==> q `uptotau` p)
= ()

let uptotau_trans () :
  Lemma (forall p q r. p `uptotau` q ==> q `uptotau` r ==> p `uptotau` r)
= ()

// Could also be proved without using extensionality
let pseq_uptotau (p q : iopostream) :
  Lemma
    (requires p `pseq` q)
    (ensures p `uptotau` q)
= postream_ext p q

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
    | Inf p -> forall (p' : iopostream). postream_prepend (trace_to_pos tr) p `uptotau` p' ==> post (Inf p')

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
  forall n. isEvent (t (postream_trunc p n))

(** Effect observation *)
let theta #a (t : iotree a) =
  fun post ->
    (forall p. isRet (t p) ==> post (Fin (ipos_trace p) (ret_val (t p)))) /\
    (forall (p p' : iopostream). event_stream t p ==> p `uptotau` p' ==> post (Inf p'))

let iodiv a (w : twp a) =
  t: iotree a { w `stronger_twp` theta t }

let iodiv_ret a (x : a) : iodiv a (wret x) =
  assert (forall p. ~ (isEvent (ioret x p))) ;
  assert (forall (p : iopostream). ~ (isEvent (ioret x (postream_trunc p 0)))) ;
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
      (exists n. ~ (isEvent (m (postream_trunc p n)))) /\
      event_stream (bind m f) p
    )
    (ensures
      exists (q : iopos) (s : iopostream).
        p `pseq` postream_prepend q s /\
        isRet (m q)
    )
= let n = indefinite_description_ghost_nat_min (fun n -> ~ (isEvent (m (postream_trunc p n)))) in
  // We now before n we only have events, and n is not an event: this leaves us
  // with either Some Ret, or None, we first show the latter is not possible
  match m (postream_trunc p n) with
  | None ->
    begin match find_ret m [] (postream_trunc p n) with
    | Some (x, q) ->
      find_ret_prefix_suffix_of m [] (postream_trunc p n) ;
      suffix_of_postream_trunc p n (find_ret_prefix m [] (postream_trunc p n))
    | None -> ()
    end
  | Some (Ret x) -> postream_trunc_drop n p

let event_stream_bind #a #b (m : iotree a) (f : a -> iotree b) (p : iopostream) (q : iopos) (s : iopostream) :
  Lemma
    (requires event_stream (bind m f) p /\ p `pseq` postream_prepend q s /\ isRet (m q))
    (ensures event_stream (f (ret_val (m q))) s)
= let aux (p : iopostream) (q : iopos) (s : iopostream) (i : nat) :
    Lemma (event_stream (bind m f) p ==> p `pseq` postream_prepend q s ==> isRet (m q) ==> isEvent (f (ret_val (m q)) (postream_trunc s i))) [SMTPat ()]
  = assert (event_stream (bind m f) p ==> isEvent (bind m f (postream_trunc p (length q + i)))) ;
    postream_trunc_ext p (postream_prepend q s) (length q + i) ;
    assert (event_stream (bind m f) p ==> p `pseq` postream_prepend q s ==> isEvent (bind m f (postream_trunc (postream_prepend q s) (length q + i)))) ;
    postream_prepend_trunc_right q s (length q + i) ;
    assert (event_stream (bind m f) p ==> p `pseq` postream_prepend q s ==> isEvent (bind m f (q @ postream_trunc s i))) ;
    find_ret_append m ;
    assert (isRet (m q) ==> find_ret m [] (q @ postream_trunc s i) == Some (ret_val (m q), postream_trunc s i))
  in ()

let shift_post_Inf_spe #a tr s p (post : wpost a) :
  Lemma
    (requires shift_post tr post (Inf s) /\ postream_prepend (trace_to_pos tr) s `uptotau` p)
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
    (ensures fun m -> ipos_trace (fst (splitAt n p)) == ipos_trace (fst (splitAt m q)) /\ m <= length q)
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

let postream_prepend_embeds (p q : iopos) (s : iopostream) :
  Lemma
    (requires ipos_trace p == ipos_trace q)
    (ensures postream_prepend p s `embeds` postream_prepend q s)
= let aux n :
    Lemma (exists m. ipos_trace (postream_trunc (postream_prepend q s) n) == ipos_trace (postream_trunc (postream_prepend p s) m)) [SMTPat ()]
  = if n <= length q
    then begin
      let m = ipos_trace_firstn_eq q p n in
      calc (==) {
        ipos_trace (postream_trunc (postream_prepend q s) n) ;
        == { postream_prepend_trunc_left q s n }
        ipos_trace (fst (splitAt n q)) ;
        == {}
        ipos_trace (fst (splitAt m p)) ;
        == { postream_prepend_trunc_left p s m }
        ipos_trace (postream_trunc (postream_prepend p s) m) ;
      }
    end
    else begin
      calc (==) {
        ipos_trace (postream_trunc (postream_prepend q s) n) ;
        == { postream_prepend_trunc_right q s n }
        ipos_trace (q @ postream_trunc s (n - length q)) ;
        == { forall_intro_2 ipos_trace_append }
        ipos_trace q @ ipos_trace (postream_trunc s (n - length q)) ;
        == {}
        ipos_trace p @ ipos_trace (postream_trunc s (n - length q)) ;
        == {}
        ipos_trace p @ ipos_trace (postream_trunc s ((length p + n - length q) - length p)) ;
        == { forall_intro_2 ipos_trace_append }
        ipos_trace (p @ postream_trunc s ((length p + n - length q) - length p)) ;
        == { postream_prepend_trunc_right p s (length p + n - length q) }
        ipos_trace (postream_trunc (postream_prepend p s) (length p + n - length q)) ;
      }
    end
  in ()

let postream_prepend_uptotau (p q : iopos) (s : iopostream) :
  Lemma
    (requires ipos_trace p == ipos_trace q)
    (ensures postream_prepend p s `uptotau` postream_prepend q s)
= postream_prepend_embeds p q s ; postream_prepend_embeds q p s

let rec ipos_trace_to_pos (tr : trace) :
  Lemma (ipos_trace (trace_to_pos tr) == tr)
= match tr with
  | [] -> ()
  | c :: tr' -> ipos_trace_to_pos tr'

let iodiv_bind_inf_fin_shift_post #a #b #w #wf (m : iodiv a w) (f : (x:a) -> iodiv b (wf x)) (post : wpost b) (p p' : iopostream) (q : iopos) (s : iopostream) :
  Lemma
    (requires wbind w wf post /\ event_stream (bind m f) p /\ ~ (event_stream m p) /\ p `uptotau` p' /\ p `pseq` postream_prepend q s /\ isRet (m q))
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
    (requires p `pseq` postream_prepend q s /\ p `uptotau` p')
    (ensures postream_prepend (trace_to_pos (ipos_trace q)) s `uptotau` p')
= pseq_uptotau p (postream_prepend q s) ;
  ipos_trace_to_pos (ipos_trace q) ;
  postream_prepend_uptotau (trace_to_pos (ipos_trace q)) q s

let iodiv_bind_inf_fin a b w wf (m : iodiv a w) (f : (x:a) -> iodiv b (wf x)) :
  Lemma (forall (post : wpost b) (p p' : iopostream). wbind w wf post ==> event_stream (bind m f) p ==> ~ (event_stream m p) ==> p `uptotau` p' ==> post (Inf p'))
= let aux (post : wpost b) (p p' : iopostream) :
    Lemma
      (requires wbind w wf post /\ event_stream (bind m f) p /\ ~ (event_stream m p) /\ p `uptotau` p')
      (ensures post (Inf p'))
      [SMTPat ()]
  = finite_branch_prefix m f p ;
    assert (exists (q : iopos) (s : iopostream). p `pseq` postream_prepend q s /\ isRet (m q)) ;
    let q = indefinite_description_ghost iopos (fun q -> exists (s : iopostream). p `pseq` postream_prepend q s /\ isRet (m q)) in
    let s = indefinite_description_ghost iopostream (fun s -> p `pseq` postream_prepend q s /\ isRet (m q)) in
    assert (p `pseq` postream_prepend q s) ;
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

let uptotau_cons_tau (p q : iopostream) :
  Lemma (p `uptotau` q ==> postream_prepend [ Tau_choice ] p `uptotau` q)
= admit ()

let event_stream_tau #a (m : iotree a) (p : iopostream) :
    Lemma
      (requires event_stream (tau m) p)
      (ensures pshead p == Tau_choice /\ event_stream m (pstail p))
= assert (isEvent (tau m (postream_trunc p 1))) ;
  assert (pshead p == Tau_choice) ;

  let aux n : Lemma (isEvent (m (postream_trunc (pstail p) n))) [SMTPat ()] =
    assert (isEvent (tau m (postream_trunc p (n+1)))) ;
    postream_trunc_succ p n
  in ()

let iodiv_tau #a #w (m : iodiv a w) : iodiv a w =

  // fin
  assert (forall (post : wpost a) p. w post ==> isRet (tau m p) ==> post (Fin (ipos_trace p) (ret_val (tau m p)))) ;

  // inf
  let aux_inf (post : wpost a) (p p' : iopostream) :
    Lemma
      (requires w post /\ event_stream (tau m) p /\ p `uptotau` p')
      (ensures post (Inf p'))
      [SMTPat ()]
    = event_stream_tau m p ;
      assert (forall q. pstail p `uptotau` q ==> post (Inf q)) ; // (*)
      pseq_head_tail p ;
      assert (p `pseq` postream_prepend [pshead p] (pstail p)) ;
      pseq_uptotau p (postream_prepend [Tau_choice] (pstail p)) ;
      assume (pstail p `uptotau` postream_prepend [Tau_choice] (pstail p)) ; // TODO lemma abstract pstail p
      assert (pstail p `uptotau` p') ;
      admit () // Should follow from (*)
  in

  assert (forall (post : wpost a). w post ==> theta (tau m) post) ;
  tau m

// let twp_call #a (o : cmds) (x : io_args o) (w : io_res o -> twp a) : twp a =
//   fun post -> post [] None /\ (forall y. w y (shift_post [ Call_choice o x y ] post))

// let iodiv_call #a (o : cmds) (x : io_args o) #w (k : (r : io_res o) -> iodiv a (w r)) : iodiv a (twp_call o x w) =
//   call o x k

// let rec twp_repeat_trunc (w : twp unit) (n : nat) : twp unit =
//   if n = 0
//   then fun post -> True
//   else wbind w (fun (_:unit) -> twp_tau (twp_repeat_trunc w (n - 1)))

// let twp_repeat (w : twp unit) : twp unit =
//   fun post -> forall n. twp_repeat_trunc w n post

// let repeat_unfold_1 (body : iotree unit) :
//   Lemma (forall p. repeat body p == bind body (fun _ -> tau ((if length p = 0 then (fun _ -> loop _) else itree_cofix_unfoldn (repeat_fix body) (length p - 1)) ())) p)
// = forall_intro (itree_cofix_unfold_1 (repeat_fix body) ()) ;
//   forall_intro_2 (repeat_fix_guarded body) ;
//   assert (forall p. itree_cofix (repeat_fix body) () p == repeat_fix body (if length p = 0 then (fun _ -> loop _) else itree_cofix_unfoldn (repeat_fix body) (length p - 1)) () p) ;
//   assert (forall p. itree_cofix (repeat_fix body) () p == bind body (fun _ -> tau ((if length p = 0 then (fun _ -> loop _) else itree_cofix_unfoldn (repeat_fix body) (length p - 1)) ())) p)

// let repeat_one_ret (body : iotree unit) :
//   Lemma (forall p q. isRet (body p) ==> repeat body (p @ Tau_choice :: q) == repeat body q)
// = repeat_unfold_1 body ;
//   find_ret_append body ;
//   assert (forall p q.
//     isRet (body p) ==>
//     repeat body (p @ Tau_choice :: q) == itree_cofix_unfoldn (repeat_fix body) (length (p @ Tau_choice :: q) - 1) () q
//   ) ;
//   forall_intro_2 (repeat_fix_guarded body)

// let rec repeat_not_ret (body : iotree unit) p :
//   Lemma (~ (isRet (repeat body p)))
// = match find_ret body [] p with
//   | Some ((), q) ->
//     repeat_unfold_1 body ;
//     if length p = 0
//     then ()
//     else begin
//       match q with
//       | Tau_choice :: r ->
//         find_ret_length body [] p ;
//         forall_intro_2 (repeat_fix_guarded body) ;
//         find_ret_smaller body [] p ;
//         repeat_not_ret body r
//       | _ :: r -> ()
//       | [] -> ()
//     end
//   | None -> ()

// let rec repeat_any_ret (body : iotree unit) (pl : list iopos) p :
//   Lemma
//     (requires forall pp. mem pp pl ==> isRet (body pp))
//     (ensures repeat body (flatten_sep [Tau_choice] pl @ p) == repeat body p)
// = match pl with
//   | [] -> ()
//   | pp :: pl ->
//     calc (==) {
//       repeat body (flatten_sep [Tau_choice] (pp :: pl) @ p) ;
//       == {}
//       repeat body ((pp @ [Tau_choice] @ flatten_sep [Tau_choice] pl) @ p) ;
//       == { forall_intro_3 (append_assoc #iochoice) }
//       repeat body (pp @ Tau_choice :: (flatten_sep [Tau_choice] pl @ p)) ;
//       == { repeat_one_ret body }
//       repeat body (flatten_sep [Tau_choice] pl @ p) ;
//       == { repeat_any_ret body pl p }
//       repeat body p ;
//     }

// let rec repeat_any_ret_event_post #w (body : iodiv unit w) (pl : list iopos) p :
//   Lemma
//     (requires forall pp. mem pp pl ==> isRet (body pp))
//     (ensures forall (post : wpost unit).
//       twp_repeat_trunc w (1 + length pl) post ==>
//       isEvent (body p) ==>
//       post (ipos_trace (flatten_sep [Tau_choice] pl @ p)) None
//     )
//     (decreases pl)
// = match pl with
//   | [] -> ()
//   | pp :: pl ->
//     repeat_any_ret_event_post body pl p ;
//     calc (==) {
//       ipos_trace (flatten_sep [Tau_choice] (pp :: pl) @ p) ;
//       == {}
//       ipos_trace ((pp @ Tau_choice :: flatten_sep [Tau_choice] pl) @ p) ;
//       == { forall_intro_3 (append_assoc #iochoice) }
//       ipos_trace (pp @ Tau_choice :: flatten_sep [Tau_choice] pl @ p) ;
//       == { forall_intro_2 ipos_trace_append }
//       ipos_trace pp @ ipos_trace (Tau_choice :: flatten_sep [Tau_choice] pl @ p) ;
//       == {}
//       ipos_trace pp @ ipos_trace (flatten_sep [Tau_choice] pl @ p) ;
//     }

// let rec repeat_any_ret_ret_post #w (body : iodiv unit w) (pl : list iopos) p :
//   Lemma
//     (requires forall pp. mem pp pl ==> isRet (body pp))
//     (ensures forall (post : wpost unit).
//       twp_repeat_trunc w (1 + length pl) post ==>
//       isRet (body p) ==>
//       post (ipos_trace (flatten_sep [Tau_choice] pl @ p)) None
//     )
//     (decreases pl)
// = match pl with
//   | [] ->
//     assert (forall (post : wpost unit).
//       twp_repeat_trunc w 1 post ==>
//       isRet (body p) ==>
//       twp_tau (twp_repeat_trunc w 0) (shift_post (ipos_trace p) post)
//     )
//   | pp :: pl ->
//     repeat_any_ret_ret_post body pl p ;
//     assert (forall (post : wpost unit).
//       twp_repeat_trunc w (1 + length pl) post ==>
//       isRet (body p) ==>
//       post (ipos_trace (flatten_sep [Tau_choice] pl @ p)) None
//     ) ;
//     assert (forall (post : wpost unit).
//       twp_repeat_trunc w (1 + length pl) (shift_post (ipos_trace pp) post) ==>
//       isRet (body p) ==>
//       shift_post (ipos_trace pp) post (ipos_trace (flatten_sep [Tau_choice] pl @ p)) None
//     ) ;
//     calc (==) {
//       ipos_trace (flatten_sep [Tau_choice] (pp :: pl) @ p) ;
//       == {}
//       ipos_trace ((pp @ Tau_choice :: flatten_sep [Tau_choice] pl) @ p) ;
//       == { forall_intro_3 (append_assoc #iochoice) }
//       ipos_trace (pp @ Tau_choice :: flatten_sep [Tau_choice] pl @ p) ;
//       == { forall_intro_2 ipos_trace_append }
//       ipos_trace pp @ ipos_trace (Tau_choice :: flatten_sep [Tau_choice] pl @ p) ;
//       == {}
//       ipos_trace pp @ ipos_trace (flatten_sep [Tau_choice] pl @ p) ;
//     } ;
//     assert (forall (post : wpost unit).
//       twp_repeat_trunc w (1 + length pl) (shift_post (ipos_trace pp) post) ==>
//       isRet (body p) ==>
//       post (ipos_trace (flatten_sep [Tau_choice] (pp :: pl) @ p)) None
//     ) ;
//     assert (forall (post : wpost unit).
//       twp_repeat_trunc w (2 + length pl) post ==>
//       isRet (body p) ==>
//       post (ipos_trace (flatten_sep [Tau_choice] (pp :: pl) @ p)) None
//     )

// let rec iodiv_repeat_proof_gen #w (body : iodiv unit w) (pl : list iopos) p :
//   Lemma
//     (requires forall pp. mem pp pl ==> isRet (body pp))
//     (ensures forall (post : wpost unit).
//       twp_repeat w post ==>
//       isEvent (repeat body (flatten_sep [Tau_choice] pl @ p)) ==>
//       post (ipos_trace (flatten_sep [Tau_choice] pl @ p)) None
//     )
//     (decreases p)
// = match find_ret body [] p with
//   | Some ((), q) ->
//     assert (isRet (body (find_ret_prefix body [] p))) ;
//     find_ret_Some_pos body [] p ;
//     assert (p == find_ret_prefix body [] p @ q) ;
//     begin match q with
//     | [] ->
//       repeat_any_ret body pl p ;
//       repeat_unfold_1 body ;
//       assert (repeat body p == Some Tau) ;
//       repeat_any_ret_ret_post body pl p ;
//       assert (isRet (body p)) ;
//       assert (forall (post : wpost unit). twp_repeat w post ==> twp_repeat_trunc w (1 + length pl) post) ;
//       assert (forall (post : wpost unit).
//         twp_repeat w post ==>
//         isEvent (repeat body p) ==>
//         post (ipos_trace (flatten_sep [Tau_choice] pl @ p)) None
//       )
//     | Tau_choice :: r ->
//       forall_intro (mem_append pl [find_ret_prefix body [] p]) ;
//       assert (forall pp. mem pp (pl @ [find_ret_prefix body [] p]) ==> isRet (body pp)) ;
//       assert (p == find_ret_prefix body [] p @ Tau_choice :: r) ;
//       forall_intro_3 (append_assoc #iochoice) ;
//       forall_intro_2 (flatten_sep_append #iochoice [Tau_choice]) ;
//       assert (flatten_sep [Tau_choice] (pl @ [find_ret_prefix body [] p]) == flatten_sep [Tau_choice] pl @ flatten_sep [Tau_choice] [find_ret_prefix body [] p]) ;
//       assert (flatten_sep [Tau_choice] [find_ret_prefix body [] p] == find_ret_prefix body [] p @ [Tau_choice] @ flatten_sep [Tau_choice] []) ;
//       flatten_sep_nil #iochoice [Tau_choice] ;
//       assert (flatten_sep [Tau_choice] pl @ p == flatten_sep [Tau_choice] (pl @ [find_ret_prefix body [] p]) @ r) ;
//       find_ret_smaller body [] p ;
//       iodiv_repeat_proof_gen body (pl @ [find_ret_prefix body [] p]) r
//     | c :: r -> repeat_any_ret body pl p ; repeat_unfold_1 body
//     end
//   | None ->
//     repeat_any_ret body pl p ;
//     repeat_any_ret_event_post body pl p ;
//     assert (forall (post : wpost unit). twp_repeat w post ==> twp_repeat_trunc w (1 + length pl) post) ;
//     repeat_unfold_1 body ;
//     assert (
//       isEvent (repeat body p) ==> isEvent (body p)
//     ) ;
//     assert (forall (post : wpost unit).
//       twp_repeat w post ==>
//       isEvent (repeat body p) ==>
//       post (ipos_trace (flatten_sep [Tau_choice] pl @ p)) None
//     )

// let iodiv_repeat_proof #w (body : iodiv unit w) p :
//   Lemma (forall (post : wpost unit).
//     twp_repeat w post ==>
//     isEvent (repeat body p) ==>
//     post (ipos_trace p) None
//   )
// = iodiv_repeat_proof_gen body [] p

// let iodiv_repeat #w (body : iodiv unit w) : iodiv unit (twp_repeat w) =
//   forall_intro (repeat_not_ret body) ;
//   forall_intro (iodiv_repeat_proof body) ;
//   repeat body

// // We can also "inline" the induction by asking the SMT to prove (p n ==> p (n+1)) which might work sometimes

// (**

//   Alternatively, we propose a definition of iodiv_repeat using an invariant.
//   The invariant is relative to the predicate transformer of the body.
//   It must hold for the empty list / root position because postconditions
//   must be downward closed.

// *)

// let trace_invariant (w : twp unit) (inv : trace -> Type0) =
//   inv [] /\
//   (forall tr. inv tr ==> w (fun tr' v -> inv (tr @ tr') /\ Some? v))

// let twp_repeat_with_inv (w : twp unit) (inv : trace -> Type0) : twp unit =
//   fun post -> forall tr. inv tr ==> post tr None

// let invpost (inv : trace -> Type0) : wpost unit =
//   fun tr v -> inv tr /\ None? v

// // Maybe prove it on the effect observation directly
// let rec twp_repeat_inv_trunc (w : twp unit) (inv : trace -> Type0) n :
//   Lemma (
//     trace_invariant w inv ==>
//     twp_repeat_trunc w n (invpost inv)
//   )
// = if n = 0
//   then ()
//   else begin
//     twp_repeat_inv_trunc w inv (n - 1) ;
//     assume (
//       trace_invariant w inv ==>
//       twp_repeat_trunc w (n-1) (invpost inv) ==>
//       wbind w (fun (_:unit) -> twp_tau (twp_repeat_trunc w (n - 1))) (invpost inv)
//       // ==
//       // w (fun tr v ->
//       //   match v with
//       //   | Some x -> (fun (_:unit) -> twp_tau (twp_repeat_trunc w (n - 1))) x (shift_post tr (invpost inv))
//       //     == twp_tau (twp_repeat_trunc w (n - 1)) (shift_post tr (invpost inv))
//       //   | None -> invpost inv tr None // == inv tr
//       // )
//     ) ;
//     assume (forall (post : wpost unit).
//       wbind w (fun (_:unit) -> twp_tau (twp_repeat_trunc w (n - 1))) post ==>
//       twp_repeat_trunc w n post
//     ) ; // why??
//     assert (
//       trace_invariant w inv ==>
//       twp_repeat_trunc w (n-1) (invpost inv) ==>
//       twp_repeat_trunc w n (invpost inv)
//     )
//   end

// // Some specifications

// // Does not make sense at the moment
// // let terminates #a : wpost a =
// //   fun tr v -> Some? v

// let diverges #a : wpost a =
//   fun tr v -> None? v

// // let ret_terminates a (x : a) : Lemma (wret x terminates) = ()

// // Should be p1 ==> p2 rather than ==
// let rec twp_repeat_trunc_ext w n (p1 p2 : wpost unit) :
//   Lemma ((forall tr x. p1 tr x == p2 tr x) ==> twp_repeat_trunc w n p1 == twp_repeat_trunc w n p2)
// = if n = 0
//   then ()
//   else begin
//     // twp_repeat_trunc_ext w (n-1) p1 p2 ;
//     // assume ((forall tr x. p1 tr x == p2 tr x) ==> wbind w (fun _ -> twp_repeat_trunc w (n -1)) p1 == wbind w (fun _ -> twp_repeat_trunc w (n -1)) p2)
//     // assert (twp_repeat_trunc w n == wbind w (fun _ -> twp_repeat_trunc w (n -1))) ; // Isn't this by def??
//     assume ((forall tr x. p1 tr x == p2 tr x) ==> twp_repeat_trunc w n p1 == twp_repeat_trunc w n p2)
//   end

// let repeat_ret_loops () :
//   Lemma (twp_repeat (wret ()) diverges)
// = let rec aux n :
//     Lemma (twp_repeat_trunc (wret ()) n diverges) [SMTPat ()]
//   = if n = 0
//     then ()
//     else begin
//       aux (n - 1) ;
//       twp_repeat_trunc_ext (wret ()) (n-1) (shift_post [] diverges) (diverges #unit)
//     end
//   in
//   ()

// // Much better
// let repeat_ret_loops_with_inv () :
//   Lemma (twp_repeat_with_inv (wret ()) (fun _ -> True) diverges)
// = ()

// [@@allow_informative_binders]
// reifiable total layered_effect {
//   IODiv : a:Type -> twp a -> Effect
//   with
//     repr   = iodiv ;
//     return = iodiv_ret ;
//     bind   = iodiv_bind
//     // tau    = iodiv_tau ; // Universe problems
//     // call   = iodiv_call
// }
