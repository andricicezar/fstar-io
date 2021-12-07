module IODivHist

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics // Also defines forall_intro so place before Classical
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc
open FStar.FunctionalExtensionality
open Util
open Stream
open Itree

(** IODivHist

    In this file we define a more complete version of the IODiv effect for I/O
    and non-termination than in SIODiv.
    In addition to that, IODivHist also comes with a history for preconditions.

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

noeq
type event =
| EOpenfile : arg : io_args Openfile -> res : io_res Openfile -> event
| ERead     : arg : io_args Read     -> res : io_res Read     -> event
| EClose    : arg : io_args Close    -> res : io_res Close    -> event

let choice_to_event (c : iochoice { c <> Tau_choice }) : event =
  match c with
  | Call_choice Openfile x y -> EOpenfile x y
  | Call_choice Read x y -> ERead x y
  | Call_choice Close x y -> EClose x y

let trace = list event

let rec ipos_trace (p : iopos) : trace =
  match p with
  | [] -> []
  | Tau_choice :: p -> ipos_trace p
  | c :: p -> choice_to_event c :: ipos_trace p

let rec ipos_trace_append (p q : iopos) :
  Lemma (ensures ipos_trace (p @ q) == ipos_trace p @ ipos_trace q) (decreases p)
= match p with
  | [] -> ()
  | Tau_choice :: p -> ipos_trace_append p q
  | Call_choice o x y :: p -> ipos_trace_append p q

(** Up to tau relation on position streams *)
let embeds (p q : iopostream) =
  forall (n : nat). exists (m : nat). ipos_trace (stream_trunc q n) == ipos_trace (stream_trunc p m)

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
    (requires p `embeds` p' /\ (forall (n : nat). pr (ipos_trace (stream_trunc p n))))
    (ensures forall (n : nat). pr (ipos_trace (stream_trunc p' n)))
= ()

noeq
type branch a =
| Fin : tr:trace -> res:a -> branch a
| Inf : p:iopostream -> branch a

unfold
let wpost a = branch a -> Type0

unfold
let wpre a = hist:trace -> Type0

let wp a = wpost a -> wpre a

let wret #a (x : a) : wp a =
  fun post hist -> post (Fin [] x)

let event_to_choice (e : event) : iochoice =
  match e with
  | EOpenfile x y -> Call_choice Openfile x y
  | ERead x y -> Call_choice Read x y
  | EClose x y -> Call_choice Close x y

let choice_to_event_to_choice (c : iochoice { c <> Tau_choice }) :
  Lemma (event_to_choice (choice_to_event c) == c)
= match c with
  | Call_choice o x y ->
    begin match o with
    | Openfile -> ()
    | Read -> ()
    | Close -> ()
    end

// Just a map
let rec trace_to_pos (tr : trace) : iopos =
  match tr with
  | [] -> []
  | c :: tr -> event_to_choice c :: trace_to_pos tr

unfold
let shift_post #a (tr : trace) (post : wpost a) : wpost a =
  fun b ->
    match b with
    | Fin tr' x -> post (Fin (tr @ tr') x)
    | Inf p -> forall (p' : iopostream). stream_prepend (trace_to_pos tr) p `uptotau` p' ==> post (Inf p')

unfold
let wbind #a #b (w : wp a) (wf : a -> wp b) : wp b =
  fun (post : wpost b) (hist : trace) ->
    w (fun b ->
      match b with
      | Fin tr x -> wf x (shift_post tr post) (hist @ tr)
      | Inf p -> post (Inf p)
    ) hist

unfold
let stronger_wp #a (w1 w2 : wp a) : Type0 =
  forall (post : wpost a) (hist : trace). w1 post hist ==> w2 post hist

unfold
let event_stream #a (t : iotree a) (p : iopostream) =
  forall (n : nat). isEvent (t (stream_trunc p n))

(** Check that a file is open *)
let rec is_open_rev (hist : trace) (fd : file_descr) : bool =
  match hist with
  | [] -> false
  | EClose fd' () :: hist' ->
    if fd = fd'
    then false
    else is_open_rev hist' fd
  | EOpenfile s fd' :: hist -> fd = fd'
  | e :: hist' -> is_open_rev hist' fd

let is_open (hist : trace) (fd : file_descr) : bool =
  is_open_rev (rev hist) fd

(** Event valid with respect to a history *)
let valid_event (hist : trace) (e : event) : bool =
  match e with
  | EOpenfile s fd -> true // Doesn't need to check it's closed right?
  | ERead fd s -> is_open hist fd
  | EClose fd () -> is_open hist fd

(** Trace valid with respect to a history *)
let rec valid_trace (hist : trace) (tr : trace) : Pure bool (requires True) (ensures fun _ -> True) (decreases tr) =
  match tr with
  | [] -> true
  | e :: tr' -> valid_event hist e && valid_trace (hist @ [e]) tr'

let valid_postream (hist : trace) (s : iopostream) : Type0 =
  forall (n : nat). valid_trace hist (ipos_trace (stream_trunc s n))

(** Effect observation *)
let theta #a (t : iotree a) : wp a =
  fun (post : wpost a) (hist : trace) ->
    (forall (p : iopos). isRet (t p) ==> post (Fin (ipos_trace p) (ret_val (t p))) /\ valid_trace hist (ipos_trace p)) /\
    (forall (p p' : iopostream). event_stream t p ==> p `uptotau` p' ==> post (Inf p') /\ valid_postream hist p')

let iodiv a (w : wp a) =
  t: iotree a { w `stronger_wp` theta t }

let iodiv_ret a (x : a) : iodiv a (wret x) =
  assert (forall p. ~ (isEvent (ioret x p))) ;
  assert (forall (p : iopostream). ~ (isEvent (ioret x (stream_trunc p 0)))) ;
  ret x

let theta_inst #a w (m : iodiv a w) (post : wpost a) (hist : trace) :
  Lemma
    (requires w post hist)
    (ensures theta m post hist)
= ()

let theta_isRet #a (t : iotree a) (post : wpost a) (hist : trace) (p : iopos) :
  Lemma
    (requires isRet (t p) /\ theta t post hist)
    (ensures post (Fin (ipos_trace p) (ret_val (t p))) /\ valid_trace hist (ipos_trace p))
= ()

let shift_post_Fin #a (tr : trace) (post : wpost a) (tr' : trace) (x : a) :
  Lemma
    (requires shift_post tr post (Fin tr' x))
    (ensures post (Fin (tr @ tr') x))
= ()

let rec valid_trace_append (hist tr tr' : trace) :
  Lemma
    (requires valid_trace hist tr /\ valid_trace (hist @ tr) tr')
    (ensures valid_trace hist (tr @ tr'))
    (decreases tr)
= match tr with
  | [] -> ()
  | e :: t ->
    append_assoc hist [e] t ;
    valid_trace_append (hist @ [e]) t tr'

let iodiv_bind_fin a b w wf (m : iodiv a w) (f : (x : a { x `return_of` m }) -> iodiv b (wf x)) (post : wpost b) (hist : trace) (p : iopos) :
  Lemma
    (requires wbind w wf post hist /\ isRet (bind m f p))
    (ensures post (Fin (ipos_trace p) (ret_val (bind m f p))) /\ valid_trace hist (ipos_trace p))
= find_ret_prefix_val m [] p ;
  theta_inst w m (fun b ->
    match b with
      | Fin tr x -> wf x (shift_post tr post) (hist @ tr)
      | Inf p -> post (Inf p)
  ) hist ;
  theta_isRet m (fun b ->
    match b with
    | Fin tr x -> wf x (shift_post tr post) (hist @ tr)
    | Inf p -> post (Inf p)
  ) hist (find_ret_prefix m [] p) ;
  assert (wf (ret_val (m (find_ret_prefix m [] p))) (shift_post (ipos_trace (find_ret_prefix m [] p)) post) (hist @ (ipos_trace (find_ret_prefix m [] p)))) ;
  assert (valid_trace hist (ipos_trace (find_ret_prefix m [] p))) ;
  theta_inst (wf (ret_val (m (find_ret_prefix m [] p)))) (f (ret_val (m (find_ret_prefix m [] p)))) (shift_post (ipos_trace (find_ret_prefix m [] p)) post) (hist @ (ipos_trace (find_ret_prefix m [] p))) ;
  assert (theta (f (find_ret_val m [] p)) (shift_post (ipos_trace (find_ret_prefix m [] p)) post) (hist @ (ipos_trace (find_ret_prefix m [] p)))) ;
  theta_isRet (f (find_ret_val m [] p)) (shift_post (ipos_trace (find_ret_prefix m [] p)) post) (hist @ (ipos_trace (find_ret_prefix m [] p))) (find_ret_pos m [] p) ;
  assert (shift_post (ipos_trace (find_ret_prefix m [] p)) post (Fin (ipos_trace (find_ret_pos m [] p)) (ret_val (f (find_ret_val m [] p) (find_ret_pos m [] p))))) ;
  assert (valid_trace (hist @ (ipos_trace (find_ret_prefix m [] p))) (ipos_trace (find_ret_pos m [] p))) ;
  assert (shift_post (ipos_trace (find_ret_prefix m [] p)) post (Fin (ipos_trace (find_ret_pos m [] p)) (ret_val (bind m f p)))) ;
  shift_post_Fin (ipos_trace (find_ret_prefix m [] p)) post (ipos_trace (find_ret_pos m [] p)) (ret_val (bind m f p)) ;
  forall_intro_2 ipos_trace_append ;
  assert (post (Fin (ipos_trace (find_ret_prefix m [] p @ find_ret_pos m [] p)) (ret_val (bind m f p)))) ;
  find_ret_Some_pos m [] p ;
  assert (post (Fin (ipos_trace p) (ret_val (bind m f p)))) ;
  valid_trace_append hist (ipos_trace (find_ret_prefix m [] p)) (ipos_trace (find_ret_pos m [] p))

let finite_branch_prefix #a #b (m : iotree a) (f : (x : a { x `return_of` m }) -> iotree b) (p : iopostream) :
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

let event_stream_bind #a #b (m : iotree a) (f : (x : a { x `return_of` m }) -> iotree b) (p : iopostream) (q : iopos) (s : iopostream) :
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

// theta_inst and theta_isRet at once
let theta_inst_Ret #a (w : wp a) (m : iodiv a w) (post : wpost a) (hist : trace) (p : iopos) :
  Lemma
    (requires w post hist /\ isRet (m p))
    (ensures post (Fin (ipos_trace p) (ret_val (m p))) /\ valid_trace hist (ipos_trace p))
= ()

let ret_val_return_of #a (m : iotree a) (p : iopos) :
  Lemma
    (requires isRet (m p))
    (ensures ret_val (m p) `return_of` m)
= ()

let theta_bind_inst #a #b w wf (m : iodiv a w) (f : (x : a { x `return_of` m }) -> iodiv b (wf x)) (post : wpost b) (hist : trace) (q : iopos) :
  Lemma
    (requires wbind w wf post hist /\ isRet (m q))
    (ensures theta (f (ret_val (m q))) (shift_post (ipos_trace q) post) (hist @ ipos_trace q) /\ valid_trace hist (ipos_trace q))
= theta_inst_Ret w m (fun b ->
    match b with
    | Fin tr x -> wf x (shift_post tr post) (hist @ tr)
    | Inf p -> post (Inf p)
  ) hist q

let theta_event_stream #a w (m : iodiv a w) (post : wpost a) (hist : trace) (p p' : iopostream) :
  Lemma
    (requires theta m post hist /\ event_stream m p /\ p `uptotau` p')
    (ensures post (Inf p') /\ valid_postream hist p')
= ()

let iodiv_bind_inf_fin_shift_post #a #b #w #wf (m : iodiv a w) (f : (x : a { x `return_of` m }) -> iodiv b (wf x)) (post : wpost b) (hist : trace) (p p' : iopostream) (q : iopos) (s : iopostream) :
  Lemma
    (requires wbind w wf post hist /\ event_stream (bind m f) p /\ p `uptotau` p' /\ p `feq` stream_prepend q s /\ isRet (m q))
    (ensures shift_post (ipos_trace q) post (Inf s) /\ valid_trace hist (ipos_trace q) /\ valid_postream (hist @ ipos_trace q) s)
= theta_bind_inst w wf m f post hist q ;
  event_stream_bind m f p q s ;
  theta_event_stream (wf (ret_val (m q))) (f (ret_val (m q))) (shift_post (ipos_trace q) post) (hist @ ipos_trace q) s s

let iodiv_bind_inf_fin_upto_aux (s p p' : iopostream) (q : iopos) :
  Lemma
    (requires p `feq` stream_prepend q s /\ p `uptotau` p')
    (ensures stream_prepend (trace_to_pos (ipos_trace q)) s `uptotau` p')
= feq_uptotau p (stream_prepend q s) ;
  ipos_trace_to_pos (ipos_trace q) ;
  stream_prepend_uptotau (trace_to_pos (ipos_trace q)) q s

let rec firstn_trace_to_pos (n : nat) (tr : trace) :
  Lemma (firstn n (trace_to_pos tr) == trace_to_pos (firstn n tr))
= match n, tr with
  | 0, _ -> ()
  | _, [] -> ()
  | _, e :: tr' -> firstn_trace_to_pos (n-1) tr'

let rec valid_trace_firstn (n : nat) (hist tr : trace) :
  Lemma
    (requires valid_trace hist tr)
    (ensures valid_trace hist (firstn n tr))
= match n, tr with
  | 0, _ -> ()
  | _, [] -> ()
  | _, e :: tr' -> valid_trace_firstn (n-1) (hist @ [e]) tr'

let valid_postream_prepend (hist tr : trace) (s p' : iopostream) :
  Lemma
    (requires valid_trace hist tr /\ valid_postream (hist @ tr) s /\ stream_prepend (trace_to_pos tr) s `uptotau` p')
    (ensures valid_postream hist p')
= introduce forall (n : nat). valid_trace hist (ipos_trace (stream_trunc p' n))
  with begin
    eliminate exists (m : nat). ipos_trace (stream_trunc p' n) == ipos_trace (stream_trunc (stream_prepend (trace_to_pos tr) s) m)
    returns valid_trace hist (ipos_trace (stream_trunc p' n))
    with _. begin
      stream_prepend_trunc (trace_to_pos tr) s m ;
      if m <= length (trace_to_pos tr)
      then begin
        calc (==) {
          ipos_trace (stream_trunc p' n) ;
          == {}
          ipos_trace (stream_trunc (stream_prepend (trace_to_pos tr) s) m) ;
          == {}
          ipos_trace (firstn m (trace_to_pos tr)) ;
          == { firstn_trace_to_pos m tr }
          ipos_trace (trace_to_pos (firstn m tr)) ;
          == { ipos_trace_to_pos (firstn m tr) }
          firstn m tr ;
        } ;
        valid_trace_firstn m hist tr
      end
      else begin
        ipos_trace_append (trace_to_pos tr) (stream_trunc s (m - length (trace_to_pos tr))) ;
        ipos_trace_to_pos tr ;
        valid_trace_append hist tr (ipos_trace (stream_trunc s (m - length (trace_to_pos tr))))
      end
    end
  end

let iodiv_bind_inf_fin_aux a b w wf (m : iodiv a w) (f : (x : a { x `return_of` m }) -> iodiv b (wf x)) (post : wpost b) (hist : trace) (p p' : iopostream) (q : iopos) (s : iopostream) :
  Lemma
    (requires wbind w wf post hist /\ event_stream (bind m f) p /\ p `uptotau` p' /\ p `feq` stream_prepend q s /\ isRet (m q))
    (ensures post (Inf p') /\ valid_postream hist p')
= iodiv_bind_inf_fin_shift_post m f post hist p p' q s ;
  iodiv_bind_inf_fin_upto_aux s p p' q ;
  shift_post_Inf_spe (ipos_trace q) s p' post ;
  valid_postream_prepend hist (ipos_trace q) s p'

let iodiv_bind_inf_fin a b w wf (m : iodiv a w) (f : (x : a { x `return_of` m }) -> iodiv b (wf x)) (post : wpost b) (hist : trace) (p p' : iopostream) :
  Lemma
    (requires wbind w wf post hist /\ event_stream (bind m f) p /\ ~ (event_stream m p) /\ p `uptotau` p')
    (ensures post (Inf p') /\ valid_postream hist p')
= finite_branch_prefix m f p ;
  eliminate exists q. exists (s : iopostream). p `feq` stream_prepend q s /\ isRet (m q)
  returns post (Inf p') /\ valid_postream hist p'
  with _. begin
    eliminate exists (s : iopostream). p `feq` stream_prepend q s /\ isRet (m q)
    returns post (Inf p') /\ valid_postream hist p'
    with _. iodiv_bind_inf_fin_aux a b w wf m f post hist p p' q s
  end

let iodiv_bind a b w wf (m : iodiv a w) (f : (x : a { x `return_of` m }) -> iodiv b (wf x)) : iodiv b (wbind w wf) =
  assert (forall (post : wpost a) (hist : trace). w post hist ==> theta m post hist) ;
  assert (forall (post : wpost b) (hist : trace) x. wf x post hist ==> theta (f x) post hist) ;

  introduce forall (post : wpost b) (hist : trace). wbind w wf post hist ==> theta (bind m f) post hist
  with begin
    introduce wbind w wf post hist ==> theta (bind m f) post hist
    with _. begin
      // fin
      introduce forall (p : iopos). isRet (bind m f p) ==> post (Fin (ipos_trace p) (ret_val (bind m f p))) /\ valid_trace hist (ipos_trace p)
      with begin
        introduce isRet (bind m f p) ==> post (Fin (ipos_trace p) (ret_val (bind m f p))) /\ valid_trace hist (ipos_trace p)
        with h2. iodiv_bind_fin a b w wf m f post hist p
      end ;

      // inf
      introduce forall (p p' : iopostream). event_stream (bind m f) p ==> p `uptotau` p' ==> post (Inf p') /\ valid_postream hist p'
      with begin
        introduce event_stream (bind m f) p ==> (p `uptotau` p' ==> post (Inf p') /\ valid_postream hist p')
        with _. begin
          introduce p `uptotau` p' ==> post (Inf p') /\ valid_postream hist p'
          with _. begin
            eliminate (event_stream m p) \/ ~ (event_stream m p)
            returns post (Inf p') /\ valid_postream hist p'
            with _. ()
            and _. iodiv_bind_inf_fin a b w wf m f post hist p p'
          end
        end
      end
    end
  end ;

  bind m f

let event_stream_tau #a (m : iotree a) (p : iopostream) :
    Lemma
      (requires event_stream (tau m) p)
      (ensures shead p == Tau_choice /\ event_stream m (stail p))
= assert (isEvent (tau m (stream_trunc p 1))) ;
  assert (shead p == Tau_choice) ;

  introduce forall (n : nat). isEvent (m (stream_trunc (stail p) n))
  with begin
    assert (isEvent (tau m (stream_trunc p (n+1)))) ;
    stream_trunc_succ p n
  end

let uptotau_prepend_tau (p : iopostream) :
  Lemma (p `uptotau` stream_prepend [Tau_choice] p)
= introduce forall n. exists m. ipos_trace (stream_trunc p n) == ipos_trace (stream_trunc (stream_prepend [Tau_choice] p) m)
  with begin
    stream_prepend_trunc [Tau_choice] p (n+1) ;
    assert (stream_trunc (stream_prepend [Tau_choice] p) (n+1) == Tau_choice :: stream_trunc p n)
  end ;
  introduce forall n. exists m. ipos_trace (stream_trunc p m) == ipos_trace (stream_trunc (stream_prepend [Tau_choice] p) n)
  with begin
    if n = 0
    then ()
    else stream_prepend_trunc [Tau_choice] p n
  end

let iodiv_tau (a:Type) w (m : iodiv a w) : iodiv a w =

  introduce forall (post : wpost a) (hist : trace). w post hist ==> theta (tau m) post hist
  with begin
    introduce w post hist ==> theta (tau m) post hist
    with _. begin
      // fin
      assert (forall p. isRet (tau m p) ==> post (Fin (ipos_trace p) (ret_val (tau m p))) /\ valid_trace hist (ipos_trace p)) ;

      // inf
      introduce forall (p p' : iopostream). event_stream (tau m) p ==> p `uptotau` p' ==> post (Inf p') /\ valid_postream hist p'
      with begin
        introduce event_stream (tau m) p ==> (p `uptotau` p' ==> post (Inf p') /\ valid_postream hist p')
        with _. begin
          introduce p `uptotau` p' ==> post (Inf p') /\ valid_postream hist p'
          with _. begin
            event_stream_tau m p ;
            assert (forall q. stail p `uptotau` q ==> post (Inf q)) ;
            feq_head_tail p ;
            assert (p `feq` stream_prepend [shead p] (stail p)) ;
            feq_uptotau p (stream_prepend [Tau_choice] (stail p)) ;
            uptotau_prepend_tau (stail p) ;
            assert (stail p `uptotau` stream_prepend [Tau_choice] (stail p)) ;
            uptotau_trans (stail p) (stream_prepend [Tau_choice] (stail p)) p ;
            uptotau_trans (stail p) p p'
          end
        end
      end
    end
  end ;

  tau m

unfold
let wcall #a (o : cmds) (x : io_args o) (w : io_res o -> wp a) : wp a =
  fun (post : wpost a) (hist : trace) ->
    forall (y : io_res o).
      w y (shift_post [ choice_to_event (Call_choice o x y) ] post) (hist @ [ choice_to_event (Call_choice o x y) ]) /\
      valid_event hist (choice_to_event (Call_choice o x y))

let isCall_choice (o : cmds) (x : io_args o) (t : iochoice) : bool =
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

  introduce forall n. isEvent (k (call_choice_res o x (shead p)) (stream_trunc (stail p) n))
  with begin
    assert (isEvent (call o x k (stream_trunc p (n+1)))) ;
    stream_trunc_succ p n
  end

let wcall_inst #a (o : cmds) (x : io_args o) (w : io_res o -> wp a) (post : wpost a) (hist : trace) (y : io_res o) :
  Lemma
    (requires wcall o x w post hist)
    (ensures w y (shift_post [ choice_to_event (Call_choice o x y) ] post) (hist @ [ choice_to_event (Call_choice o x y) ]) /\ valid_event hist (choice_to_event (Call_choice o x y)))
= ()


let theta_wcall_inf #a (o : cmds) (x : io_args o) #w (k : (r : io_res o) -> iodiv a (w r)) (post : wpost a) (hist : trace) (p : iopostream) :
  Lemma
    (requires wcall o x w post hist /\ event_stream (call o x k) p)
    (ensures isCall_choice o x (shead p) /\ shift_post [ choice_to_event (Call_choice o x (call_choice_res o x (shead p))) ] post (Inf (stail p)) /\ valid_event hist (choice_to_event (Call_choice o x (call_choice_res o x (shead p)))) /\ valid_postream (hist @ [ choice_to_event (Call_choice o x (call_choice_res o x (shead p))) ]) (stail p))
= event_stream_call o x k p ;
  wcall_inst o x w post hist (call_choice_res o x (shead p)) ;
  theta_inst (w (call_choice_res o x (shead p))) (k (call_choice_res o x (shead p))) (shift_post [ choice_to_event (Call_choice o x (call_choice_res o x (shead p))) ] post) (hist @ [ choice_to_event (Call_choice o x (call_choice_res o x (shead p))) ]) ;
  theta_event_stream (w (call_choice_res o x (shead p))) (k (call_choice_res o x (shead p))) (shift_post [ choice_to_event (Call_choice o x (call_choice_res o x (shead p))) ] post) (hist @ [ choice_to_event (Call_choice o x (call_choice_res o x (shead p))) ]) (stail p) (stail p)

let iodiv_call_aux_upto (a : Type) (o : cmds) (x : io_args o) #w (k : (r : io_res o) -> iodiv a (w r)) (post : wpost a) (hist : trace) (p p' : iopostream) :
  Lemma
    (requires isCall_choice o x (shead p) /\ p `uptotau` p')
    (ensures stream_prepend (trace_to_pos [ choice_to_event (Call_choice o x (call_choice_res o x (shead p))) ]) (stail p) `uptotau` p')
= feq_head_tail p ;
  assert (stream_prepend [shead p] (stail p) `feq` p) ;
  assert (isCall_choice o x (shead p)) ;
  assert (shead p == Call_choice o x (call_choice_res o x (shead p))) ;
  assert (stream_prepend [ Call_choice o x (call_choice_res o x (shead p)) ] (stail p) `feq` p) ;
  calc (==) {
    trace_to_pos [ choice_to_event (Call_choice o x (call_choice_res o x (shead p))) ] ;
    == {}
    [ event_to_choice (choice_to_event (Call_choice o x (call_choice_res o x (shead p)))) ] ;
    == { choice_to_event_to_choice (Call_choice o x (call_choice_res o x (shead p))) }
    [ Call_choice o x (call_choice_res o x (shead p)) ] ;
  } ;
  assert (stream_prepend [ Call_choice o x (call_choice_res o x (shead p)) ] (stail p) == stream_prepend (trace_to_pos [ choice_to_event (Call_choice o x (call_choice_res o x (shead p))) ]) (stail p)) ;
  assert (stream_prepend (trace_to_pos [ choice_to_event (Call_choice o x (call_choice_res o x (shead p))) ]) (stail p) `feq` p) ;
  feq_uptotau (stream_prepend (trace_to_pos [ choice_to_event (Call_choice o x (call_choice_res o x (shead p))) ]) (stail p)) p ;
  uptotau_trans (stream_prepend (trace_to_pos [ choice_to_event (Call_choice o x (call_choice_res o x (shead p))) ]) (stail p)) p p'

let iodiv_call_aux (a : Type) (o : cmds) (x : io_args o) #w (k : (r : io_res o) -> iodiv a (w r)) (post : wpost a) (hist : trace) (p p' : iopostream) :
  Lemma
    (requires wcall o x w post hist /\ event_stream (call o x k) p /\ p `uptotau` p')
    (ensures post (Inf p') /\ valid_postream hist p')
= theta_wcall_inf o x k post hist p ;
  iodiv_call_aux_upto a o x k post hist p p' ;
  assert (post (Inf p')) ;
  valid_postream_prepend hist [ choice_to_event (Call_choice o x (call_choice_res o x (shead p))) ] (stail p) p' ;
  assert (valid_postream hist p')

let iodiv_call (a : Type) (o : cmds) (x : io_args o) #w (k : (r : io_res o) -> iodiv a (w r)) : iodiv a (wcall o x w) =

  introduce forall (post : wpost a) (hist : trace). wcall o x w post hist ==> theta (call o x k) post hist
  with begin
    introduce wcall o x w post hist ==> theta (call o x k) post hist
    with _. begin
      // fin
      assert (forall p. isRet (call o x k p) ==> post (Fin (ipos_trace p) (ret_val (call o x k p))) /\ valid_trace hist (ipos_trace p)) ;

      // inf
      introduce forall (p p' : iopostream). event_stream (call o x k) p ==> p `uptotau` p' ==> post (Inf p') /\ valid_postream hist p'
      with begin
        introduce event_stream (call o x k) p ==> (p `uptotau` p' ==> post (Inf p') /\ valid_postream hist p')
        with _. begin
          introduce p `uptotau` p' ==> post (Inf p') /\ valid_postream hist p'
          with _. iodiv_call_aux a o x k post hist p p'
        end
      end
    end
  end ;

  call o x k

(** Turning pre-/post-conditions into wp *)

unfold
let wprepost #a (pre : trace -> Type0) (post : trace -> branch a -> Type0) : wp a =
  fun p hist -> pre hist /\ (forall b. post hist b ==> p b)

let wprepost_id_inst #a (pre : trace -> Type0) (post : trace -> branch a -> Type0) (t : iodiv a (wprepost pre post)) (hist : trace) :
  Lemma
    (requires pre hist)
    (ensures theta t (post hist) hist)
= ()

(** repeat *)

(** Morally,
   t : IODiv unit
         (requires inv)
         (ensures fun hist r ->
           (terminates r /\ inv (hist @ tr)) \/
           (diverges r /\ inv (hist @ every_tr))
         )
   by subcomp.
   Maybe not necessary to talk about the computed wp of t.
*)
// let loop_preserving (w : wp unit) (inv : trace -> Type0) =
//   forall hist.
//     inv hist ==>
//     w (fun b ->
//       match b with
//       | Fin tr x -> inv (hist @ tr)
//       | Inf p -> forall n. inv (hist @ ipos_trace (stream_trunc p n))
//     ) hist

let downward_closed (inv : trace -> Type0) =
  forall tr tr'. tr `prefix_of` tr' ==> inv tr' ==> inv tr

let trace_invariant (inv : trace -> Type0) =
  inv [] /\
  downward_closed inv // /\
  // loop_preserving w inv

let wrepeat_inv (inv : trace -> Type0) : wp unit =
  fun post hist -> forall (p : iopostream). (forall n. inv (hist @ ipos_trace (stream_trunc p n))) ==> post (Inf p)

unfold
let winv (inv : trace -> Type0) : wp unit =
  wprepost inv (fun hist b ->
    match b with
    | Fin tr () -> inv (hist @ tr)
    | Inf p -> forall n. inv (hist @ ipos_trace (stream_trunc p n))
  )

let winv_inst (inv : trace -> Type0) (t : iodiv unit (winv inv)) (hist : trace) :
  Lemma
    (requires inv hist)
    (ensures
      theta t (fun b ->
        match b with
        | Fin tr () -> inv (hist @ tr)
        | Inf p -> forall n. inv (hist @ ipos_trace (stream_trunc p n))
      ) hist
    )
= ()

let winv_ret (inv : trace -> Type0) (t : iodiv unit (winv inv)) (hist : trace) (p : iopos) :
  Lemma
    (requires inv hist /\ isRet (t p))
    (ensures inv (hist @ ipos_trace p) /\ valid_trace hist (ipos_trace p))
= winv_inst inv t hist

let winv_event_stream (inv : trace -> Type0) (t : iodiv unit (winv inv)) (hist : trace) (p p' : iopostream) :
  Lemma
    (requires inv hist /\ event_stream t p /\ p `uptotau` p')
    (ensures (forall n. inv (hist @ ipos_trace (stream_trunc p' n))) /\ valid_postream hist p')
= winv_inst inv t hist ;
  theta_event_stream (winv inv) t (fun b ->
    match b with
    | Fin tr () -> inv (hist @ tr)
    | Inf p -> forall n. inv (hist @ ipos_trace (stream_trunc p n))
  ) hist p p'

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

let iodiv_repeat_inv_proof_aux_inf (inv : trace -> Type0) (body : iodiv unit (winv inv)) (post : wpost unit) (hist : trace) (p : iopostream) n :
  Lemma
    (requires inv hist /\ trace_invariant inv /\ event_stream (repeat body) p /\ event_stream body p)
    (ensures inv (hist @ ipos_trace (stream_trunc p n)) /\ valid_trace hist (ipos_trace (stream_trunc p n)))
= winv_event_stream inv body hist p p

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

// let iodiv_repeat_inv_proof_aux_overfin_None #w (body : iodiv unit w) (inv : trace -> Type0) (tr0 : trace) (post : wpost unit) (p : iopostream) (n n0 : nat) :
//   Lemma
//     (requires
//       inv tr0 /\
//       trace_invariant w inv /\
//       event_stream (repeat body) p /\
//       ~ (event_stream body p) /\
//       find_ret body [] (stream_trunc p n) == None /\
//       ~ (isEvent (body (stream_trunc p n0))) /\
//       (forall (m : nat). m < n0 ==> ~ (~ (isEvent (body (stream_trunc p m))))) /\
//       body (stream_trunc p n0) == None
//     )
//     (ensures inv (tr0 @ ipos_trace (stream_trunc p n)))
// = begin match find_ret body [] (stream_trunc p n0) with
//     | Some (x, q) ->
//       find_ret_prefix_prefix_of body [] (stream_trunc p n0) ;
//       // assert (find_ret_prefix body [] (stream_trunc p n0) `prefix_of` (stream_trunc p n0)) ;
//       prefix_of_stream_trunc p n0 (find_ret_prefix body [] (stream_trunc p n0)) ;
//       assert (exists (m : nat). m <= n0 /\ find_ret_prefix body [] (stream_trunc p n0) == stream_trunc p m) ;
//       assert (exists (m : nat). m <= n0 /\ isRet (body (stream_trunc p m))) ;
//       assert (forall (m : nat). m < n0 ==> isEvent (body (stream_trunc p m))) ;
//       assert (forall (m : nat). m < n0 ==> ~ (isRet (body (stream_trunc p m)))) ;
//       forall_below_and_eq (fun m -> ~ (isRet (body (stream_trunc p m)))) n0 ;
//       assert (forall (m : nat). m <= n0 ==> ~ (isRet (body (stream_trunc p m))))
//     | None ->
//       assert (isEvent (repeat body (stream_trunc p n0))) ;
//       repeat_unfold_1 body ;
//       assert (isEvent (bind body (fun _ -> tau ((if length (stream_trunc p n0) = 0 then (fun _ -> loop _) else itree_cofix_unfoldn (repeat_fix body) (length (stream_trunc p n0) - 1)) ())) (stream_trunc p n0)))
//     end

let iodiv_repeat_inv_proof_aux_overfin (inv : trace -> Type0) (body : iodiv unit (winv inv)) (post : wpost unit) (hist : trace) (p : iopostream) n :
  Lemma
    (requires inv hist /\ trace_invariant inv /\ event_stream (repeat body) p /\ ~ (event_stream body p) /\ find_ret body [] (stream_trunc p n) == None)
    (ensures inv (hist @ ipos_trace (stream_trunc p n)) /\ valid_trace hist (ipos_trace (stream_trunc p n)))
= // Similar to finite_branch_prefix
  // let n0 = indefinite_description_ghost_nat_min (fun n -> ~ (isEvent (body (stream_trunc p n)))) in
  // match body (stream_trunc p n0) with
  // | None -> iodiv_repeat_inv_proof_aux_overfin_None body inv tr0 post p n n0
  // | Some (Ret ()) ->
  //   assert (isRet (body (stream_trunc p n0))) ;
  //   assert (inv (tr0 @ ipos_trace (stream_trunc p n0))) ;
  //   if n < n0
  //   then begin
  //     stream_trunc_leq_prefix_of p n n0 ;
  //     ipos_trace_prefix_of (stream_trunc p n) (stream_trunc p n0) ;
  //     prefix_of_append_left (ipos_trace (stream_trunc p n)) (ipos_trace (stream_trunc p n0)) tr0
  //   end
  //   else begin
  //     find_ret_append body ;
  //     assert (Some? (find_ret body [] (stream_trunc p n0 @ skipn n0 (stream_trunc p n)))) ;
  //     calc (==) {
  //       stream_trunc p n ;
  //       == { splitAt_eq n0 (stream_trunc p n) }
  //       firstn n0 (stream_trunc p n) @ skipn n0 (stream_trunc p n) ;
  //       == { firstn_stream_trunc_left n0 n p }
  //       stream_trunc p n0 @ skipn n0 (stream_trunc p n) ;
  //     } ;
  //     assert (Some? (find_ret body [] (stream_trunc p n)))
  //   end
  admit ()

let rec iodiv_repeat_inv_proof_aux (inv : trace -> Type0) (body : iodiv unit (winv inv)) (post : wpost unit) (hist : trace) (p : iopostream) (n : nat) :
  Lemma
    (requires inv hist /\ trace_invariant inv /\ event_stream (repeat body) p)
    (ensures inv (hist @ ipos_trace (stream_trunc p n)) /\ valid_trace hist (ipos_trace (stream_trunc p n)))
    (decreases n)
= match find_ret body [] (stream_trunc p n) with
  | Some ((), q) ->
    assert (isRet (body (find_ret_prefix body [] (stream_trunc p n)))) ;
    winv_ret inv body hist (find_ret_prefix body [] (stream_trunc p n)) ;
    assert (inv (hist @ ipos_trace (find_ret_prefix body [] (stream_trunc p n)))) ;
    assert (valid_trace hist (ipos_trace (find_ret_prefix body [] (stream_trunc p n)))) ;
    find_ret_Some_pos body [] (stream_trunc p n) ;
    assert (stream_trunc p n == (find_ret_prefix body [] (stream_trunc p n)) @ q) ;
    ipos_trace_append (find_ret_prefix body [] (stream_trunc p n)) q ;
    append_assoc hist (ipos_trace (find_ret_prefix body [] (stream_trunc p n))) (ipos_trace q) ;
    begin match q with
    | [] -> ()
    | Tau_choice :: q' ->
      event_stream_repeat_one_ret body p n q' ;
      repeat_inv_proof_aux_smaller body n p (find_ret_prefix body [] (stream_trunc p n)) q' ;
      iodiv_repeat_inv_proof_aux inv body post (hist @ ipos_trace (find_ret_prefix body [] (stream_trunc p n))) (stream_drop (1 + length (find_ret_prefix body [] (stream_trunc p n))) p) (n - 1 - length (find_ret_prefix body [] (stream_trunc p n))) ;
      repeat_inv_proof_aux_eqpos p (find_ret_prefix body [] (stream_trunc p n)) q' n ;
      assert (inv ((hist @ ipos_trace (find_ret_prefix body [] (stream_trunc p n))) @ ipos_trace q')) ;
      valid_trace_append hist (ipos_trace (find_ret_prefix body [] (stream_trunc p n))) (ipos_trace q') ;
      assert (valid_trace hist ((ipos_trace (find_ret_prefix body [] (stream_trunc p n))) @ ipos_trace q'))
    | c :: q' ->
      assert (isEvent (repeat body (stream_trunc p n))) ;
      repeat_unfold_1 body
    end
  | None ->
    // In case where we still haven't reached a return, we do a case
    // analysis on wheter there will ever be such a return.
    eliminate (event_stream body p) \/ ~ (event_stream body p)
    returns inv (hist @ ipos_trace (stream_trunc p n)) /\ valid_trace hist (ipos_trace (stream_trunc p n))
    with h. iodiv_repeat_inv_proof_aux_inf inv body post hist p n
    and  h. iodiv_repeat_inv_proof_aux_overfin inv body post hist p n

// let iodiv_repeat_inv_proof #w (body : iodiv unit w) (inv : trace -> Type0) :
//   Lemma
//     (requires trace_invariant w inv)
//     (ensures
//       forall (post : wpost unit) (p p' : iopostream).
//         event_stream (repeat body) p ==>
//         p `uptotau` p' ==>
//         (forall n. inv (ipos_trace (stream_trunc p' n)))
//     )
// = let aux (post : wpost unit) (p p' : iopostream) n :
//     Lemma
//       (requires event_stream (repeat body) p)
//       (ensures inv (ipos_trace (stream_trunc p n)))
//       [SMTPat ()]
//   = iodiv_repeat_inv_proof_aux body inv [] post p n
//   in
//   forall_intro_2 (move_requires_2 (embeds_trace_implies inv))

let iodiv_repeat_inv_proof (inv : trace -> Type0) (body : iodiv unit (winv inv)) (post : wpost unit) (hist : trace) (p p' : iopostream) :
  Lemma
    (requires trace_invariant inv /\ wrepeat_inv inv post hist /\ event_stream (repeat body) p /\ p `uptotau` p')
    (ensures post (Inf p') /\ valid_postream hist p')
= admit ()

let iodiv_repeat_with_inv (inv : trace -> Type0) (body : iodiv unit (winv inv)) :
  Pure (iodiv unit (wrepeat_inv inv)) (requires trace_invariant inv) (ensures fun _ -> True)
= introduce forall (post : wpost unit) (hist : trace). wrepeat_inv inv post hist ==> theta (repeat body) post hist
  with begin
    introduce wrepeat_inv inv post hist ==> theta (repeat body) post hist
    with _. begin
      // fin
      introduce forall p. isRet (repeat body p) ==> post (Fin (ipos_trace p) (ret_val (repeat body p))) /\ valid_trace hist (ipos_trace p)
      with begin
        repeat_not_ret body p
      end ;

      // inf
      introduce forall (p p' : iopostream). event_stream (repeat body) p ==> p `uptotau` p' ==> post (Inf p') /\ valid_postream hist p'
      with begin
        introduce event_stream (repeat body) p ==> (p `uptotau` p' ==> post (Inf p') /\ valid_postream hist p')
        with _. begin
          introduce p `uptotau` p' ==> post (Inf p') /\ valid_postream hist p'
          with _. begin
            iodiv_repeat_inv_proof inv body post hist p p'
          end
        end
      end
    end
  end ;

  repeat body

let iodiv_subcomp (a : Type) (w1 w2 : wp a) (m : iodiv a w1) :
  Pure (iodiv a w2) (requires w2 `stronger_wp` w1) (ensures fun _ -> True)
= m

let wite #a (w1 w2 : wp a) (b : bool) : wp a =
  fun post hist -> (b ==> w1 post hist) /\ (~ b ==> w2 post hist)

let iodiv_if_then_else (a : Type) (w1 w2 : wp a) (f : iodiv a w1) (g : iodiv a w2) (b : bool) : Type =
  iodiv a (wite w1 w2 b)

(* In order for F* to accept it, we must remove the refinement *)
let iodiv_bind' a b w wf (m : iodiv a w) (f : (x : a) -> iodiv b (wf x)) : iodiv b (wbind w wf) =
  iodiv_bind a b w wf m f

(** Predicates *)

let terminates #a : wpost a =
  fun b -> Fin? b

let diverges #a : wpost a =
  fun b -> Inf? b

// let repeat_ret_loops () :
//   Lemma (wrepeat_inv (wret ()) (fun _ -> True) diverges)
// = ()


(** Making the effect partial *)

unfold
let wTrue a : wpost a =
  fun _ -> True

// Since the pre-condition is not a prop, it's not clear what to do here
// Use the empty history? Quantify over every history?
// Do we have to pass hist around instead?
// Say you take read which requires the history to guarantee the file is open, it should not check in isolation
// but should check after open. Also how to make use of ambient assumptions over the history? How do they materialise? Via subcomp.
// The precondition / partiality is really just an illusion, the only issue is getting the lift from PURE in fact
// Maybe easier to see with how we would define wlift
(*
let piodiv a (w : wp a) =
  squash (w (wTrue a)) -> iodiv a w

let piodiv_ret a (x : a) : piodiv a (wret x) =
  fun _ -> iodiv_ret a x

// We use pwbind instead of wbind to get the precondition
unfold
let pwbind #a #b (w : wp a) (wf : a -> wp b) : wp b =
  fun post -> w (wTrue a) /\ wbind w wf post

// TODO MOVE
let wbind_inst #a #b (w : wp a) (wf : a -> wp b) (post : wpost b) :
  Lemma
    (requires wbind w wf post)
    (ensures
      w (fun b ->
        match b with
        | Fin tr x -> wf x (shift_post tr post)
        | Inf p -> post (Inf p)
      )
    )
= ()

let shift_post_unfold #a (tr : trace) (post : wpost a) :
  Lemma (
    shift_post tr post ==
    (fun b ->
      match b with
      | Fin tr' x -> post (Fin (tr @ tr') x)
      | Inf p -> forall (p' : iopostream). stream_prepend (trace_to_pos tr) p `uptotau` p' ==> post (Inf p'))
  )
= ()

let shift_post_True a (tr : trace) :
  Lemma (shift_post tr (wTrue a) == wTrue a)
= calc (==) {
    shift_post tr (wTrue a) ;
    == { shift_post_unfold tr (wTrue a) }
    begin fun (b : branch a) -> match b with
    | Fin tr' x -> wTrue a (Fin (tr @ tr') x)
    | Inf p -> forall (p' : iopostream). stream_prepend (trace_to_pos tr) p `uptotau` p' ==> wTrue a (Inf p')
    end ;
    == { _ by (norm [ nbe ; iota ; delta ]) }
    begin fun (b : branch a) -> match b with
    | Fin tr' x -> True
    | Inf p -> forall (p' : iopostream). stream_prepend (trace_to_pos tr) p `uptotau` p' ==> True
    end ;
    == {}
    begin fun (b : branch a) -> match b with
    | Fin tr' x -> True
    | Inf p -> True
    end ;
    == {}
    begin fun (b : branch a) -> True end ;
    == {}
    wTrue a ;
  }

let piodiv_bind a b w wf (m : piodiv a w) (f : (x:a) -> piodiv b (wf x)) : piodiv b (pwbind w wf) =
  fun h ->
    assert (wbind w wf (wTrue b)) ;
    wbind_inst w wf (wTrue b) ;
    assert (forall p. isRet (m () p) ==> wf (ret_val (m () p)) (shift_post (ipos_trace p) (wTrue b))) ;
    forall_intro (shift_post_True b) ;
    assert (forall p. isRet (m () p) ==> wf (ret_val (m () p)) (wTrue b)) ;
    assert (forall x. x `return_of` m () ==> wf x (wTrue b)) ;
    iodiv_bind a b w wf (m ()) (fun x -> f x ())

(** We don't really need tau do we? *)

let piodiv_call #a (o : cmds) (x : io_args o) #w (k : (r : io_res o) -> piodiv a (w r)) : piodiv a (wcall o x w) =
  fun h ->
    assert (wcall o x w (wTrue a)) ;
    forall_intro (shift_post_True a) ;
    assert (forall (y : io_res o). w y (wTrue a)) ;
    iodiv_call a o x (fun z -> k z ())

let pwrepeat_inv (w : wp unit) (inv : trace -> Type0) : wp unit =
  fun post -> w (wTrue unit) /\ wrepeat_inv w inv post

let piodiv_repeat_with_inv #w (body : piodiv unit w) (inv : trace -> Type0) :
  Pure (piodiv unit (pwrepeat_inv w inv)) (requires trace_invariant w inv) (ensures fun _ -> True)
= fun h -> iodiv_repeat_with_inv (body ()) inv

let piodiv_subcomp (a : Type) (w1 w2 : wp a) (m : piodiv a w1) :
  Pure (piodiv a w2) (requires w2 `stronger_wp` w1) (ensures fun _ -> True)
= m

let piodiv_if_then_else (a : Type) (w1 w2 : wp a) (f : piodiv a w1) (g : piodiv a w2) (b : bool) : Type =
  piodiv a (wite w1 w2 b)

let wlift #a (w : pure_wp a) : wp a =
  fun post -> w (fun x -> post (Fin [] x))

let wlift_unfold #a (w : pure_wp a) post :
  Lemma (wlift w post == w (fun x -> post (Fin [] x)))
= ()

let elim_pure #a #w (f : unit -> PURE a w) :
  Pure
    a
    (requires w (fun _ -> True))
    (ensures fun r -> forall post. w post ==> post r)
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall () ;
  f ()

let lift_pure_piodiv (a : Type) (w : pure_wp a) (f:(eqtype_as_type unit -> PURE a w)) : piodiv a (wlift w) =
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
    let r = elim_pure #a #w f in
    assert (forall post. w post ==> post r) ;
    let r' : iodiv a (wret r) = iodiv_ret a r in
    iodiv_subcomp _ (wret r) (wlift w) r'

[@@allow_informative_binders]
reflectable reifiable total layered_effect {
  IODIV : a:Type -> w:wp a -> Effect
  with
    repr         = piodiv ;
    return       = piodiv_ret ;
    bind         = piodiv_bind ;
    subcomp      = piodiv_subcomp ;
    if_then_else = piodiv_if_then_else
}

sub_effect PURE ~> IODIV = lift_pure_piodiv

effect IODiv (a : Type) (pre : Type0) (post : wpost a) =
  IODIV a (fun p -> pre /\ (forall x. post x ==> p x))

// TODO MOVE
let ret_trace #a (r : branch a) : Pure trace (requires terminates r) (ensures fun _ -> True) =
  match r with
  | Fin tr x -> tr

let result #a (r : branch a) : Pure a (requires terminates r) (ensures fun _ -> True) =
  match r with
  | Fin tr x -> x

let act_call (o : cmds) (x : io_args o) : IODiv (io_res o) (requires True) (ensures fun r -> terminates r /\ ret_trace r == [ choice_to_event (Call_choice o x (result r)) ]) =
  IODIV?.reflect (piodiv_call o x (fun y -> piodiv_ret _ y))

let open_file (s : string) : IODiv file_descr (requires True) (ensures fun r -> terminates r /\ ret_trace r == [ EOpenfile s (result r) ]) =
  act_call Openfile s

let read (fd : file_descr) : IODiv string (requires True) (ensures fun r -> terminates r /\ ret_trace r == [ ERead fd (result r) ]) =
  act_call Read fd

let close (fd : file_descr) : IODiv unit (requires True) (ensures fun r -> terminates r /\ ret_trace r == [ EClose fd (result r) ]) =
  act_call Close fd

let repeat_inv #w (body : unit -> IODIV unit w) (inv : (trace -> Type0) { trace_invariant w inv }) : IODIV unit (pwrepeat_inv w inv) =
  IODIV?.reflect (piodiv_repeat_with_inv (reify (body ())) inv)
*)
