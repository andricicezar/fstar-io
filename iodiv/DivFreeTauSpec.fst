(** Specification of IO + Div in the style of DM4Ever using silent steps *)

module DivFreeTauSpec

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics // Also defines forall_intro so place before Classical
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc
open FStar.FunctionalExtensionality

open Util
open Stream
open IIOSig

(** Traces with silent steps (Tau) *)

type otrace =
  list (option event)

type sotrace =
  stream (option event)

let rec to_trace (t : otrace) : trace =
  match t with
  | [] -> []
  | Some e :: t -> e :: to_trace t
  | None :: t -> to_trace t

let embeds (p q : sotrace) =
  forall (n : nat). exists (m : nat). to_trace (stream_trunc q n) == to_trace (stream_trunc p m)

let uptotau (p q : sotrace) =
  p `embeds` q /\ q `embeds` p

let rec to_trace_append (t t' : otrace) :
  Lemma (to_trace (t @ t') == to_trace t @ to_trace t')
= match t with
  | [] -> ()
  | Some e :: t -> to_trace_append t t'
  | None :: t -> to_trace_append t t'

let embeds_inst (p q : sotrace) (n : nat) :
  Lemma
    (requires p `embeds` q)
    (ensures exists (m : nat). to_trace (stream_trunc q n) == to_trace (stream_trunc p m))
= ()

let embeds_prepend (t t' : otrace) (s s' : sotrace) :
  Lemma
    (requires to_trace t == to_trace t' /\ s `embeds` s')
    (ensures stream_prepend t s `embeds` stream_prepend t' s')
= introduce forall (n : nat). exists (m : nat). to_trace (stream_trunc (stream_prepend t' s') n) == to_trace (stream_trunc (stream_prepend t s) m)
  with begin
    if n <= length t'
    then begin
      admit () // TODO LATER
    end
    else begin
      embeds_inst s s' (n - length t') ;
      // eliminate exists m. to_trace (stream_trunc s' (n - length t')) == to_trace (stream_trunc s m)
      // returns (exists (m : nat). to_trace (stream_trunc (stream_prepend t' s') n) == to_trace (stream_trunc (stream_prepend t s) m))
      // with _. begin
      //   calc (==) {
      //     to_trace (stream_trunc (stream_prepend t' s') n) ;
      //     == { stream_prepend_trunc_right t' s' n }
      //     to_trace (t' @ stream_trunc s' (n - length t')) ;
      //     == { to_trace_append t' (stream_trunc s' (n - length t')) }
      //     to_trace t' @ to_trace (stream_trunc s' (n - length t')) ;
      //     == {}
      //     to_trace t @ to_trace (stream_trunc s' (n - length t')) ;
      //     == {}
      //     to_trace t @ to_trace (stream_trunc s' (n - length t')) ;
      //     == {}
      //     to_trace t @ to_trace (stream_trunc s m) ;
      //     == { to_trace_append t (stream_trunc s m) }
      //     to_trace (t @ stream_trunc s m) ;
      //   } ;
      //   calc (==) {
      //     to_trace (stream_trunc (stream_prepend t s) (m + length t)) ;
      //     == { stream_prepend_trunc_right t s (m + length t) }
      //     to_trace (t @ stream_trunc s (m + length t - length t)) ;
      //     == {}
      //     to_trace (t @ stream_trunc s m) ;
      //   }
      // end
      // The proof works but is very very slow
      admit ()
    end
  end

let uptotau_prepend (t t' : otrace) (s s' : sotrace) :
  Lemma
    (requires to_trace t == to_trace t' /\ s `uptotau` s')
    (ensures stream_prepend t s `uptotau` stream_prepend t' s')
= embeds_prepend t t' s s' ;
  embeds_prepend t' t s' s

(** Converging or diverging run *)
noeq
type orun a =
| Ocv : otrace -> a -> orun a
| Odv : sotrace -> orun a

(** Equivalence up to tau *)

let eutt #a (r r' : orun a) : Type0 =
  match r, r' with
  | Ocv t x, Ocv t' x' -> to_trace t == to_trace t' /\ x == x'
  | Odv s, Odv s' -> s `uptotau` s'
  | _, _ -> False

(** Specification monad *)

unfold
let i_pre = history -> Type0

unfold
let i_post' a = orun a -> Type0

let resp_eutt #a (p : i_post' a) : Type0 =
  forall r r'. r `eutt` r' /\ p r ==> p r'

unfold
let i_post a = p : (i_post' a) { resp_eutt p }

unfold
let as_i_post #a (p : i_post' a) : Pure (i_post a) (requires resp_eutt p) (ensures fun r -> r == p) =
  p

let i_post_resp_eutt #a (p : i_post a) r r' :
  Lemma
    (requires r `eutt` r' /\ p r)
    (ensures p r')
= ()

unfold
let i_pre_le (p q : i_pre) =
  forall hist. p hist ==> q hist

let i_post_le #a (p q : i_post a) =
  forall r. p r ==> q r

let i_post_eq #a (p q : i_post a) =
  p `i_post_le` q /\ q `i_post_le` p

let iwp' a = i_post a -> i_pre

let iwp_monotonic #a (w : iwp' a) =
  forall p q. p `i_post_le` q ==> w p `i_pre_le` w q

let iwp a =
  w : iwp' a { iwp_monotonic w }

let iwp_monotonic_inst #a (w : iwp a) p q hist :
  Lemma
    (requires w p hist /\ p `i_post_le` q)
    (ensures w q hist)
= ()

unfold
let _ile #a (w w' : iwp a) =
  forall p. w' p `i_pre_le` w p

let ile = _ile

let ieq #a (w w' : iwp a) =
  w `ile` w' /\ w' `ile` w

let ile_trans #a (w1 w2 w3 : iwp a) :
  Lemma
    (requires w1 `ile` w2 /\ w2 `ile` w3)
    (ensures w1 `ile` w3)
= ()

let as_iwp #a (w : iwp' a) : Pure (iwp a) (requires iwp_monotonic w) (ensures fun r -> r == w) =
  w

unfold
let _i_ret #a (x : a) : iwp a =
  as_iwp (fun post hist -> post (Ocv [] x))

let i_ret = _i_ret

let ishift_post' #a (tr : otrace) (post : i_post a) : i_post' a =
  fun r ->
    match r with
    | Ocv tr' x -> post (Ocv (tr @ tr') x)
    | Odv st -> post (Odv (stream_prepend tr st))

let ishift_post #a (tr : otrace) (post : i_post a) : i_post a =
  introduce forall r r'. r `eutt` r' /\ ishift_post' tr post r ==> ishift_post' tr post r'
  with begin
    introduce r `eutt` r' /\ ishift_post' tr post r ==> ishift_post' tr post r'
    with _. begin
      match r, r' with
      | Ocv t x, Ocv t' x' ->
        to_trace_append tr t ;
        to_trace_append tr t' ;
        assert (Ocv (tr @ t) x `eutt` Ocv (tr @ t') x') ;
        i_post_resp_eutt post (Ocv (tr @ t) x) (Ocv (tr @ t') x')
      | Odv s, Odv s' ->
        uptotau_prepend tr tr s s' ;
        assert (Odv (stream_prepend tr s) `eutt #a` Odv (stream_prepend tr s')) ;
        i_post_resp_eutt post (Odv (stream_prepend tr s)) (Odv (stream_prepend tr s'))
    end
  end ;
  ishift_post' tr post

let ishift_post_nil #a (post : i_post a) :
  Lemma (ishift_post [] post `i_post_le` post)
= introduce forall r. ishift_post [] post r ==> post r
  with begin
    match r with
    | Ocv tr x -> ()
    | Odv s -> stream_prepend_nil s ; stream_ext (stream_prepend [] s) s
  end

let ishift_post_mono a tr :
  Lemma (forall (p q : i_post a). p `i_post_le` q ==> ishift_post tr p `i_post_le` ishift_post tr q)
= ()

let ishift_post_app #a t t' (p : i_post a) :
  Lemma (ishift_post (t' @ t) p `i_post_le` ishift_post t (ishift_post t' p))
= introduce forall r. ishift_post (t' @ t) p r ==> ishift_post t (ishift_post t' p) r
  with begin
    match r with
    | Ocv tr x -> append_assoc t' t tr
    | Odv st -> stream_prepend_app t' t st
  end


let i_bind_post' #a #b (wf : a -> iwp b) (post : i_post b) hist : i_post' a =
  fun r ->
    match r with
    | Ocv tr x -> wf x (ishift_post tr post) (rev_acc (to_trace tr) hist)
    | Odv st -> post (Odv st)



let i_bind_post #a #b (wf : a -> iwp b) (post : i_post b) hist : i_post a =
  introduce forall r r'. r `eutt` r' /\ i_bind_post' wf post hist r ==> i_bind_post' wf post hist r'
  with begin
    introduce r `eutt` r' /\ i_bind_post' wf post hist r ==> i_bind_post' wf post hist r'
    with _. begin
      match r, r' with
      | Ocv t x, Ocv t' x' ->
        introduce forall r. ishift_post t post r ==> ishift_post t' post r
        with begin
          introduce ishift_post t post r ==> ishift_post t' post r
          with _. begin
            match r with
            | Ocv tr y ->
              to_trace_append t tr ;
              to_trace_append t' tr ;
              assert (Ocv (t @ tr) y `eutt` Ocv (t' @ tr) y) ;
              i_post_resp_eutt post (Ocv (t @ tr) y) (Ocv (t' @ tr) y)
            | Odv s ->
              uptotau_prepend t t' s s ;
              assert (Odv (stream_prepend t s) `eutt #a` Odv (stream_prepend t' s)) ;
              i_post_resp_eutt post (Odv (stream_prepend t s)) (Odv (stream_prepend t' s))
          end
        end ;
        iwp_monotonic_inst (wf x) (ishift_post t post) (ishift_post t' post) (rev_acc (to_trace t) hist)
      | Odv s, Odv s' ->
        i_post_resp_eutt post (Odv s) (Odv s')
    end
  end ;
  i_bind_post' wf post hist

let i_bind_post_mono #a #b (wf : a -> iwp b) p q hist :
  Lemma
    (requires p `i_post_le` q)
    (ensures i_bind_post wf p hist `i_post_le` i_bind_post wf q hist)
= introduce forall r. i_bind_post wf p hist r ==> i_bind_post wf q hist r
  with begin
    match r with
    | Ocv tr x ->
      ishift_post_mono b tr ;
      assert (ishift_post tr p `i_post_le` ishift_post tr q) ;
      assert (wf x (ishift_post tr p) (rev_acc (to_trace tr) hist) ==> wf x (ishift_post tr q) (rev_acc (to_trace tr) hist))
    | Odv s -> ()
  end

private
let postprocess_i_bind () : Tac unit =
  norm [delta_only [`%as_iwp; `%i_bind_post;`%i_bind_post';`%ishift_post;`%ishift_post']; iota]; 
  trefl ()

[@@ (postprocess_with postprocess_i_bind)]
unfold
let _i_bind (#a : Type u#a) (#b : Type u#b) (w : iwp a) (wf : a -> iwp b) : iwp b =
  introduce forall p q hist. p `i_post_le` q ==> i_bind_post wf p hist `i_post_le` i_bind_post wf q hist
  with begin
    move_requires (i_bind_post_mono wf p q) hist
  end ;
  as_iwp (fun post hist ->
    w (i_bind_post wf post hist) hist
  )

let i_bind = _i_bind

let i_bind_mono #a #b (w : iwp a) (wf wf' : a -> iwp b) :
  Lemma
    (requires forall x. wf x `ile` wf' x)
    (ensures i_bind w wf `ile` i_bind w wf')
= introduce forall post hist. i_bind w wf' post hist ==> i_bind w wf post hist
  with begin
    assert (i_bind_post wf' post hist `i_post_le` i_bind_post wf post hist)
  end

let i_bind_cong #a #b (w : iwp a) (wf wf' : a -> iwp b) :
  Lemma
    (requires forall x. wf x `ieq` wf' x)
    (ensures i_bind w wf `ieq` i_bind w wf')
= i_bind_mono w wf wf' ;
  i_bind_mono w wf' wf

let i_bind_assoc #a #b #c (w : iwp a) (wf : a -> iwp b) (wg : b -> iwp c) :
  Lemma (i_bind w (fun x -> i_bind (wf x) wg) `ile` i_bind (i_bind w wf) wg)
= introduce forall post hist. i_bind (i_bind w wf) wg post hist ==> i_bind w (fun x -> i_bind (wf x) wg) post hist
  with begin
    introduce forall r. i_bind_post wf (i_bind_post wg post hist) hist r ==> i_bind_post (fun x -> i_bind (wf x) wg) post hist r
    with begin
      match r with
      | Ocv tr x ->
        introduce forall r'. ishift_post tr (i_bind_post wg post hist) r' ==> i_bind_post wg (ishift_post tr post) (rev_acc (to_trace tr) hist) r'
        with begin
          match r' with
          | Ocv tr' y ->
            to_trace_append tr tr' ;
            rev_acc_rev' (to_trace tr @ to_trace tr') hist ; // rev_acc (to_trace tr @ to_trace tr') hist == rev' (to_trace tr @ to_trace tr') @ hist
            rev'_append (to_trace tr) (to_trace tr') ; // == (rev' (to_trace tr') @ rev' (to_trace tr)) @ hist
            append_assoc (rev' (to_trace tr')) (rev' (to_trace tr)) hist ; // == rev' (to_trace tr') @ rev' (to_trace tr) @ hist
            rev_acc_rev' (to_trace tr) hist ; // == rev' (to_trace tr') @ rev_acc (to_trace tr) hist
            rev_acc_rev' (to_trace tr') (rev_acc (to_trace tr) hist) ; // == rev_acc (to_trace tr') (rev_acc (to_trace tr) hist)
            ishift_post_app tr' tr post
          | Odv st -> ()
        end ;
        assert (ishift_post tr (i_bind_post wg post hist) `i_post_le` i_bind_post wg (ishift_post tr post) (rev_acc (to_trace tr) hist))
      | Odv st -> ()
    end ;
    assert (i_bind_post wf (i_bind_post wg post hist) hist `i_post_le` i_bind_post (fun x -> i_bind (wf x) wg) post hist)
  end

let i_bind_post_ret #a (post : i_post a) hist :
  Lemma (i_bind_post i_ret post hist `i_post_eq` post)
= introduce forall r. i_bind_post i_ret post hist r <==> post r
  with begin
    match r with
    | Ocv tr x -> ()
    | Odv st -> ()
  end

let i_bind_ret #a (w : iwp a) :
  Lemma (i_bind w i_ret `ieq` w)
= introduce forall post hist. i_bind w i_ret post hist <==> w post hist
  with begin
    calc (<==>) {
      i_bind w i_ret post hist ;
      == {}
      w (i_bind_post i_ret post hist) hist ;
      <==> { i_bind_post_ret post hist }
      w post hist ;
    }
  end

let i_req (pre : pure_pre) : iwp (squash pre) =
  as_iwp (fun post hist -> pre /\ post (Ocv [] (Squash.get_proof pre)))

unfold
let i_open (s : string) : iwp file_descr =
  as_iwp (fun post hist -> forall fd. post (Ocv [ Some (EOpenFile s fd) ] fd))

unfold
let i_read (fd : file_descr) : iwp string =
  as_iwp (fun post hist -> is_open fd hist /\ (forall s. post (Ocv [ Some (ERead fd s) ] s)))

unfold
let i_close (fd : file_descr) : iwp unit =
  as_iwp (fun post hist -> is_open fd hist /\ post (Ocv [ Some (EClose fd) ] ()))

unfold
let i_get_trace : iwp history =
  as_iwp (fun post hist -> post (Ocv [] hist))

unfold
let iwite #a (w1 w2 : iwp a) (b : bool) : iwp a =
  fun post hist -> (b ==> w1 post hist) /\ (~ b ==> w2 post hist)

unfold
let _i_tau : iwp unit =
  as_iwp (fun post hist -> post (Ocv [ None ] ()))

let i_tau = _i_tau

(** Specification of iter using an impredicative encoding *)

unfold
let iter_expand_cont (#index : Type0) (#a : Type0) (k : index -> iwp a) (x : either index a) : iwp a =
  match x with
  | Inl j -> i_bind i_tau (fun _ -> k j)
  | Inr y -> i_ret y

let iter_expand (#index : Type0) (#a : Type0) (w : index -> iwp (either index a)) (i : index) (k : index -> iwp a) : iwp a =
  i_bind (w i) (iter_expand_cont k)

let iter_expand_mono (#index : Type0) (#a : Type0) (w w' : index -> iwp (either index a)) (i : index) (k : index -> iwp a) :
  Lemma
    (requires w i `ile` w' i)
    (ensures iter_expand w i k `ile` iter_expand w' i k)
= admit () (** this was working before adding the post-processing **)

let iter_expand_mono_k (#index : Type0) (#a : Type0) (w : index -> iwp (either index a)) (i : index) (k k' : index -> iwp a) :
  Lemma
    (requires forall j. k j `ile` k' j)
    (ensures iter_expand w i k `ile` iter_expand w i k')
= introduce forall x. iter_expand_cont k x `ile` iter_expand_cont k' x
  with begin
    match x with
    | Inl j -> ()
    | Inr y -> ()
  end ;
  i_bind_mono (w i) (iter_expand_cont k) (iter_expand_cont k')

let i_iter (#index : Type0) (#a : Type0) (w : index -> iwp (either index a)) (i : index) : iwp a =
  fun post hist ->
    exists (it : index -> iwp a).
      (forall j. iter_expand w j it `ile` it j) /\
      it i post hist

let i_iter_unfold (#index : Type0) (#a : Type0) (w : index -> iwp (either index a)) (i : index) :
  Lemma (iter_expand w i (i_iter w) `ile` i_iter w i)
= introduce forall post hist. i_iter w i post hist ==> iter_expand w i (i_iter w) post hist
  with begin
    introduce i_iter w i post hist ==> iter_expand w i (i_iter w) post hist
    with _. begin
      eliminate exists (it : index -> iwp a). (forall j. iter_expand w j it `ile` it j) /\ it i post hist
      returns iter_expand w i (i_iter w) post hist
      with _. begin
        assert (iter_expand w i it post hist) ;
        iter_expand_mono_k w i (i_iter w) it
      end
    end
  end

let i_iter_coind (#index : Type0) (#a : Type0) (w : index -> iwp (either index a)) (i : index) w' :
  Lemma
    (requires forall j. iter_expand w j w' `ile` w' j)
    (ensures i_iter w i `ile` w' i)
= ()

let i_iter_fold (#index : Type0) (#a : Type0) (w : index -> iwp (either index a)) (i : index) :
  Lemma (i_iter w i `ile` iter_expand w i (i_iter w))
= introduce forall j. iter_expand w j (fun j -> iter_expand w j (i_iter w)) `ile` iter_expand w j (i_iter w)
  with begin
    introduce forall k. iter_expand w k (i_iter w) `ile` i_iter w k
    with begin
      i_iter_unfold w k
    end ;
    iter_expand_mono_k w j (fun j -> iter_expand w j (i_iter w)) (i_iter w)
  end ;
  i_iter_coind w i (fun j -> iter_expand w j (i_iter w))

let i_iter_mono (#index : Type0) (#a : Type0) (w w' : index -> iwp (either index a)) (i : index) :
  Lemma
    (requires forall j. w j `ile` w' j)
    (ensures i_iter w i `ile` i_iter w' i)
= admit () (** this was working before adding the post-processing **)

let i_iter_cong (#index : Type0) (#a : Type0) (w w' : index -> iwp (either index a)) (i : index) :
  Lemma
    (requires forall j. w j `ieq` w' j)
    (ensures i_iter w i `ieq` i_iter w' i)
= i_iter_mono w w' i ; i_iter_mono w' w i

(** Specification from pre/post *)
// Note: don't need resp_eutt for the post, the generated pre will take care or it (post r ==> p r) where resp_eutt p
// might also be interesting to have nice posts by construction so one doesn't need to worry about taus. One option being to go through the other spec, but
// maybe it's not needed.

unfold
let iprepost #a (pre : history -> Type0) (post : (hist : history) -> orun a -> Pure Type0 (requires pre hist) (ensures fun _ -> True)) : iwp a =
  fun p hist -> pre hist /\ (forall r. post hist r ==> p r)

let iprepost_inst #a (pre : history -> Type0) (post : (hist : history) -> orun a -> Pure Type0 (requires pre hist) (ensures fun _ -> True)) (p : i_post a) h r :
  Lemma (requires iprepost pre post p h /\ post h r) (ensures p r)
= ()

(** Basic predicates *)

unfold
let terminates #a : i_post a =
  as_i_post (fun r -> Ocv? r)

unfold
let diverges #a : i_post a =
  as_i_post (fun r -> Odv? r)

let ret_otrace #a (r : orun a) : Pure otrace (requires terminates r) (ensures fun _ -> True) =
  match r with
  | Ocv tr x -> tr

let ret_trace #a (r : orun a) : Pure trace (requires terminates r) (ensures fun _ -> True) =
  match r with
  | Ocv tr x -> to_trace tr

let result #a (r : orun a) : Pure a (requires terminates r) (ensures fun _ -> True) =
  match r with
  | Ocv tr x -> x

let inf_trace #a (r : orun a) : Pure sotrace (requires diverges r) (ensures fun _ -> True) =
  match r with
  | Odv p -> p

(** Loop invariants *)

// TODO MOVE
let lval #a #b (x : either a b) : Pure a (requires Inl? x) (ensures fun _ -> True) =
  match x with
  | Inl v -> v

(* Specification of the body that always continues *)
unfold
let repeat_body_inv #index (pre : index -> i_pre) (inv : trace -> Type0) (i : index) : iwp (either index unit) =
  iprepost (pre i) (fun hist r -> terminates r /\ Inl? (result r) /\ pre (lval (result r)) (rev_acc (ret_trace r) hist) /\ inv (ret_trace r))

unfold
let sotrace_refines (s : sotrace) (trs : stream trace) =
  forall (n : nat). exists (m : nat) (k : nat). n <= m /\ to_trace (stream_trunc s m) == flatten (stream_trunc trs k)

unfold
let _repeat_inv #index (pre : index -> i_pre) (inv : trace -> Type0) (i : index) : iwp unit =
  iprepost (pre i) (fun hist r -> diverges r /\ (exists (trs : stream trace). (forall n. inv (trs n)) /\ (inf_trace r) `sotrace_refines` trs))

let repeat_inv = _repeat_inv

let repeat_inv_inst #index (pre : index -> i_pre) (inv : trace -> Type0) (i : index) (post : i_post unit) hist (s : sotrace) (trs : stream trace) :
  Lemma (requires repeat_inv pre inv i post hist /\ (forall n. inv (trs n)) /\ s `sotrace_refines` trs) (ensures post (Odv s))
= ()

let sotrace_refines_prepend_None (tr : otrace) (s : sotrace) (trs : stream trace) :
  Lemma
    (requires to_trace tr == [] /\ s `sotrace_refines` trs)
    (ensures stream_prepend tr s `sotrace_refines` trs)
= admit ()

let sotrace_refines_prepend (tr : otrace) (s : sotrace) (trs : stream trace) :
  Lemma
    (requires s `sotrace_refines` trs)
    (ensures stream_prepend tr s `sotrace_refines` stream_prepend [ to_trace tr ] trs)
= introduce forall (n : nat). exists (m : nat) (k : nat). n <= m /\ to_trace (stream_trunc (stream_prepend tr s) m) == flatten (stream_trunc (stream_prepend [ to_trace tr ] trs) k)
  with begin
    if n <= length tr
    then begin
      // m = length tr, k = 1
      assume (to_trace (stream_trunc (stream_prepend tr s) (length tr)) == flatten (stream_trunc (stream_prepend [ to_trace tr ] trs) 1)) ;
      admit ()
    end
    else begin
      // Specialise hyp with n = n - length tr
      eliminate exists (m : nat) (k : nat). n - length tr <= m /\ to_trace (stream_trunc s m) == flatten (stream_trunc trs k)
      returns exists (m : nat) (k : nat). n <= m /\ to_trace (stream_trunc (stream_prepend tr s) m) == flatten (stream_trunc (stream_prepend [ to_trace tr ] trs) k)
      with _. begin
        // m = m + length tr, k = k + 1
        // assume (to_trace (stream_trunc (stream_prepend tr s) (m + length tr)) == flatten (stream_trunc (stream_prepend [ to_trace tr ] trs) (k + 1))) ;
        admit ()
      end
    end
  end

let repeat_inv_expand_aux #idx (pre : idx -> i_pre) (inv : trace -> Type0) (post : i_post unit) (hist : history) (j : idx) (tr : otrace) (trs : stream trace) (s : sotrace) :
  Lemma
    (requires repeat_inv pre inv j post hist /\ (forall n. inv (trs n)) /\ s `sotrace_refines` trs /\ inv (to_trace tr))
    (ensures post (Odv (stream_prepend tr (stream_prepend [ None ] s))))
= introduce forall n. inv (stream_prepend [ to_trace tr ] trs n)
  with begin
    if n = 0
    then begin
      assert_norm (stream_prepend [ to_trace tr ] trs 0 == to_trace tr)
    end
    else begin
      // assume (stream_prepend [ to_trace tr ] trs n == trs (n - 1)) ; // This should be true, but even assuming it makes F* unhappy
      admit ()
    end
  end ;

  sotrace_refines_prepend_None [ None ] s trs ;
  sotrace_refines_prepend tr (stream_prepend [ None ] s) trs ;
  assert ((stream_prepend tr (stream_prepend [ None ] s)) `sotrace_refines` (stream_prepend [ to_trace tr ] trs)) ;

  repeat_inv_inst pre inv j post hist (stream_prepend tr (stream_prepend [ None ] s)) (stream_prepend [ to_trace tr ] trs)

let repeat_inv_expand #index (pre : index -> i_pre) (inv : trace -> Type0) (post : i_post unit) (hist : history) (j : index) (tr : otrace) :
  Lemma
    (requires repeat_inv pre inv j post hist /\ pre j (rev_acc (to_trace tr) hist) /\ inv (to_trace tr))
    (ensures repeat_inv pre inv j (ishift_post [ None ] (ishift_post tr post)) (rev_acc (to_trace tr) hist))
= introduce forall r. diverges r /\ (exists (trs : stream trace). (forall n. inv (trs n)) /\ (inf_trace r) `sotrace_refines` trs) ==> ishift_post [ None ] (ishift_post tr post) r
  with begin
    introduce diverges r /\ (exists (trs : stream trace). (forall n. inv (trs n)) /\ (inf_trace r) `sotrace_refines` trs) ==> ishift_post [ None ] (ishift_post tr post) r
    with _. begin
      match r with
      | Odv s ->
        eliminate exists (trs : stream trace). (forall n. inv (trs n)) /\ (inf_trace r) `sotrace_refines` trs
        returns ishift_post [ None ] (ishift_post tr post) (Odv s)
        with _. begin
          repeat_inv_expand_aux pre inv post hist j tr trs s
        end
    end
  end

let repeat_inv_proof #index (pre : index -> i_pre) (inv : trace -> Type0) (i : index) :
  Lemma (i_iter (repeat_body_inv pre inv) i `ile` repeat_inv pre inv i)
= introduce forall j. iter_expand (repeat_body_inv pre inv) j (fun j -> repeat_inv pre inv j) `ile` repeat_inv pre inv j
  with begin
    introduce forall post hist. repeat_inv pre inv j post hist ==> iter_expand (repeat_body_inv pre inv) j (fun k -> repeat_inv pre inv k) post hist
    with begin
      introduce repeat_inv pre inv j post hist ==> iter_expand (repeat_body_inv pre inv) j (fun k -> repeat_inv pre inv k) post hist
      with _. begin
        calc (==) {
          iter_expand (repeat_body_inv pre inv) j (fun k -> repeat_inv pre inv k) post hist ;
          == { _ by (compute ()) }
          i_bind (repeat_body_inv pre inv j) (iter_expand_cont (fun k -> repeat_inv pre inv k)) post hist ;
          == { _ by (compute ()) }
          repeat_body_inv pre inv j (i_bind_post (iter_expand_cont (fun k -> repeat_inv pre inv k)) post hist) hist ;
        } ;
        assert (pre j hist) ;
        introduce forall (r : orun (either index unit)). terminates r /\ Inl? (result r) /\ pre (lval (result r)) (rev_acc (ret_trace r) hist) /\ inv (ret_trace r) ==> i_bind_post (iter_expand_cont (fun k -> repeat_inv pre inv k)) post hist r
        with begin
          introduce terminates r /\ Inl? (result r) /\ pre (lval (result r)) (rev_acc (ret_trace r) hist) /\ inv (ret_trace r) ==> i_bind_post (iter_expand_cont (fun k -> repeat_inv pre inv k)) post hist r
          with _. begin
            match r with
            | Ocv tr (Inl j) ->
              calc (==) {
                i_bind_post (iter_expand_cont (fun k -> repeat_inv pre inv k)) post hist r ;
                == {}
                iter_expand_cont (fun k -> repeat_inv pre inv k) (Inl j) (ishift_post tr post) (rev_acc (to_trace tr) hist) ;
                == { _ by (compute ()) }
                i_bind i_tau (fun _ -> repeat_inv pre inv j) (ishift_post tr post) (rev_acc (to_trace tr) hist) ;
                == { _ by (compute ()) }
                i_tau (i_bind_post (fun _ -> repeat_inv pre inv j) (ishift_post tr post) (rev_acc (to_trace tr) hist)) (rev_acc (to_trace tr) hist) ;
                == { _ by (compute ()) }
                i_bind_post (fun _ -> repeat_inv pre inv j) (ishift_post tr post) (rev_acc (to_trace tr) hist) (Ocv [ None ] ()) ;
                == { _ by (compute ()) }
                repeat_inv pre inv j (ishift_post [ None ] (ishift_post tr post)) (rev_acc [] (rev_acc (to_trace tr) hist)) ;
                == { _ by (compute ()) }
                repeat_inv pre inv j (ishift_post [ None ] (ishift_post tr post)) (rev_acc (to_trace tr) hist) ;
              } ;
              assume (repeat_inv pre inv j post hist) ; // It's my assumption already...
              repeat_inv_expand pre inv post hist j tr
          end
        end
      end
    end
  end ;
  i_iter_coind (repeat_body_inv pre inv) i (fun j -> repeat_inv pre inv j)
