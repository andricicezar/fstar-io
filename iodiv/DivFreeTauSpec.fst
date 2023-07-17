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

type fin_trace =
  list (option event)

type inf_trace =
  stream (option event)

let rec to_trace (t : fin_trace) : trace =
  match t with
  | [] -> []
  | Some e :: t -> e :: to_trace t
  | None :: t -> to_trace t

[@"opaque_to_smt"]
let embeds (p q : inf_trace) =
  forall (n : nat). exists (m : nat). to_trace (stream_trunc q n) == to_trace (stream_trunc p m)

let uptotau (p q : inf_trace) =
  p `embeds` q /\ q `embeds` p

let rec to_trace_append (t t' : fin_trace) :
  Lemma (to_trace (t @ t') == to_trace t @ to_trace t')
= match t with
  | [] -> ()
  | Some e :: t -> to_trace_append t t'
  | None :: t -> to_trace_append t t'

let embeds_inst (p q : inf_trace) (n : nat) :
  Lemma
    (requires p `embeds` q)
    (ensures exists (m : nat). to_trace (stream_trunc q n) == to_trace (stream_trunc p m))
= reveal_opaque (`%embeds) embeds

let embeds_refl (p : inf_trace) :
  Lemma (p `embeds` p)
= reveal_opaque (`%embeds) embeds

let uptotau_refl (p : inf_trace) :
  Lemma (p `uptotau` p)
= embeds_refl p

let rec to_trace_firstn (t : fin_trace) (n : nat) :
  Lemma (exists (m : nat). to_trace (firstn n t) == firstn m (to_trace t))
= match t with
  | [] -> ()
  | Some e :: t' ->
    if n = 0
    then ()
    else begin
      to_trace_firstn t' (n-1) ;
      eliminate exists (m : nat). to_trace (firstn (n-1) t') == firstn m (to_trace t')
      returns exists (m : nat). to_trace (firstn n t) == firstn m (to_trace t)
      with _. begin
        calc (==) {
          to_trace (firstn n t) ;
          == {}
          e :: to_trace (firstn (n-1) t') ;
          == {}
          e :: firstn m (to_trace t') ;
          == {}
          firstn (m+1) (to_trace t) ;
        }
      end
    end
  | None :: t' ->
    if n = 0
    then ()
    else begin
      to_trace_firstn t' (n-1) ;
      eliminate exists (m : nat). to_trace (firstn (n-1) t') == firstn m (to_trace t')
      returns exists (m : nat). to_trace (firstn n t) == firstn m (to_trace t)
      with _. begin
        calc (==) {
          to_trace (firstn n t) ;
          == {}
          to_trace (firstn (n-1) t') ;
          == {}
          firstn m (to_trace t') ;
          == {}
          firstn m (to_trace t) ;
        }
      end
    end

let rec firstn_to_trace (t : fin_trace) (n : nat) :
  Lemma (exists (m : nat). firstn n (to_trace t) == to_trace (firstn m t))
= match t with
  | [] -> ()
  | Some e :: t' ->
    if n = 0
    then ()
    else begin
      firstn_to_trace t' (n-1) ;
      eliminate exists (m : nat). firstn (n-1) (to_trace t') == to_trace (firstn m t')
      returns exists (m : nat). firstn n (to_trace t) == to_trace (firstn m t)
      with _. begin
        calc (==) {
          firstn n (to_trace t) ;
          == {}
          e :: firstn (n-1) (to_trace t') ;
          == {}
          e :: to_trace (firstn m t') ;
          == {}
          to_trace (firstn (m+1) t) ;
        }
      end
    end
  | None :: t' ->
    if n = 0
    then ()
    else begin
      firstn_to_trace t' n ;
      eliminate exists (m : nat). firstn n (to_trace t') == to_trace (firstn m t')
      returns exists (m : nat). firstn n (to_trace t) == to_trace (firstn m t)
      with _. begin
        calc (==) {
          firstn n (to_trace t) ;
          == {}
          firstn n (to_trace t') ;
          == {}
          to_trace (firstn m t') ;
          == {}
          to_trace (firstn (m+1) t) ;
        }
      end
    end

let embeds_prepend (t t' : fin_trace) (s s' : inf_trace) :
  Lemma
    (requires to_trace t == to_trace t' /\ s `embeds` s')
    (ensures stream_prepend t s `embeds` stream_prepend t' s')
= introduce forall (n : nat). exists (m : nat). to_trace (stream_trunc (stream_prepend t' s') n) == to_trace (stream_trunc (stream_prepend t s) m)
  with begin
    if n <= length t'
    then begin
      to_trace_firstn t' n ;
      eliminate exists (m : nat). to_trace (firstn n t') == firstn m (to_trace t')
      returns exists (m : nat). to_trace (stream_trunc (stream_prepend t' s') n) == to_trace (stream_trunc (stream_prepend t s) m)
      with _. begin
        firstn_to_trace t m ;
        eliminate exists (k : nat). firstn m (to_trace t) == to_trace (firstn k t)
        returns exists (m : nat). to_trace (stream_trunc (stream_prepend t' s') n) == to_trace (stream_trunc (stream_prepend t s) m)
        with _. begin
          calc (==) {
            to_trace (stream_trunc (stream_prepend t' s') n) ;
            == { stream_prepend_trunc_left t' s' n }
            to_trace (firstn n t') ;
            == {}
            firstn m (to_trace t') ;
            == {}
            firstn m (to_trace t) ;
            == {}
            to_trace (firstn k t) ;
            == { firstn_min_length k t }
            to_trace (firstn (min k (length t)) t) ;
            == { stream_prepend_trunc_left t s (min k (length t)) }
            to_trace (stream_trunc (stream_prepend t s) (min k (length t))) ;
          }
        end
      end
    end
    else begin
      embeds_inst s s' (n - length t') ;
      eliminate exists m. to_trace (stream_trunc s' (n - length t')) == to_trace (stream_trunc s m)
      returns (exists (m : nat). to_trace (stream_trunc (stream_prepend t' s') n) == to_trace (stream_trunc (stream_prepend t s) m))
      with _. begin
        calc (==) {
          to_trace (stream_trunc (stream_prepend t' s') n) ;
          == { stream_prepend_trunc_right t' s' n }
          to_trace (t' @ stream_trunc s' (n - length t')) ;
          == { to_trace_append t' (stream_trunc s' (n - length t')) }
          to_trace t' @ to_trace (stream_trunc s' (n - length t')) ;
          == {}
          to_trace t @ to_trace (stream_trunc s' (n - length t')) ;
          == {}
          to_trace t @ to_trace (stream_trunc s m) ;
          == { to_trace_append t (stream_trunc s m) }
          to_trace (t @ stream_trunc s m) ;
        } ;
        calc (==) {
          to_trace (stream_trunc (stream_prepend t s) (m + length t)) ;
          == { stream_prepend_trunc_right t s (m + length t) }
          to_trace (t @ stream_trunc s (m + length t - length t)) ;
          == {}
          to_trace (t @ stream_trunc s m) ;
        } ;
        assert (to_trace (stream_trunc (stream_prepend t' s') n) == to_trace (stream_trunc (stream_prepend t s) (m + length t)))
      end
    end
  end ;
  reveal_opaque (`%embeds) embeds

let uptotau_prepend (t t' : fin_trace) (s s' : inf_trace) :
  Lemma
    (requires to_trace t == to_trace t' /\ s `uptotau` s')
    (ensures stream_prepend t s `uptotau` stream_prepend t' s')
= embeds_prepend t t' s s' ;
  embeds_prepend t' t s' s

(** Converging or diverging run *)
noeq
type orun a =
| Cv : fin_trace -> a -> orun a
| Dv : inf_trace -> orun a

(** Equivalence up to tau *)

let eutt #a (r r' : orun a) : Type0 =
  match r, r' with
  | Cv t x, Cv t' x' -> to_trace t == to_trace t' /\ x == x'
  | Dv s, Dv s' -> s `uptotau` s'
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

let ile #a (w w' : iwp a) =
  forall p. w' p `i_pre_le` w p

let ieq #a (w w' : iwp a) =
  w `ile` w' /\ w' `ile` w

let ile_trans #a (w1 w2 w3 : iwp a) :
  Lemma
    (requires w1 `ile` w2 /\ w2 `ile` w3)
    (ensures w1 `ile` w3)
= ()

let as_iwp #a (w : iwp' a) : Pure (iwp a) (requires iwp_monotonic w) (ensures fun r -> r == w) =
  w

(** Basic predicates *)

unfold
let terminates #a : i_post a =
  as_i_post (fun r -> Cv? r)

unfold
let diverges #a : i_post a =
  as_i_post (fun r -> Dv? r)

let ret_fin_trace #a (r : orun a) : Pure fin_trace (requires terminates r) (ensures fun _ -> True) =
  match r with
  | Cv tr x -> tr

let ret_trace #a (r : orun a) : Pure trace (requires terminates r) (ensures fun _ -> True) =
  match r with
  | Cv tr x -> to_trace tr

let ret_itrace #a (r : orun a) : Pure inf_trace (requires diverges r) (ensures fun _ -> True) =
  match r with
  | Dv s -> s

let result #a (r : orun a) : Pure a (requires terminates r) (ensures fun _ -> True) =
  match r with
  | Cv tr x -> x

(** Specifications *)

let i_ret #a (x : a) : iwp a =
  as_iwp (fun post hist -> post (Cv [] x))

let ishift_post' #a (tr : fin_trace) (post : i_post a) : i_post' a =
  fun r ->
    (terminates r ==> post (Cv (tr @ ret_fin_trace r) (result r))) /\
    (diverges r ==> post (Dv (stream_prepend tr (ret_itrace r))))
    // match r with
    // | Cv tr' x -> post (Cv (tr @ tr') x)
    // | Dv st -> post (Dv (stream_prepend tr st))

let ishift_post #a (tr : fin_trace) (post : i_post a) : i_post a =
  introduce forall r r'. r `eutt` r' /\ ishift_post' tr post r ==> ishift_post' tr post r'
  with begin
    introduce r `eutt` r' /\ ishift_post' tr post r ==> ishift_post' tr post r'
    with _. begin
      match r, r' with
      | Cv t x, Cv t' x' ->
        to_trace_append tr t ;
        to_trace_append tr t' ;
        assert (Cv (tr @ t) x `eutt` Cv (tr @ t') x') ;
        i_post_resp_eutt post (Cv (tr @ t) x) (Cv (tr @ t') x')
      | Dv s, Dv s' ->
        uptotau_prepend tr tr s s' ;
        assert (Dv (stream_prepend tr s) `eutt #a` Dv (stream_prepend tr s')) ;
        i_post_resp_eutt post (Dv (stream_prepend tr s)) (Dv (stream_prepend tr s'))
    end
  end ;
  ishift_post' tr post

let ishift_post_nil #a (post : i_post a) :
  Lemma (ishift_post [] post `i_post_le` post)
= introduce forall r. ishift_post [] post r ==> post r
  with begin
    match r with
    | Cv tr x -> ()
    | Dv s -> stream_prepend_nil s ; stream_ext (stream_prepend [] s) s
  end

let ishift_post_mono a tr :
  Lemma (forall (p q : i_post a). p `i_post_le` q ==> ishift_post tr p `i_post_le` ishift_post tr q)
= ()

let ishift_post_app #a t t' (p : i_post a) :
  Lemma (ishift_post (t' @ t) p `i_post_le` ishift_post t (ishift_post t' p))
= introduce forall r. ishift_post (t' @ t) p r ==> ishift_post t (ishift_post t' p) r
  with begin
    match r with
    | Cv tr x -> append_assoc t' t tr
    | Dv st -> stream_prepend_app t' t st
  end

let i_bind_post' #a #b (wf : a -> iwp b) (post : i_post b) hist : i_post' a =
  fun r ->
    (terminates r ==> wf (result r) (ishift_post (ret_fin_trace r) post) (rev_acc (ret_trace r) hist)) /\
    (diverges r ==> post (Dv (ret_itrace r)))
//    match r with
//    | Cv tr x -> wf x (ishift_post tr post) (rev_acc (to_trace tr) hist)
//    | Dv st -> post (Dv st)

let i_bind_post #a #b (wf : a -> iwp b) (post : i_post b) hist : i_post a =
  introduce forall r r'. r `eutt` r' /\ i_bind_post' wf post hist r ==> i_bind_post' wf post hist r'
  with begin
    introduce r `eutt` r' /\ i_bind_post' wf post hist r ==> i_bind_post' wf post hist r'
    with _. begin
      match r, r' with
      | Cv t x, Cv t' x' ->
        introduce forall r. ishift_post t post r ==> ishift_post t' post r
        with begin
          introduce ishift_post t post r ==> ishift_post t' post r
          with _. begin
            match r with
            | Cv tr y ->
              to_trace_append t tr ;
              to_trace_append t' tr ;
              assert (Cv (t @ tr) y `eutt` Cv (t' @ tr) y) ;
              i_post_resp_eutt post (Cv (t @ tr) y) (Cv (t' @ tr) y)
            | Dv s ->
              uptotau_refl s ;
              uptotau_prepend t t' s s ;
              assert (Dv (stream_prepend t s) `eutt #a` Dv (stream_prepend t' s)) ;
              i_post_resp_eutt post (Dv (stream_prepend t s)) (Dv (stream_prepend t' s))
          end
        end ;
        iwp_monotonic_inst (wf x) (ishift_post t post) (ishift_post t' post) (rev_acc (to_trace t) hist)
      | Dv s, Dv s' ->
        i_post_resp_eutt post (Dv s) (Dv s')
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
    | Cv tr x ->
      ishift_post_mono b tr ;
      assert (ishift_post tr p `i_post_le` ishift_post tr q) ;
      assert (wf x (ishift_post tr p) (rev_acc (to_trace tr) hist) ==> wf x (ishift_post tr q) (rev_acc (to_trace tr) hist))
    | Dv s -> ()
  end

let i_bind (#a : Type u#a) (#b : Type u#b) (w : iwp a) (wf : a -> iwp b) : iwp b =
  introduce forall p q hist. p `i_post_le` q ==> i_bind_post wf p hist `i_post_le` i_bind_post wf q hist
  with begin
    move_requires (i_bind_post_mono wf p q) hist
  end ;
  as_iwp (fun post hist ->
    w (i_bind_post wf post hist) hist
  )

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
      | Cv tr x ->
        introduce forall r'. ishift_post tr (i_bind_post wg post hist) r' ==> i_bind_post wg (ishift_post tr post) (rev_acc (to_trace tr) hist) r'
        with begin
          match r' with
          | Cv tr' y ->
            to_trace_append tr tr' ;
            rev_acc_rev' (to_trace tr @ to_trace tr') hist ; // rev_acc (to_trace tr @ to_trace tr') hist == rev' (to_trace tr @ to_trace tr') @ hist
            rev'_append (to_trace tr) (to_trace tr') ; // == (rev' (to_trace tr') @ rev' (to_trace tr)) @ hist
            append_assoc (rev' (to_trace tr')) (rev' (to_trace tr)) hist ; // == rev' (to_trace tr') @ rev' (to_trace tr) @ hist
            rev_acc_rev' (to_trace tr) hist ; // == rev' (to_trace tr') @ rev_acc (to_trace tr) hist
            rev_acc_rev' (to_trace tr') (rev_acc (to_trace tr) hist) ; // == rev_acc (to_trace tr') (rev_acc (to_trace tr) hist)
            ishift_post_app tr' tr post
          | Dv st -> ()
        end ;
        assert (ishift_post tr (i_bind_post wg post hist) `i_post_le` i_bind_post wg (ishift_post tr post) (rev_acc (to_trace tr) hist))
      | Dv st -> ()
    end ;
    assert (i_bind_post wf (i_bind_post wg post hist) hist `i_post_le` i_bind_post (fun x -> i_bind (wf x) wg) post hist)
  end

let i_bind_post_ret #a (post : i_post a) hist :
  Lemma (i_bind_post i_ret post hist `i_post_eq` post)
= introduce forall r. i_bind_post i_ret post hist r <==> post r
  with begin
    match r with
    | Cv tr x -> ()
    | Dv st -> ()
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
  as_iwp (fun post hist -> pre /\ post (Cv [] (Squash.get_proof pre)))

unfold
let iwite #a (w1 w2 : iwp a) (b : bool) : iwp a =
  fun post hist -> (b ==> w1 post hist) /\ (~ b ==> w2 post hist)

let i_tau : iwp unit =
  as_iwp (fun post hist -> post (Cv [ None ] ()))

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
= ()

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

let i_iter_def (#index : Type0) (#a : Type0) (w : index -> iwp (either index a)) (i : index) : iwp a =
  fun post hist ->
    exists (it : index -> iwp a).
      (forall j. iter_expand w j it `ile` it j) /\
      it i post hist

[@"opaque_to_smt"]
let i_iter = i_iter_def

let reveal_i_iter (index a : Type0) :
  Lemma (i_iter #index #a == i_iter_def)
= reveal_opaque (`%i_iter) (i_iter #index #a)

let i_iter_def_unfold (#index : Type0) (#a : Type0) (w : index -> iwp (either index a)) (i : index) :
  Lemma (iter_expand w i (i_iter_def w) `ile` i_iter_def w i)
= introduce forall post hist. i_iter_def w i post hist ==> iter_expand w i (i_iter_def w) post hist
  with begin
    introduce i_iter_def w i post hist ==> iter_expand w i (i_iter_def w) post hist
    with _. begin
      eliminate exists (it : index -> iwp a). (forall j. iter_expand w j it `ile` it j) /\ it i post hist
      returns iter_expand w i (i_iter_def w) post hist
      with _. begin
        assert (iter_expand w i it post hist) ;
        iter_expand_mono_k w i (i_iter_def w) it
      end
    end
  end

let i_iter_unfold (#index : Type0) (#a : Type0) (w : index -> iwp (either index a)) (i : index) :
  Lemma (iter_expand w i (i_iter w) `ile` i_iter w i)
= reveal_i_iter index a ;
  i_iter_def_unfold w i

let i_iter_coind (#index : Type0) (#a : Type0) (w : index -> iwp (either index a)) (i : index) w' :
  Lemma
    (requires forall j. iter_expand w j w' `ile` w' j)
    (ensures i_iter w i `ile` w' i)
= reveal_i_iter index a

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
= reveal_i_iter index a

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

(** Loop invariants *)

// TODO MOVE
let lval #a #b (x : either a b) : Pure a (requires Inl? x) (ensures fun _ -> True) =
  match x with
  | Inl v -> v

(* Specification of the body that always continues *)
let repeat_body_inv #index (pre : index -> i_pre) (inv : trace -> Type0) (i : index) : iwp (either index unit) =
  iprepost (pre i) (fun hist r -> terminates r /\ Inl? (result r) /\ pre (lval (result r)) (rev_acc (ret_trace r) hist) /\ inv (ret_trace r))

[@"opaque_to_smt"]
let inf_trace_refines (s : inf_trace) (trs : stream trace) =
  forall (n : nat). exists (m : nat) (k : nat). n <= m /\ to_trace (stream_trunc s m) == flatten (stream_trunc trs k)

let inf_trace_refine_inst (s : inf_trace) (trs : stream trace) (n : nat) :
  Lemma
    (requires s `inf_trace_refines` trs)
    (ensures exists (m : nat) (k : nat). n <= m /\ to_trace (stream_trunc s m) == flatten (stream_trunc trs k))
= reveal_opaque (`%inf_trace_refines) inf_trace_refines

[@"opaque_to_smt"]
let repeat_inv_post (inv : trace -> Type0) (r : orun unit { diverges r }) =
  exists (trs : stream trace). (forall n. inv (trs n)) /\ (ret_itrace r) `inf_trace_refines` trs

let repeat_inv #index (pre : index -> i_pre) (inv : trace -> Type0) (i : index) : iwp unit =
  iprepost (pre i) (fun hist r -> diverges r /\ repeat_inv_post inv r)

let repeat_inv_inst #index (pre : index -> i_pre) (inv : trace -> Type0) (i : index) (post : i_post unit) hist (s : inf_trace) (trs : stream trace) :
  Lemma (requires repeat_inv pre inv i post hist /\ (forall n. inv (trs n)) /\ s `inf_trace_refines` trs) (ensures post (Dv s))
= reveal_opaque (`%repeat_inv_post) repeat_inv_post

let inf_trace_refines_prepend_None (tr : fin_trace) (s : inf_trace) (trs : stream trace) :
  Lemma
    (requires to_trace tr == [] /\ s `inf_trace_refines` trs)
    (ensures stream_prepend tr s `inf_trace_refines` trs)
= introduce forall (n : nat). exists (m : nat) (k : nat). n <= m /\ to_trace (stream_trunc (stream_prepend tr s) m) == flatten (stream_trunc trs k)
  with begin
    inf_trace_refine_inst s trs n ;
    eliminate exists (m : nat) (k : nat). n <= m /\ to_trace (stream_trunc s m) == flatten (stream_trunc trs k)
    returns (exists (m : nat) (k : nat). n <= m /\ to_trace (stream_trunc (stream_prepend tr s) m) == flatten (stream_trunc trs k))
    with _. begin
      calc (==) {
        to_trace (stream_trunc (stream_prepend tr s) (m + length tr)) ;
        == { stream_prepend_trunc_right tr s (m + length tr) }
        to_trace (tr @ stream_trunc s (m + length tr - length tr)) ;
        == {}
        to_trace (tr @ stream_trunc s m) ;
        == { to_trace_append tr (stream_trunc s m) }
        to_trace tr @ to_trace (stream_trunc s m) ;
        == {}
        [] @ to_trace (stream_trunc s m) ;
        == {}
        to_trace (stream_trunc s m) ;
        == {}
        flatten (stream_trunc trs k) ;
      }
    end
  end ;
  reveal_opaque (`%inf_trace_refines) inf_trace_refines

#push-options "--split_queries always"
let inf_trace_refines_prepend (tr : fin_trace) (s : inf_trace) (trs : stream trace) :
  Lemma
    (requires s `inf_trace_refines` trs)
    (ensures stream_prepend tr s `inf_trace_refines` stream_prepend [ to_trace tr ] trs)
= introduce forall (n : nat). exists (m : nat) (k : nat). n <= m /\ to_trace (stream_trunc (stream_prepend tr s) m) == flatten (stream_trunc (stream_prepend [ to_trace tr ] trs) k)
  with begin
    if n <= length tr
    then begin
      introduce exists (m : nat) (k : nat). n <= m /\ to_trace (stream_trunc (stream_prepend tr s) m) == flatten (stream_trunc (stream_prepend [ to_trace tr ] trs) k)
      with (length tr) 1
      and begin
        assert (n <= length tr) ;
        calc (==) {
          to_trace (stream_trunc (stream_prepend tr s) (length tr)) ;
          == { stream_prepend_trunc_left tr s (length tr) }
          to_trace (firstn (length tr) tr) ;
          == { firstn_all (length tr) tr }
          to_trace tr ;
          == { flatten_one (to_trace tr) }
          flatten [ to_trace tr ] ;
          == {}
          flatten (firstn 1 [ to_trace tr ]) ;
          == { stream_prepend_trunc_left [ to_trace tr ] trs 1 }
          flatten (stream_trunc (stream_prepend [ to_trace tr ] trs) 1) ;
        }
      end
    end
    else begin
      // Specialise hyp with n = n - length tr
      inf_trace_refine_inst s trs (n - length tr) ;
      eliminate exists (m : nat) (k : nat). n - length tr <= m /\ to_trace (stream_trunc s m) == flatten (stream_trunc trs k)
      returns exists (m : nat) (k : nat). n <= m /\ to_trace (stream_trunc (stream_prepend tr s) m) == flatten (stream_trunc (stream_prepend [ to_trace tr ] trs) k)
      with _. begin
        // m = m + length tr, k = k + 1
        calc (==) {
          to_trace (stream_trunc (stream_prepend tr s) (m + length tr)) ;
          == { stream_prepend_trunc_right tr s (m + length tr) }
          to_trace (tr @ stream_trunc s (m + length tr - length tr)) ;
          == {}
          to_trace (tr @ stream_trunc s m) ;
          == { to_trace_append tr (stream_trunc s m) }
          to_trace tr @ to_trace (stream_trunc s m) ;
          == {}
          to_trace tr @ flatten (stream_trunc trs k) ;
          == { flatten_one (to_trace tr) }
          flatten [ to_trace tr ] @ flatten (stream_trunc trs k) ;
          == { flatten_append [ to_trace tr ] (stream_trunc trs k) }
          flatten ([ to_trace tr ] @ stream_trunc trs k) ;
          == {}
          flatten ([ to_trace tr ] @ stream_trunc trs (k + 1 - length [ to_trace tr ])) ;
          == { stream_prepend_trunc_right [ to_trace tr ] trs (k+1) }
          flatten (stream_trunc (stream_prepend [ to_trace tr ] trs) (k + 1)) ;
        }
      end
    end
  end ;
  reveal_opaque (`%inf_trace_refines) inf_trace_refines
#pop-options

let repeat_inv_expand_aux #idx (pre : idx -> i_pre) (inv : trace -> Type0) (post : i_post unit) (hist : history) (j : idx) (tr : fin_trace) (trs : stream trace) (s : inf_trace) :
  Lemma
    (requires repeat_inv pre inv j post hist /\ (forall n. inv (trs n)) /\ s `inf_trace_refines` trs /\ inv (to_trace tr))
    (ensures post (Dv (stream_prepend tr (stream_prepend [ None ] s))))
= introduce forall n. inv (stream_prepend [ to_trace tr ] trs n)
  with begin
    if n = 0
    then begin
      assert_norm (stream_prepend [ to_trace tr ] trs 0 == to_trace tr)
    end
    else begin
      assert (stream_prepend [ to_trace tr ] trs n == trs (n - 1))
    end
  end ;

  inf_trace_refines_prepend_None [ None ] s trs ;
  inf_trace_refines_prepend tr (stream_prepend [ None ] s) trs ;
  assert ((stream_prepend tr (stream_prepend [ None ] s)) `inf_trace_refines` (stream_prepend [ to_trace tr ] trs)) ;

  repeat_inv_inst pre inv j post hist (stream_prepend tr (stream_prepend [ None ] s)) (stream_prepend [ to_trace tr ] trs)

let repeat_inv_expand #index (pre : index -> i_pre) (inv : trace -> Type0) (post : i_post unit) (hist : history) (j jj : index) (tr : fin_trace) :
  Lemma
    (requires repeat_inv pre inv j post hist /\ pre jj (rev_acc (to_trace tr) hist) /\ inv (to_trace tr))
    (ensures repeat_inv pre inv jj (ishift_post [ None ] (ishift_post tr post)) (rev_acc (to_trace tr) hist))
= introduce forall r. diverges r /\ (exists (trs : stream trace). (forall n. inv (trs n)) /\ (ret_itrace r) `inf_trace_refines` trs) ==> ishift_post [ None ] (ishift_post tr post) r
  with begin
    introduce diverges r /\ (exists (trs : stream trace). (forall n. inv (trs n)) /\ (ret_itrace r) `inf_trace_refines` trs) ==> ishift_post [ None ] (ishift_post tr post) r
    with _. begin
      match r with
      | Dv s ->
        eliminate exists (trs : stream trace). (forall n. inv (trs n)) /\ (ret_itrace r) `inf_trace_refines` trs
        returns ishift_post [ None ] (ishift_post tr post) (Dv s)
        with _. begin
          repeat_inv_expand_aux pre inv post hist j tr trs s
        end
    end
  end ;
  reveal_opaque (`%repeat_inv_post) repeat_inv_post

#push-options "--split_queries always"
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
        introduce
          forall (r : orun (either index unit)).
            terminates r /\ Inl? (result r) /\ pre (lval (result r)) (rev_acc (ret_trace r) hist) /\ inv (ret_trace r) ==>
            i_bind_post (iter_expand_cont (fun k -> repeat_inv pre inv k)) post hist r
        with begin
          introduce
            terminates r /\ Inl? (result r) /\ pre (lval (result r)) (rev_acc (ret_trace r) hist) /\ inv (ret_trace r) ==>
            i_bind_post (iter_expand_cont (fun k -> repeat_inv pre inv k)) post hist r
          with _. begin
            match r with
            | Cv tr (Inl jj) -> ();
            (**
              calc (==) {
                i_bind_post (iter_expand_cont (fun k -> repeat_inv pre inv k)) post hist r ;
                == {}
                iter_expand_cont (fun k -> repeat_inv pre inv k) (Inl jj) (ishift_post tr post) (rev_acc (to_trace tr) hist) ;
                == { _ by (compute ()) }
                i_bind i_tau (fun _ -> repeat_inv pre inv jj) (ishift_post tr post) (rev_acc (to_trace tr) hist) ;
                == { _ by (compute ()) }
                i_tau (i_bind_post (fun _ -> repeat_inv pre inv jj) (ishift_post tr post) (rev_acc (to_trace tr) hist)) (rev_acc (to_trace tr) hist) ;
                == { _ by (compute ()) }
                i_bind_post (fun _ -> repeat_inv pre inv jj) (ishift_post tr post) (rev_acc (to_trace tr) hist) (Cv [ None ] ()) ;
                == { _ by (compute ()) }
                repeat_inv pre inv jj (ishift_post [ None ] (ishift_post tr post)) (rev_acc [] (rev_acc (to_trace tr) hist)) ;
                == { _ by (compute ()) }
                repeat_inv pre inv jj (ishift_post [ None ] (ishift_post tr post)) (rev_acc (to_trace tr) hist) ;
              } ;**)
              repeat_inv_expand pre inv post hist j jj tr
          end
        end
      end
    end
  end ;
  i_iter_coind (repeat_body_inv pre inv) i (fun j -> repeat_inv pre inv j)
#pop-options

(** Using implications rather than match *)

let i_bind_post_alt' #a #b (wf : a -> iwp b) (post : i_post b) hist : i_post' a =
  fun r ->
    (terminates r ==> wf (result r) (ishift_post (ret_fin_trace r) post) (rev_acc (ret_trace r) hist)) /\
    (diverges r ==> post (Dv (ret_itrace r)))

let i_bind_post_alt #a #b (wf : a -> iwp b) (post : i_post b) hist : i_post a =
  introduce forall r r'. r `eutt` r' /\ i_bind_post' wf post hist r ==> i_bind_post' wf post hist r'
  with begin
    introduce r `eutt` r' /\ i_bind_post' wf post hist r ==> i_bind_post' wf post hist r'
    with _. begin
      match r, r' with
      | Cv t x, Cv t' x' ->
        introduce forall r. ishift_post t post r ==> ishift_post t' post r
        with begin
          introduce ishift_post t post r ==> ishift_post t' post r
          with _. begin
            match r with
            | Cv tr y ->
              to_trace_append t tr ;
              to_trace_append t' tr ;
              assert (Cv (t @ tr) y `eutt` Cv (t' @ tr) y) ;
              i_post_resp_eutt post (Cv (t @ tr) y) (Cv (t' @ tr) y)
            | Dv s ->
              uptotau_refl s ;
              uptotau_prepend t t' s s ;
              assert (Dv (stream_prepend t s) `eutt #a` Dv (stream_prepend t' s)) ;
              i_post_resp_eutt post (Dv (stream_prepend t s)) (Dv (stream_prepend t' s))
          end
        end ;
        iwp_monotonic_inst (wf x) (ishift_post t post) (ishift_post t' post) (rev_acc (to_trace t) hist)
      | Dv s, Dv s' ->
        i_post_resp_eutt post (Dv s) (Dv s')
    end
  end ;
  i_bind_post_alt' wf post hist

let i_bind_post_alt_mono #a #b (wf : a -> iwp b) p q hist :
  Lemma
    (requires p `i_post_le` q)
    (ensures i_bind_post_alt wf p hist `i_post_le` i_bind_post_alt wf q hist)
= introduce forall r. i_bind_post wf p hist r ==> i_bind_post wf q hist r
  with begin
    match r with
    | Cv tr x ->
      ishift_post_mono b tr ;
      assert (ishift_post tr p `i_post_le` ishift_post tr q) ;
      assert (wf x (ishift_post tr p) (rev_acc (to_trace tr) hist) ==> wf x (ishift_post tr q) (rev_acc (to_trace tr) hist))
    | Dv s -> ()
  end

let i_bind_alt (#a : Type u#a) (#b : Type u#b) (w : iwp a) (wf : a -> iwp b) : iwp b =
  introduce forall p q hist. p `i_post_le` q ==> i_bind_post_alt wf p hist `i_post_le` i_bind_post_alt wf q hist
  with begin
    move_requires (i_bind_post_alt_mono wf p q) hist
  end ;
  as_iwp (fun post hist ->
    forall (k : i_post b).
      (forall (rb : orun b). {:pattern (guard_free (k rb))} post rb ==> k rb) ==>
      w (i_bind_post_alt wf k hist) hist
  )

let i_bind_post_alt_eq #a #b (wf : a -> iwp b) (post : i_post b) hist :
  Lemma (i_bind_post_alt wf post hist `i_post_eq` i_bind_post wf post hist)
= ()

let i_bind_alt_eq #a #b (w : iwp a) (wf : a -> iwp b) :
  Lemma (i_bind_alt w wf `ieq` i_bind w wf)
= introduce forall post hist. i_bind_post_alt wf post hist `i_post_eq` i_bind_post wf post hist
  with begin
    i_bind_post_alt_eq wf post hist
  end ;
  // i_bind_alt w wf `ile` i_bind w wf
  introduce forall p hist. i_bind w wf p hist ==> i_bind_alt w wf p hist
  with begin
    introduce i_bind w wf p hist ==> i_bind_alt w wf p hist
    with _. begin
      introduce forall (k : i_post b).
        (forall (rb : orun b). {:pattern (guard_free (k rb))} p rb ==> k rb) ==>
        w (i_bind_post_alt wf k hist) hist
      with begin
        introduce
          (forall (rb : orun b). {:pattern (guard_free (k rb))} p rb ==> k rb) ==>
          w (i_bind_post_alt wf k hist) hist
        with _. begin
          i_bind_post_mono wf p k hist
        end
      end
    end
  end

(** Other alternative to i_bind that uses the generalisation but still uses a match *)

let i_bind_alt2 (#a : Type u#a) (#b : Type u#b) (w : iwp a) (wf : a -> iwp b) : iwp b =
  introduce forall p q hist. p `i_post_le` q ==> i_bind_post wf p hist `i_post_le` i_bind_post wf q hist
  with begin
    move_requires (i_bind_post_mono wf p q) hist
  end ;
  as_iwp (fun post hist ->
    forall (k : i_post b).
      (forall (rb : orun b). {:pattern (guard_free (k rb))} post rb ==> k rb) ==>
      w (i_bind_post wf k hist) hist
  )

let i_bind_alt2_eq #a #b (w : iwp a) (wf : a -> iwp b) :
  Lemma (i_bind_alt2 w wf `ieq` i_bind w wf)
= // i_bind_alt2 w wf `ile` i_bind w wf
  introduce forall p hist. i_bind w wf p hist ==> i_bind_alt2 w wf p hist
  with begin
    introduce i_bind w wf p hist ==> i_bind_alt2 w wf p hist
    with _. begin
      introduce forall (k : i_post b).
        (forall (rb : orun b). {:pattern (guard_free (k rb))} p rb ==> k rb) ==>
        w (i_bind_post wf k hist) hist
      with begin
        introduce
          (forall (rb : orun b). {:pattern (guard_free (k rb))} p rb ==> k rb) ==>
          w (i_bind_post wf k hist) hist
        with _. begin
          i_bind_post_mono wf p k hist
        end
      end
    end
  end

(** Unfolding things so that they compute better now that the proofs are done. *)

let pp_unfold l () : Tac unit =
  norm [delta_only l ; iota] ; trefl ()

[@@ (postprocess_with (pp_unfold [ `%ile ; `%i_post_le ]))]
unfold let _ile = ile

[@@ (postprocess_with (pp_unfold [ `%i_ret ; `%as_iwp ]))]
unfold let _i_ret = i_ret

// [@@ (postprocess_with (pp_unfold [ `%i_bind ; `%i_bind_post ; `%i_bind_post' ; `%ishift_post ; `%ishift_post' ; `%as_iwp ]))]
// unfold let _i_bind = i_bind

[@@ (postprocess_with (pp_unfold [ `%i_bind_alt ; `%i_bind_post_alt ; `%i_bind_post_alt' ; `%ishift_post ; `%ishift_post' ; `%as_iwp ]))]
unfold let _i_bind = i_bind_alt

// [@@ (postprocess_with (pp_unfold [ `%i_bind_alt2 ; `%i_bind_post ; `%i_bind_post' ; `%ishift_post ; `%ishift_post' ; `%as_iwp ]))]
// unfold let _i_bind = i_bind_alt2
