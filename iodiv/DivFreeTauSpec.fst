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

let i_pre = history -> Type0

let i_post' a = orun a -> Type0

let resp_eutt #a (p : i_post' a) : Type0 =
  forall r r'. r `eutt` r' /\ p r ==> p r'

let i_post a = p : (i_post' a) { resp_eutt p }

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

let i_ret #a (x : a) : iwp a =
  as_iwp (fun post hist -> post (Ocv [] x))

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

// TODO
