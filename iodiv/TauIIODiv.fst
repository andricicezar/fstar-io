(** Instrumented IODiv effect definition on top of DivFree, using TauSpec *)

module TauIIODiv

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
open IIOSigSpec
open DivFree
open DivFreeTauSpec
open DivFreeTauDM
open TauIODiv

let iiodiv_dm a w =
  dm iio_sig iiodiv_act a w

let iiodiv_ret a (x : a) : iiodiv_dm a (_i_ret x) =
  dm_ret x

let iiodiv_bind a b w wf (c : iiodiv_dm a w) (f : (x : a) -> iiodiv_dm b (wf x)) : iiodiv_dm b (_i_bind w wf) =
  dm_bind c f

let iiodiv_subcomp a w w' (c : iiodiv_dm a w) :
  Pure (iiodiv_dm a w') (requires w `_ile` w') (ensures fun _ -> True)
= dm_subcomp c

unfold
let iiodiv_if_then_else (a : Type) (w1 w2 : iwp a) (f : iiodiv_dm a w1) (g : iiodiv_dm a w2) (b : bool) : Type =
  dm_if_then_else a w1 w2 f g b

let iiodiv_call (ac : iio_sig.act) (x : iio_sig.arg ac) : iiodiv_dm (iio_sig.res x) (iiodiv_act ac x) =
  dm_call ac x

[@@allow_informative_binders]
reflectable reifiable total layered_effect {
  IIODIV : a:Type -> w:iwp a -> Effect
  with
    repr         = iiodiv_dm ;
    return       = iiodiv_ret ;
    bind         = iiodiv_bind ;
    subcomp      = iiodiv_subcomp ;
    if_then_else = iiodiv_if_then_else
}

sub_effect PURE ~> IIODIV = dm_lift_pure #(iio_sig) #(iiodiv_act)

effect IIODiv (a : Type) (pre : history -> Type0) (post : (hist : history) -> orun a -> Pure Type0 (requires pre hist) (ensures fun _ -> True)) =
  IIODIV a (iprepost pre post)

(** Lift from IODIV *)

let rec m_io_to_iio #a (c : m io_sig a) : m iio_sig a =
  match c with
  | Ret x -> Ret x
  | Req pre k -> Req pre (fun h -> m_io_to_iio (k h))
  | Iter index d g i k -> Iter index d (fun j ->  m_io_to_iio (g j)) i (fun y -> m_io_to_iio (k y))
  | Call ac x k -> Call #iio_sig ac x (fun y -> m_io_to_iio (k y))

let rec theta_io_to_iio #a (c : m io_sig a) :
  Lemma (theta iodiv_act c `ieq` theta iiodiv_act (m_io_to_iio c))
= match c with
  | Ret x -> ()

  | Req pre k ->

    introduce forall x. theta iodiv_act (k x) `ieq` theta iiodiv_act (m_io_to_iio (k x))
    with begin
      theta_io_to_iio (k x)
    end

  | Iter index d g i k ->

    assert_norm (m_io_to_iio (Iter index d g i k) == Iter index d (fun j ->  m_io_to_iio (g j)) i (fun y -> m_io_to_iio (k y))) ;

    introduce forall x. theta iodiv_act (k x) `ieq` theta iiodiv_act (m_io_to_iio (k x))
    with begin
      theta_io_to_iio (k x)
    end ;

    introduce forall j. theta iodiv_act (g j) `ieq` theta iiodiv_act (m_io_to_iio (g j))
    with begin
      theta_io_to_iio (g j)
    end ;

    calc (ieq) {
      theta iodiv_act c ;
      == {}
      theta iodiv_act (Iter index d g i k) ;
      == { _ by (compute ()) }
      i_bind (i_iter_lift (fun j -> theta iodiv_act (g j)) i) (fun y -> theta iodiv_act (k y)) ;
      `ieq` { i_bind_cong (i_iter_lift (fun j -> theta iodiv_act (g j)) i) (fun y -> theta iodiv_act (k y)) (fun y -> theta iiodiv_act (m_io_to_iio (k y))) }
      i_bind (i_iter_lift (fun j -> theta iodiv_act (g j)) i) (fun y -> theta iiodiv_act (m_io_to_iio (k y))) ;
      `ieq` { i_iter_lift_cong (fun j -> theta iodiv_act (g j)) (fun j -> theta iiodiv_act (m_io_to_iio (g j))) i }
      i_bind (i_iter_lift (fun j -> theta iiodiv_act (m_io_to_iio (g j))) i) (fun y -> theta iiodiv_act (m_io_to_iio (k y))) ;
      `ieq` { _ by (compute ()) }
      theta iiodiv_act (Iter index d (fun j ->  m_io_to_iio (g j)) i (fun y -> m_io_to_iio (k y))) ;
      == {}
      theta iiodiv_act (m_io_to_iio c) ;
    }

  | Call ac x k ->

    assert_norm (m_io_to_iio (Call ac x k) == Call #iio_sig ac x (fun y -> m_io_to_iio (k y))) ;

    introduce forall x. theta iodiv_act (k x) `ieq` theta iiodiv_act (m_io_to_iio (k x))
    with begin
      theta_io_to_iio (k x)
    end ;

    calc (ieq) {
      theta iodiv_act c ;
      == {}
      theta iodiv_act (Call ac x k) ;
      == { _ by (compute ()) }
      i_bind (iodiv_act ac x) (fun y -> theta iodiv_act (k y)) ;
      `ieq` { i_bind_cong (iodiv_act ac x) (fun y -> theta iodiv_act (k y)) (fun y -> theta iiodiv_act (m_io_to_iio (k y))) }
      i_bind (iodiv_act ac x) (fun y -> theta iiodiv_act (m_io_to_iio (k y))) ;
      `ieq` {}
      i_bind (iiodiv_act ac x) (fun y -> theta iiodiv_act (m_io_to_iio (k y))) ;
      `ieq` {}
      theta iiodiv_act (Call #iio_sig ac x (fun y -> m_io_to_iio (k y))) ;
      == {}
      theta iiodiv_act (m_io_to_iio c) ;
    }

let iodiv_to_iiodiv a w (c : iodiv_dm a w) : iiodiv_dm a w =
  theta_io_to_iio c ;
  m_io_to_iio c

sub_effect IODIV ~> IIODIV = iodiv_to_iiodiv

(** Actions *)

let get_hist () : IIODiv history (requires fun hist -> True) (ensures fun hist r -> terminates r /\ ret_trace r == [] /\ result r == hist)
= IIODIV?.reflect (iiodiv_call GetTrace ())

let iter #index #a #w (f : (j : index) -> IIODIV (either index a) (w j)) (i : index) : IIODIV a (i_iter w i) =
  IIODIV?.reflect (dm_iter (fun j -> reify (f j)) i)
