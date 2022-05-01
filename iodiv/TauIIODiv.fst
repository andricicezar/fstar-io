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
open DivFree
open DivFreeTauSpec
open DivFreeTauDM
open TauIODiv

let iiodiv_act : action_iwp iio_sig =
  fun ac arg ->
    match ac with
    | OpenFile -> i_open arg
    | Read -> i_read arg
    | Close -> i_close arg
    | GetTrace -> i_get_trace

let iiodiv_dm a w =
  dm iio_sig iiodiv_act a w

let iiodiv_ret a (x : a) : iiodiv_dm a (i_ret x) =
  dm_ret x

let iiodiv_bind a b w wf (c : iiodiv_dm a w) (f : (x : a) -> iiodiv_dm b (wf x)) : iiodiv_dm b (i_bind w wf) =
  dm_bind c f

let iiodiv_subcomp a w w' (c : iiodiv_dm a w) :
  Pure (iiodiv_dm a w') (requires w `ile` w') (ensures fun _ -> True)
= dm_subcomp c

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

let theta_io_to_iio #a (c : m io_sig a) :
  Lemma (theta iodiv_act c `ieq` theta iiodiv_act (m_io_to_iio c))
= admit ()

let iodiv_to_iiodiv a w (c : iodiv_dm a w) : iiodiv_dm a w =
  theta_io_to_iio c ;
  m_io_to_iio c

sub_effect IODIV ~> IIODIV = iodiv_to_iiodiv

(** Actions *)

let get_hist () : IIODiv history (requires fun hist -> True) (ensures fun hist r -> terminates r /\ ret_trace r == [] /\ result r == hist)
= IIODIV?.reflect (iiodiv_call GetTrace ())
