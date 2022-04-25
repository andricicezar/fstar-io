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

let iiodiv_iter #index #a #w (f : (j : index) -> iiodiv_dm (either index a) (w j)) (i : index) : iiodiv_dm a (i_iter w i) =
  dm_iter f i

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

let iodiv_to_iiodiv #a #w (f : (eqtype_as_type unit -> IODIV a w)) : iiodiv_dm a w =
  admit () ; // Why not?
  reify (f ())

// Why does it fail?
// sub_effect IODIV ~> IIODIV = iodiv_to_iiodiv

(** Actions *)

// TODO Mostly lifted from IODIV?
