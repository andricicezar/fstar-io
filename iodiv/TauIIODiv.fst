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
