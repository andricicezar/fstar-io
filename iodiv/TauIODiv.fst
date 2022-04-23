(** IODiv effect definition on top of DivFree, using TauSpec *)

module TauIODiv

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

let iodiv_act : action_iwp io_sig =
  fun ac arg ->
    match ac with
    | OpenFile -> i_open arg
    | Read -> i_read arg
    | Close -> i_close arg

let iodiv_dm a w =
  dm io_sig iodiv_act a w

let iodiv_ret a (x : a) : iodiv_dm a (i_ret x) =
  dm_ret x

let iodiv_bind a b w wf (c : iodiv_dm a w) (f : (x : a) -> iodiv_dm b (wf x)) : iodiv_dm b (i_bind w wf) =
  dm_bind c f

let iodiv_subcomp a w w' (c : iodiv_dm a w) :
  Pure (iodiv_dm a w') (requires w `ile` w') (ensures fun _ -> True)
= dm_subcomp c

let iodiv_if_then_else (a : Type) (w1 w2 : iwp a) (f : iodiv_dm a w1) (g : iodiv_dm a w2) (b : bool) : Type =
  dm_if_then_else a w1 w2 f g b

[@@allow_informative_binders]
reflectable reifiable total layered_effect {
  IODIV : a:Type -> w:iwp a -> Effect
  with
    repr         = iodiv_dm ;
    return       = iodiv_ret ;
    bind         = iodiv_bind ;
    subcomp      = iodiv_subcomp ;
    if_then_else = iodiv_if_then_else
}

sub_effect PURE ~> IODIV = dm_lift_pure #(io_sig) #(iodiv_act)

// iprepost should be defined in DivFreeTauSpec
// invariants too

// effect IODiv (a : Type) (pre : history -> Type0) (post : (hist : history) -> branch a -> Pure Type0 (requires pre hist) (ensures fun _ -> True)) =
//   IODIV a (wprepost pre post)

// TODO Actions
