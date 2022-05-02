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

unfold
let iodiv_act : action_iwp io_sig =
  fun ac arg ->
    match ac with
    | OpenFile -> i_open arg
    | Read -> i_read arg
    | Close -> i_close arg

let iodiv_dm a w =
  dm io_sig iodiv_act a w

let iodiv_ret a (x : a) : iodiv_dm a (_i_ret x) =
  dm_ret x

let iodiv_bind a b w wf (c : iodiv_dm a w) (f : (x : a) -> iodiv_dm b (wf x)) : iodiv_dm b (_i_bind w wf) =
  dm_bind c f

let iodiv_subcomp a w w' (c : iodiv_dm a w) :
  Pure (iodiv_dm a w') (requires w `_ile` w') (ensures fun _ -> True)
= dm_subcomp c

unfold
let iodiv_if_then_else (a : Type) (w1 w2 : iwp a) (f : iodiv_dm a w1) (g : iodiv_dm a w2) (b : bool) : Type =
  dm_if_then_else a w1 w2 f g b

let iodiv_call (ac : io_sig.act) (x : io_sig.arg ac) : iodiv_dm (io_sig.res x) (iodiv_act ac x) =
  dm_call ac x

let iodiv_iter #index #a #w (f : (j : index) -> iodiv_dm (either index a) (w j)) (i : index) : iodiv_dm a (i_iter w i) =
  dm_iter f i

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

effect IODiv (a : Type) (pre : history -> Type0) (post : (hist : history) -> orun a -> Pure Type0 (requires pre hist) (ensures fun _ -> True)) =
  IODIV a (iprepost pre post)

(** Actions *)

let act_call (ac : io_sig.act) (x : io_sig.arg ac) : IODIV (io_sig.res x) (iodiv_act ac x) =
  IODIV?.reflect (iodiv_call ac x)

let open_file (s : string) : IODiv file_descr (requires fun hist -> True) (ensures fun hist r -> terminates r /\ ret_trace r == [ EOpenFile s (result r) ]) =
  act_call OpenFile s

let read (fd : file_descr) : IODiv string (requires fun hist -> is_open fd hist) (ensures fun hist r -> terminates r /\ ret_trace r == [ ERead fd (result r) ]) =
  act_call Read fd

let close (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun hist r -> terminates r /\ ret_trace r == [ EClose fd ]) =
  act_call Close fd

let iter #index #a #w (f : (j : index) -> IODIV (either index a) (w j)) (i : index) : IODIV a (i_iter w i) =
  IODIV?.reflect (dm_iter (fun j -> reify (f j)) i)

let repeat_with_inv #pre #inv (body : unit -> IODiv unit (requires fun hist -> pre hist) (ensures fun hist r -> terminates r /\ pre (rev_acc (ret_trace r) hist) /\ inv (ret_trace r))) :
  IODiv
    unit
    (requires fun hist -> pre hist)
    (ensures fun hist r ->
      diverges r /\
      (exists (trs : stream trace). (forall n. inv (trs n)) /\ (inf_trace r) `sotrace_refines` trs)
    )
= admit () ;
  repeat_inv_proof #unit (fun _ -> pre) inv () ;
  // It's odd that I have to give the spec by hand.
  iter #unit #unit #(fun _ -> _i_bind (iprepost #unit (fun hist -> pre hist) (fun hist r -> terminates r /\ pre (rev_acc (ret_trace r) hist) /\ inv (ret_trace r))) (fun _ -> _i_ret #(either unit unit) (Inl ()))) (fun _ -> body () ; Inl ()) ()
