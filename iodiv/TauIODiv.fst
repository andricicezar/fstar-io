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
open IIOSigSpec

let iodiv_dm a w =
  dm io_sig i_act a w

let iodiv_ret a (x : a) : iodiv_dm a (_i_ret x) =
  dm_ret x

let iodiv_bind a b w wf (c : iodiv_dm a w) (f : (x : a) -> iodiv_dm b (wf x)) : iodiv_dm b (_i_bind w wf) =
  dm_bind c f

[@@ (postprocess_with (pp_unfold [ `%_ile ]))]
let iodiv_subcomp a w w' (c : iodiv_dm a w) :
  Pure (iodiv_dm a w') (requires w `_ile` w') (ensures fun _ -> True)
= dm_subcomp c

unfold
let iodiv_if_then_else (a : Type) (w1 w2 : iwp a) (f : iodiv_dm a w1) (g : iodiv_dm a w2) (b : bool) : Type =
  dm_if_then_else a w1 w2 f g b

let iodiv_call (ac : io_sig.act) (x : io_sig.arg ac) : iodiv_dm (io_sig.res x) (i_act ac x) =
  dm_call ac x

let iodiv_iter #index #a #w (f : (j : index) -> iodiv_dm (either index a) (w j)) (i : index) : iodiv_dm a (i_iter w i) =
  dm_iter f i

reflectable reifiable total layered_effect {
  IODIV : a:Type -> w:iwp a -> Effect
  with
    repr         = iodiv_dm ;
    return       = iodiv_ret ;
    bind         = iodiv_bind ;
    subcomp      = iodiv_subcomp ;
    if_then_else = iodiv_if_then_else
}

sub_effect PURE ~> IODIV = dm_lift_pure #(io_sig) #(i_act)

effect IODiv (a : Type) (pre : history -> Type0) (post : (hist : history) -> orun a -> Pure Type0 (requires pre hist) (ensures fun _ -> True)) =
  IODIV a (iprepost pre post)

(** Helping the SMT with the goals we generate *)

let to_trace_append_pat t t' :
  Lemma (to_trace (t @ t') == to_trace t @ to_trace t') [SMTPat (to_trace (t @ t'))]
= to_trace_append t t'

(** Actions *)

let act_call (ac : io_sig.act) (x : io_sig.arg ac) : IODIV (io_sig.res x) (i_act ac x) =
  IODIV?.reflect (iodiv_call ac x)

let open_file (s : string) : IODiv file_descr (requires fun hist -> True) (ensures fun hist r -> terminates r /\ ret_trace r == [ EOpenfile s (result r) ]) =
  act_call Openfile s

let read (fd : file_descr) : IODiv string (requires fun hist -> is_open fd hist) (ensures fun hist r -> terminates r /\ ret_trace r == [ ERead fd (result r) ]) =
  act_call Read fd

let close (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun hist r -> terminates r /\ ret_trace r == [ EClose fd ]) =
  act_call Close fd

let print (s:string) : IODiv unit (requires fun hist -> True) (ensures fun hist r -> terminates r /\ ret_trace r == [ EPrint s ]) =
  act_call Print s

let iter #index #a #w ($f : (j : index) -> IODIV (either index a) (w j)) (i : index) : IODIV a (i_iter w i) =
  IODIV?.reflect (dm_iter (fun j -> reify (f j)) i)

let _repeat_with_inv_aux pre inv (body : iodiv_dm (either unit unit) (repeat_body_inv (fun _ -> pre) inv ())) :
  iodiv_dm unit (repeat_inv (fun _ -> pre) inv ())
= repeat_inv_proof #unit (fun _ -> pre) inv () ;
  i_iter_mono (fun _ -> repeat_body_inv (fun _ -> pre) inv ()) (repeat_body_inv (fun _ -> pre) inv) () ;
  dm_subcomp (dm_iter (fun _ -> body) ())

let _repeat_with_inv 
  pre
  inv 
  (#c1: squash (forall h lt. pre h /\ inv lt ==> pre (rev_acc lt h)))
  (body : iodiv_dm unit (iprepost (fun hist -> pre hist) (fun hist r -> terminates r /\ inv (ret_trace r)))) :
  iodiv_dm
    unit
    (iprepost
      (fun hist -> pre hist)
      (fun hist r -> diverges r /\ repeat_inv_post inv r)
    )
= _repeat_with_inv_aux pre inv (dm_bind body (fun _ -> dm_ret (Inl ())))

[@"opaque_to_smt"]
let repeat_with_inv #pre #inv 
  (#c1:squash (forall h lt. pre h /\ inv lt ==> pre (rev_acc lt h)))
  ($body : unit -> IODiv unit (requires fun hist -> pre hist) (ensures fun hist r -> terminates r /\ inv (ret_trace r))) :
  // ^ The dollar sign here tells F* to check for type equality in this argument,
  // instead of just subtyping, so a call `repeat_with_inv body` can actually
  // help the unifier find pre/inv/c1.
  IODiv
    unit
    (requires fun hist -> pre hist)
    (ensures fun hist r -> diverges r /\ repeat_inv_post inv r)
= IODIV?.reflect (_repeat_with_inv pre inv (reify (body ())))

let _repeat_aux #a (pre : a -> i_pre) inv (body : (x:a) -> iodiv_dm (either a unit) (repeat_body_inv pre inv x)) (x : a) :
  iodiv_dm unit (repeat_inv pre inv x)
= repeat_inv_proof pre inv x ;
  i_iter_mono (fun y -> repeat_body_inv pre inv y) (repeat_body_inv pre inv) x ;
  dm_subcomp (dm_iter body x)

let _repeat #a (pre : a -> i_pre) inv (body : (x:a) -> iodiv_dm a (iprepost (fun hist -> pre x hist) (fun hist r -> terminates r /\ pre (result r) (rev_acc (ret_trace r) hist) /\ inv (ret_trace r)))) (x : a) :
  iodiv_dm
    unit
    (iprepost
      (fun hist -> pre x hist)
      (fun hist r -> diverges r /\ repeat_inv_post inv r)
    )
= _repeat_aux pre inv (fun y -> iodiv_subcomp _ _ _ (dm_bind (body y) (fun z -> dm_ret (Inl z)))) x

[@"opaque_to_smt"]
let repeat #a 
  pre 
  inv
  ($body : (x:a) -> IODiv a (requires fun hist -> pre x hist) (ensures fun hist r -> terminates r /\ pre (result r) (rev_acc (ret_trace r) hist) /\ inv (ret_trace r))) (x : a) :
  // ^ The dollar sign here tells F* to check for type equality in this argument,
  // instead of just subtyping, so a call `repeat_with_inv body` can actually
  // help the unifier find pre/inv/c1.
  IODiv
    unit
    (requires fun hist -> pre x hist)
    (ensures fun hist r -> diverges r /\ repeat_inv_post inv r)
= IODIV?.reflect (_repeat pre inv (fun y -> reify (body y)) x)
