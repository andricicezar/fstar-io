module DivFreeTauDM.Test

open FStar.List.Tot
open FStar.Tactics

open DivFree
open DivFreeTauSpec
open DivFreeTauDM

open IIOSig
open IIOSigSpec

open DivFree.Test
open DivFreeTauSpec.Test

open TauIODiv

let lift_i (w:iwp 'a) (#index:Type0) : index -> iwp (either index unit) =
  (fun i -> i_bind_alt w (fun _ -> i_ret (Inl i)))

let iodiv_repeat #a #w (f :  iodiv_dm a w) : iodiv_dm unit (i_iter (lift_i w) ()) =
  let f' : i:unit -> iodiv_dm (either unit unit) (lift_i w i) =
    fun i -> iodiv_bind _ _ _ _ f (fun _ -> iodiv_ret _ (Inl i)) in
  iodiv_iter f' ()

let lem_spec_to_loop
  (a:Type)
  (pre0 : trace -> Type0)
  (inv0 : trace -> Type0)
  (pre0_inv0 : squash (forall h lt. pre0 h /\ inv0 lt ==> pre0 (rev_acc lt h))) :
  Lemma (
    let body0 : iwp a = iprepost pre0 (fun h r -> terminates r /\ inv0 (_trace r)) in
    let loop0 : iwp unit = iprepost pre0 (fun h r -> diverges r /\ repeat_inv_post inv0 r) in
    i_iter (lift_i body0) () `ile` loop0) =
  let body0 : iwp a = iprepost pre0 (fun h r -> terminates r /\ inv0 (_trace r)) in
  let loop0 = iprepost pre0 (fun h r -> diverges r /\ repeat_inv_post inv0 r) in
  let body' = lift_i body0 in
  let body_inv = repeat_body_inv #unit (fun _ -> pre0) inv0 in
  assert (body' () `ile` body_inv ());
  i_iter_mono #unit body' body_inv ();
  assert ((i_iter body' ()) `ile` (i_iter body_inv ()));
  repeat_inv_proof (fun _ -> pre0) inv0 () ;
  assert (i_iter body_inv () `ile` repeat_inv (fun _ -> pre0) inv0 ());
  assert (repeat_inv (fun _ -> pre0) inv0 () `ile` loop0);
  assert (i_iter body' () `ile` loop0)

let lem_body_to_loop
  (#a:Type)
  (#pre0 : trace -> Type0)
  (#inv0 : trace -> Type0)
  (#pre0_inv0 : squash (forall h lt. pre0 h /\ inv0 lt ==> pre0 (rev_acc lt h))) 
  (f : iodiv_dm a (iprepost pre0 (fun h r -> terminates r /\ inv0 (_trace r)))) :
  Lemma (
    let body0 : iwp a = iprepost pre0 (fun h r -> terminates r /\ inv0 (_trace r)) in
    let loop0 : iwp unit = iprepost pre0 (fun h r -> diverges r /\ repeat_inv_post inv0 r) in
    i_iter (lift_i body0) () `ile` loop0) =
  lem_spec_to_loop a pre0 inv0 pre0_inv0

let dm_body1 (fd:file_descr) : iodiv_dm string (ibody1 fd) = body1 fd

let dm_loop1 (fd:file_descr) : iodiv_dm unit (iloop1 fd) = 
  lem_body_to_loop (dm_body1 fd);
  iodiv_repeat (dm_body1 fd)

(** ** Test print 0 1 **)

(** What the actual **** **)
let dm_body2 : iodiv_dm unit (iprepost (fun _ -> True) (fun h r -> terminates r /\ _trace r == [EPrint "0";EPrint "1"] /\ False)) = 
  (m_bind (m_call Print "0") (fun () -> m_call Print "1"))

let iloop2 : iwp unit = iprepost (fun _ -> True) (fun h r -> diverges r /\ False) //repeat_inv_post (fun lt -> lt == [EPrint "0"; EPrint "3:"]) r)

let dm_loop2 () : iodiv_dm unit iloop2  =
  iodiv_repeat dm_body2
