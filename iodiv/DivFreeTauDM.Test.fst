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

let th #a = theta #a #io_sig iodiv_act


let test1 (fd:file_descr) : Lemma (th (body1 fd) `ile` ibody1 fd) = ()

#set-options "--split_queries always"
let test2 (fd:file_descr) =
  let body' = lift_body (ibody1 fd) in
//  pre1_inv1 fd;
//  let body_inv = repeat_body_inv #unit (fun _ -> pre1 fd) (inv1 fd) in

  test1 fd;

  assert (th (m_bind (body1 fd) (fun msg -> m_ret (Inl ()))) `ile` i_bind #_ #(either unit string) (ibody1 fd) (fun _ -> i_ret (Inl ())));
  assert (th (m_bind (body1 fd) (fun msg -> m_ret (Inl ()))) `ile` lift_body (ibody1 fd) ());
  //repeat_inv_proof #unit (fun _ -> (pre1 fd)) (inv1 fd) () ;
  //i_iter_mono (fun _ -> repeat_body_inv (fun _ -> (pre1 fd)) (inv1 fd) ()) (repeat_body_inv (fun _ -> (pre1 fd)) (inv1 fd)) () ;
  assume (th (m_iter (fun i -> m_bind (body1 fd) (fun msg -> m_ret (Inl i))) ()) `ile` i_iter (lift_body (ibody1 fd)) ());
  assert (th (m_iter (body1' fd) ()) `ile` i_iter body' ());
  assert (th (loop1 fd) `ile` i_iter body' ());
  itest1 fd;
  assert (th (loop1 fd) `ile` iloop1 fd)
