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


let test2 (fd:file_descr) =
//  pre1_inv1 fd;
  let body' = lift_body #file_descr (ibody1 fd) #unit in
//  let body_inv = repeat_body_inv #unit (fun _ -> pre1 fd) (inv1 fd) in
//  repeat_inv_proof #unit (fun _ -> (pre1 fd)) (inv1 fd) () ;
//  i_iter_mono (fun _ -> repeat_body_inv (fun _ -> (pre1 fd)) (inv1 fd) ()) (repeat_body_inv (fun _ -> (pre1 fd)) (inv1 fd)) () ;

  test1 fd;
  assume (th (loop1 fd) `ile` i_iter body' ());
  itest1 fd;
  assert (th (loop1 fd) `ile` iloop1 fd)
