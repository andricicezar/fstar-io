module SharedInPulse


open Pulse.Lib.Pervasives

module H = PulseCore.Heap
module GR = Pulse.Lib.MonotonicGhostRef
open FStar.Preorder
open Pulse.Lib.Stick

type addr = nat
let addr_of = H.core_ref_as_addr

type map_sharedT = 
  GR.mref #(addr -> bool) (fun (m0 m1:addr -> bool) -> forall p. m0 p ==> m1 p)

noeq
type sigT = {
  map_shared : map_sharedT;
  is_shared : #a:Type0 -> ref a -> slprop; (** one should add back here monotonic references.  *)
  // is_shared_stable : #a:Type0 -> r:ref a -> Lemma (stable (is_shared r) (fun _ _ -> True)) [SMTPat (is_shared r)];

  share : #a:Type0 -> sr:(ref a) -> #v:erased a -> #ms:erased (addr -> bool) ->
    stt_ghost unit 
      (* invariants *)
      FStar.GhostSet.empty 

      (* requires *)
      (
        pts_to sr v **
        GR.pts_to map_shared #1.0R ms ** (** no idea how this work **)
        // *addr_of sr =!= addr_of map_shared) (** we should not need this anymore, since map_share is ghost **)

        //(forall p. p >= next_addr h0 ==> ~(sel h0 map_shared p)))) (** necessary to prove that freshly allocated references are not shared **)       
        (forall* r. (forall* v. not* (pts_to r v) @==> ~(is_shared r)))
      ) 


      
      (* ensures *)
      (fun _ -> emp)
      //   h0 `contains` sr /\
      //   h0 `contains` map_shared /\
      //   (addr_of sr =!= addr_of map_shared) /\ (** prevent sharing the map *)
      //   ~(is_shared (map_shared) h0) /\
      //   (forall p. p >= next_addr h0 ==> ~(sel h0 map_shared p)))) (** necessary to prove that freshly allocated references are not shared **)
      // (ensures (fun h0 _ h1 ->
      //   modifies !{map_shared} h0 h1 /\
      //   ~(is_shared (map_shared) h1) /\
      //   (forall b (r:ref b). is_shared r h0 ==> is_shared r h1) /\
      //   (forall b (r:ref b). ~(is_shared r h0) /\ addr_of r =!= addr_of sr ==> ~(is_shared r h1)) /\
      //   (forall p. p >= next_addr h1 ==> ~(sel h1 map_shared p)) /\
      //   is_shared sr h1))
}

let pulse_five_in_fstar = five ()
