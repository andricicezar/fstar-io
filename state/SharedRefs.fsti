module SharedRefs

open FStar.Tactics

open FStar.Preorder
open FStar.Monotonic.Heap
open FStar.Ghost
open MST.Tot

type map_sharedT = mref (pos -> GTot bool) (fun (m0 m1:pos -> GTot bool) -> forall p. m0 p ==> m1 p) (** pre-order necessary to show that the predicate `is_shared` is stable **)

noeq
type sigT = {
  map_shared : erased map_sharedT;
  is_shared : #a:Type0 -> #p:preorder a -> mref a p -> h:heap -> Type0;
  is_shared_stable : #a:Type0 -> r:ref a -> Lemma (stable (is_shared r)) [SMTPat (is_shared r)];
  share : #a:Type0 -> #p:preorder a -> sr:(mref a p) ->
    ST unit 
      (requires (fun h0 -> 
        h0 `contains` sr /\
        h0 `contains` map_shared /\
        (addr_of sr =!= addr_of map_shared) /\ (** prevent sharing the map *)
        ~(is_shared (map_shared) h0) /\
        (forall p. p >= next_addr h0 ==> ~(sel h0 map_shared p)))) (** necessary to prove that freshly allocated references are not shared **)
      (ensures (fun h0 _ h1 ->
        modifies !{map_shared} h0 h1 /\
        ~(is_shared (map_shared) h1) /\
        (forall b (r:ref b). is_shared r h0 ==> is_shared r h1) /\
        (forall b (r:ref b). ~(is_shared r h0) /\ addr_of r =!= addr_of sr ==> ~(is_shared r h1)) /\
        (forall p. p >= next_addr h1 ==> ~(sel h1 map_shared p)) /\
        is_shared sr h1))
}

val shareS : sigT

unfold let unmodified_common (h0:heap) (h1:heap) : Type0 =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (contains h1 r)}
                               h0 `contains` r ==> h1 `contains` r) /\
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (r `unused_in` h0)}
                               r `unused_in` h1 ==> r `unused_in` h0) /\
  (forall (n: nat) . {:pattern (n `addr_unused_in` h0) }
    n `addr_unused_in` h1 ==> n `addr_unused_in` h0)
let modifies_only_shared (h0:heap) (h1:heap) : Type0 =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (sel h1 r)} 
    (h0 `contains` r /\ ~(shareS.is_shared r h0)) ==> sel h0 r == sel h1 r) /\
  unmodified_common h0 h1

effect IST (a:Type) (pre:st_pre) (post: (h:heap -> Tot (st_post' a (pre h)))) =
  ST a 
    (requires (fun h0      -> 
      h0 `contains` shareS.map_shared /\ 
      ~(shareS.is_shared (shareS.map_shared) h0) /\ (* the map stays unshared *)
      (forall p. p >= next_addr h0 ==> ~(sel h0 shareS.map_shared p)) /\
      pre h0))
    (ensures  (fun h0 r h1 -> 
      ~(shareS.is_shared (shareS.map_shared) h1) /\
      (forall p. p >= next_addr h1 ==> ~(sel h1 shareS.map_shared p)) /\
      post h0 r h1))
