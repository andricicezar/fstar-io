module Monotonic.IFC.Heap


module S  = FStar.Set
module TS = FStar.TSet

open FStar.Preorder

let set  = Set.set
let tset = TSet.set

type label =
  | NoVisa
  | Diplomatic
  | Tourist

(**
         NoVisa
        /      \
Diplomatic    Tourist
**)

let lattice_gte (l1:label) (l2:label) : bool =
  match l1, l2 with
  | NoVisa, _ -> true
  | _ -> l1 = l2

val map_addr_label : Type u#0

val lheap :Type u#1

val equal: lheap -> lheap -> Type0

val equal_extensional (h1:lheap) (h2:lheap)
  :Lemma (requires True) (ensures (equal h1 h2 <==> h1 == h2))
         [SMTPat (equal h1 h2)]

val emp :lheap

val next_addr: lheap -> GTot pos

val core_mref ([@@@ strictly_positive] a:Type0) : Type0

let mref (a:Type0) (rel:preorder a) : Type0 = core_mref a

val addr_of: #a:Type0 -> #rel:preorder a -> mref a rel -> GTot pos

val is_mm: #a:Type0 -> #rel:preorder a -> mref a rel -> GTot bool

let compare_addrs (#a #b:Type0) (#rel1:preorder a) (#rel2:preorder b) (r1:mref a rel1) (r2:mref b rel2)
  :GTot bool = addr_of r1 = addr_of r2

val contains: #a:Type0 -> #rel:preorder a -> lheap -> mref a rel -> Type0

val label_of : #a:Type0 -> #rel:preorder a -> mref a rel -> lheap -> GTot label

val addr_unused_in: nat -> lheap -> Type0

val not_addr_unused_in_nullptr (h: lheap) : Lemma (~ (addr_unused_in 0 h))

val unused_in: #a:Type0 -> #rel:preorder a -> mref a rel -> lheap -> Type0

let fresh (#a:Type) (#rel:preorder a) (r:mref a rel) (h0:lheap) (h1:lheap) =
  r `unused_in` h0 /\ h1 `contains` r

let only_t (#a:Type0) (#rel:preorder a) (x:mref a rel) :GTot (tset nat) = TS.singleton (addr_of x)

let only (#a:Type0) (#rel:preorder a) (x:mref a rel) :GTot (set nat) = S.singleton (addr_of x)

let op_Hat_Plus_Plus (#a:Type0) (#rel:preorder a) (r:mref a rel) (s:set nat) :GTot (set nat) = S.union (only r) s

let op_Plus_Plus_Hat (#a:Type0) (#rel:preorder a) (s:set nat) (r:mref a rel) :GTot (set nat) = S.union s (only r)

let op_Hat_Plus_Hat (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (r1:mref a rel1) (r2:mref b rel2)
  :GTot (set nat) = S.union (only r1) (only r2)

val sel_tot: #a:Type0 -> #rel:preorder a -> h:lheap -> r:mref a rel{h `contains` r} -> Tot a

val sel: #a:Type0 -> #rel:preorder a -> lheap -> mref a rel -> GTot a

val upd_tot: #a:Type0 -> #rel:preorder a -> h:lheap -> r:mref a rel{h `contains` r} -> x:a -> Tot lheap

val upd: #a:Type0 -> #rel:preorder a -> h:lheap -> r:mref a rel -> x:a -> GTot lheap

val alloc: #a:Type0 -> rel:preorder a -> lheap -> a -> mm:bool -> Tot (mref a rel * lheap)

val declassify : #a:Type0 -> #rel:preorder a -> lheap -> mref a rel -> label -> Tot (option lheap)

let modifies_t (s:tset nat) (h0:lheap) (h1:lheap) =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (sel h1 r)}
                               ((~ (TS.mem (addr_of r) s)) /\ h0 `contains` r) ==> sel h1 r == sel h0 r) /\
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (contains h1 r)}
                               h0 `contains` r ==> h1 `contains` r) /\
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (r `unused_in` h0)}
                               r `unused_in` h1 ==> r `unused_in` h0) /\
  (forall (n: nat) . {:pattern (n `addr_unused_in` h0) }
    n `addr_unused_in` h1 ==> n `addr_unused_in` h0
  )


let modifies (s:set nat) (h0:lheap) (h1:lheap) = modifies_t (TS.tset_of_set s) h0 h1

let equal_dom (h1:lheap) (h2:lheap) :GTot Type0 =
  (forall (a:Type0) (rel:preorder a) (r:mref a rel).
     {:pattern (h1 `contains` r) \/ (h2 `contains` r)}
     h1 `contains` r <==> h2 `contains` r) /\
  (forall (a:Type0) (rel:preorder a) (r:mref a rel).
     {:pattern (r `unused_in` h1) \/ (r `unused_in` h2)}
     r `unused_in` h1 <==> r `unused_in` h2)

val lemma_ref_unused_iff_addr_unused (#a:Type0) (#rel:preorder a) (h:lheap) (r:mref a rel)
  :Lemma (requires True)
         (ensures  (r `unused_in` h <==> addr_of r `addr_unused_in` h))
	 [SMTPatOr [[SMTPat (r `unused_in` h)]; [SMTPat (addr_of r `addr_unused_in` h)]]]

val lemma_contains_implies_used (#a:Type0) (#rel:preorder a) (h:lheap) (r:mref a rel)
  :Lemma (requires (h `contains` r))
         (ensures  (~ (r `unused_in` h)))
	 [SMTPatOr [[SMTPat (h `contains` r)]; [SMTPat (r `unused_in` h)]]]

val lemma_distinct_addrs_distinct_types
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h:lheap) (r1:mref a rel1) (r2:mref b rel2)
  :Lemma (requires (a =!= b /\ h `contains` r1 /\ h `contains` r2))
         (ensures  (addr_of r1 <> addr_of r2))
	 [SMTPat (h `contains` r1); SMTPat (h `contains` r2)]

val lemma_distinct_addrs_distinct_preorders (u:unit)
  :Lemma (forall (a:Type0) (rel1 rel2:preorder a) (r1:mref a rel1) (r2:mref a rel2) (h:lheap).
            {:pattern (h `contains` r1); (h `contains` r2)}
	    (h `contains` r1 /\ h `contains` r2 /\ rel1 =!= rel2) ==> addr_of r1 <> addr_of r2)

val lemma_distinct_addrs_distinct_mm (u:unit)
  :Lemma (forall (a b:Type0) (rel1:preorder a) (rel2:preorder b) (r1:mref a rel1) (r2:mref b rel2) (h:lheap).
            {:pattern (h `contains` r1); (h `contains` r2)}
	    (h `contains` r1 /\ h `contains` r2 /\ is_mm r1 =!= is_mm r2) ==> addr_of r1 <> addr_of r2)

val lemma_distinct_addrs_unused
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h:lheap) (r1:mref a rel1) (r2:mref b rel2)
  :Lemma (requires (r1 `unused_in` h /\ ~ (r2 `unused_in` h)))
         (ensures  (addr_of r1 <> addr_of r2 /\ (~ (r1 === r2))))
         [SMTPat (r1 `unused_in` h); SMTPat (r2 `unused_in` h)]

val lemma_alloc (#a:Type0) (rel:preorder a) (h0:lheap) (x:a) (mm:bool)
  :Lemma (requires True)
         (ensures  (let r, h1 = alloc rel h0 x mm in
                    fresh r h0 h1 /\ h1 == upd h0 r x /\ is_mm r = mm /\ addr_of r == next_addr h0))
	 [SMTPat (alloc rel h0 x mm)]

val lemma_sel_same_addr (#a:Type0) (#rel:preorder a) (h:lheap) (r1:mref a rel) (r2:mref a rel)
  :Lemma (requires (h `contains` r1 /\ addr_of r1 = addr_of r2 /\ is_mm r1 == is_mm r2))
         (ensures  (h `contains` r2 /\ sel h r1 == sel h r2))
         [SMTPatOr [
	   [SMTPat (sel h r1); SMTPat (sel h r2)];
           [SMTPat (h `contains` r1); SMTPat (h `contains` r2)];
         ]]

val lemma_sel_upd1 (#a:Type0) (#rel:preorder a) (h:lheap) (r1:mref a rel) (x:a) (r2:mref a rel)
  :Lemma (requires (addr_of r1 = addr_of r2 /\ is_mm r1 == is_mm r2))
         (ensures  (sel (upd h r1 x) r2 == x))
         [SMTPat (sel (upd h r1 x) r2)]

val lemma_sel_upd2 (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h:lheap) (r1:mref a rel1) (r2:mref b rel2) (x:b)
  :Lemma (requires (addr_of r1 <> addr_of r2))
         (ensures  (sel (upd h r2 x) r1 == sel h r1))
	 [SMTPat (sel (upd h r2 x) r1)]

val lemma_mref_injectivity
  :(u:unit{forall (a:Type0) (b:Type0) (rel1:preorder a) (rel2:preorder b) (r1:mref a rel1) (r2:mref b rel2). a =!= b ==> ~ (r1 === r2)})

val lemma_in_dom_emp (#a:Type0) (#rel:preorder a) (r:mref a rel)
  :Lemma (requires True)
         (ensures  (r `unused_in` emp))
	 [SMTPat (r `unused_in` emp)]

val lemma_upd_contains (#a:Type0) (#rel:preorder a) (h:lheap) (r:mref a rel) (x:a)
  :Lemma (requires True)
         (ensures  ((upd h r x) `contains` r))
	 [SMTPat ((upd h r x) `contains` r)]

val lemma_well_typed_upd_contains
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h:lheap) (r1:mref a rel1) (x:a) (r2:mref b rel2)
  :Lemma (requires (h `contains` r1))
         (ensures  (let h1 = upd h r1 x in
	            h1 `contains` r2 <==> h `contains` r2))
	 [SMTPat ((upd h r1 x) `contains` r2)]

val lemma_unused_upd_contains
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h:lheap) (r1:mref a rel1) (x:a) (r2:mref b rel2)
  :Lemma (requires (r1 `unused_in` h))
         (ensures  (let h1 = upd h r1 x in
	            (h `contains` r2  ==> h1 `contains` r2) /\
		    (h1 `contains` r2 ==> (h `contains` r2 \/ addr_of r2 = addr_of r1))))
	 [SMTPat ((upd h r1 x) `contains` r2)]

val lemma_upd_contains_different_addr
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h:lheap) (r1:mref a rel1) (x:a) (r2:mref b rel2)
  :Lemma (requires (h `contains` r2 /\ addr_of r1 <> addr_of r2))
         (ensures  ((upd h r1 x) `contains` r2))
	 [SMTPat ((upd h r1 x) `contains` r2)]

val lemma_upd_unused
  (#a:Type0) (#b:Type0) (#rel1:preorder a) (#rel2:preorder b) (h:lheap) (r1:mref a rel1) (x:a) (r2:mref b rel2)
  :Lemma (requires True)
         (ensures  ((addr_of r1 <> addr_of r2 /\ r2 `unused_in` h) <==> r2 `unused_in` (upd h r1 x)))
	 [SMTPat (r2 `unused_in` (upd h r1 x))]

val lemma_contains_upd_modifies (#a:Type0) (#rel:preorder a) (h:lheap) (r:mref a rel) (x:a)
  :Lemma (requires (h `contains` r))
         (ensures  (modifies (S.singleton (addr_of r)) h (upd h r x)))
         [SMTPat (upd h r x)]

val lemma_unused_upd_modifies (#a:Type0) (#rel:preorder a) (h:lheap) (r:mref a rel) (x:a)
  :Lemma (requires (r `unused_in` h))
         (ensures  (modifies (Set.singleton (addr_of r)) h (upd h r x)))
         [SMTPat (upd h r x); SMTPat (r `unused_in` h)]

val lemma_sel_equals_sel_tot_for_contained_refs
  (#a:Type0) (#rel:preorder a) (h:lheap) (r:mref a rel{h `contains` r})
  :Lemma (requires True)
         (ensures  (sel_tot h r == sel h r))

val lemma_upd_equals_upd_tot_for_contained_refs
  (#a:Type0) (#rel:preorder a) (h:lheap) (r:mref a rel{h `contains` r}) (x:a)
  :Lemma (requires True)
         (ensures  (upd_tot h r x == upd h r x))

val lemma_modifies_and_equal_dom_sel_diff_addr
  (#a:Type0)(#rel:preorder a) (s:set nat) (h0:lheap) (h1:lheap) (r:mref a rel)
  :Lemma (requires (modifies s h0 h1 /\ equal_dom h0 h1 /\ (~ (S.mem (addr_of r) s))))
         (ensures  (sel h0 r == sel h1 r))
	 [SMTPat (modifies s h0 h1); SMTPat (equal_dom h0 h1); SMTPat (sel h1 r)]

val lemma_next_addr_upd_tot
  (#a:Type0) (#rel:preorder a) (h0:lheap) (r:mref a rel{h0 `contains` r}) (x:a)
  :Lemma (let h1 = upd_tot h0 r x in next_addr h1 == next_addr h0)

val lemma_next_addr_upd
  (#a:Type0) (#rel:preorder a) (h0:lheap) (r:mref a rel) (x:a)
  :Lemma (let h1 = upd h0 r x in next_addr h1 >= next_addr h0)

val lemma_next_addr_alloc
  (#a:Type0) (rel:preorder a) (h0:lheap) (x:a) (mm:bool)
  :Lemma (let _, h1 = alloc rel h0 x mm in next_addr h1 > next_addr h0)

val lemma_next_addr_contained_refs_addr
  (#a:Type0) (#rel:preorder a) (h:lheap) (r:mref a rel)
  :Lemma (h `contains` r ==> addr_of r < next_addr h)

val lemma_declassify_gte
  (#a:Type0) (#rel:preorder a) (hll:lheap) (r:mref a rel) (l:label)
  :Lemma (requires (label_of r hll `lattice_gte` l))
         (ensures  (Some? (declassify hll r l)))
   [SMTPat (declassify hll r l)]