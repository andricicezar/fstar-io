(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Monotonic.IFC.Heap

open FStar.Preorder
open FStar.Classical
module F = FStar.FunctionalExtensionality

private noeq type heap_rec = {
  next_addr: pos;
  memory   : F.restricted_t pos (fun (x:pos) 
             -> option (a:Type0 & rel:(option (preorder a)) & b:bool & a)) 
                      //type, preorder, mm flag, and value
}

let heap = h:heap_rec{(forall (n:nat). n >= h.next_addr ==> None? (h.memory n))}

type map_addr_label = F.restricted_t pos (fun _ -> label)

type lheap = heap * map_addr_label

let equal (h1, ll1) (h2, ll2) =
  let _ = () in
  h1.next_addr = h2.next_addr /\
  FStar.FunctionalExtensionality.feq h1.memory h2.memory /\
  FStar.FunctionalExtensionality.feq ll1 ll2

let equal_extensional h1 h2 = ()

let emp = ({
  next_addr = 1;
  memory    = F.on_dom pos (fun r -> None)
}, F.on_dom pos (fun _ -> High))

let next_addr (h, _) = h.next_addr

noeq
type core_mref (a:Type0) : Type0 = {
  addr: (x: nat { x > 0 } );
  init: a;
  mm:   bool;  //manually managed flag
}

let addr_of #a #rel r = r.addr

let is_mm #a #rel r = r.mm

let contains #a #rel (h, ll) r =
  let _ = () in
  Some? (h.memory r.addr) /\
  (let Some (| a1, pre_opt, mm, _ |) = h.memory r.addr in
   a == a1 /\ Some? pre_opt /\ Some?.v pre_opt == rel /\ mm = r.mm)  //using `===` here, since otherwise typechecker fails with a and a1 being different types, why?

let label_of r lh = FStar.Ghost.hide ((snd lh) (addr_of r))

let addr_unused_in n (h, _) = n <> 0 && None? (h.memory n)

let not_addr_unused_in_nullptr h = ()

let unused_in #a #rel r h = addr_unused_in (addr_of r) h

module FSet = FStar.FiniteSet.Base

let get_hdom h =
  FSet.all_finite_set_facts_lemma ();
  let rec aux (n:nat) : res:(FSet.set nat){forall i. 0 < i && i <= n ==> i `FSet.mem` res} =
    if n = 0 then FSet.emptyset else FSet.singleton n `FSet.union` (aux (n-1)) in
  aux ((fst h).next_addr-1)

let sel_tot #a #rel (h, _) r =
  let Some (| _, _, _, x |) = h.memory r.addr in
  x

//
// We want to provide a `sel` API to the client that does not require a
//   `contains` precondition, so that the clients don't have to prove it at
//   every use of `sel`
//
// To do so, we need to be able to branch on whether the ref is contained in the heap
//
// But that's a problem since `contains` is in prop
//
// The following function assumes a boolean returning version of contains
//   We could implement is using the classical strong excluded middle axiom,
//   but we prefer to assume an specialized instance of it
//
assume val contains_bool (#a:Type0) (#rel:preorder a) (lh:lheap) (r:mref a rel)
  : GTot (b:bool{b <==> (lh `contains` r)})

let sel #a #rel h r =
  if h `contains_bool` r
  then sel_tot #a h r
  else r.init

let upd_tot' (#a: Type0) (#rel: preorder a) (h: heap) (r: mref a rel) (x: a) =
  { h with memory = F.on_dom pos (fun r' -> if r.addr = r'
			                 then Some (| a, Some rel, r.mm, x |)
                                         else h.memory r') }

let upd_tot #a #rel (h,ll) r x = (upd_tot' h r x, ll)

let extend_map addr l ll =
  F.on_dom pos (fun addr' -> if addr = addr' then l else ll addr')

let upd #a #rel hll r x =
  if hll `contains_bool` r
  then upd_tot hll r x
  else
    let h, ll = hll in
    if r.addr >= h.next_addr
    then
      ({ next_addr = r.addr + 1;
        memory    = F.on_dom pos (fun r' -> if r' = r.addr
	   		                 then Some (| a, Some rel, r.mm, x |)
                                         else h.memory r') }, 
        extend_map r.addr High ll)
    else
      ({ h with memory = F.on_dom pos (fun r' -> if r' = r.addr
				             then Some (| a, Some rel, r.mm, x |)
                                             else h.memory r') }, ll)

val alloc_heap: #a:Type0 -> rel:preorder a -> heap -> a -> mm:bool -> Tot (mref a rel * heap)
let alloc_heap #a rel h x mm =
  let r = { addr = h.next_addr; init = x; mm = mm } in
  r, { next_addr = r.addr + 1;
       memory    = F.on_dom pos (fun r' -> if r' = r.addr
	   		                then Some (| a, Some rel, r.mm, x |)
                                        else h.memory r') }

let alloc #a rel (h, ll) x mm =
  let r, h' = alloc_heap #a rel h x mm in
  (r, (h', extend_map r.addr High ll)) (* We have to extend ll because we don't know that the new address was not used before in ll. *)

let declassify_tot #a #rel ((h, ll):lheap) l (r:mref a rel) =
  (h, extend_map r.addr l ll)
  
(*
 * update of a well-typed mreference
 *)
private let lemma_upd_contains_test
  (#a:Type) (#rel:preorder a) (h0:lheap) (r:mref a rel) (x:a)
  :Lemma (h0 `contains` r ==>
          (let h1 = upd h0 r x in
	   (forall (b:Type) (rel:preorder b) (r':mref b rel). (h0 `contains` r' /\ addr_of r' = addr_of r) ==> sel h1 r' == x) /\
     (forall (b:Type) (rel:preorder b) (r':mref b rel). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r')             /\
	   (forall (b:Type) (rel:preorder b) (r':mref b rel). h0 `contains` r' <==> h1 `contains` r')                         /\
	   (forall (b:Type) (rel:preorder b) (r':mref b rel). r' `unused_in` h0  <==> r' `unused_in` h1)))
  = ()

(*
 * update of a mreference that is mapped but not necessarily well-typed
 * we cannot prove that h0 `contains` r' ==> h1 `contains` r'
 * because consider that in h0 (r:mref a) contains (| b, y:b |),
 * and that (r':mref b) s.t. r'.addr = r.addr
 * in h0, r' is well-typed, but in h1 it's not
 *)
private let lemma_upd_contains_not_necessarily_well_typed_test
  (#a:Type) (#rel:preorder a) (h0:lheap) (r:mref a rel) (x:a)
  :Lemma ((~ (r `unused_in` h0)) ==>
          (let h1 = upd h0 r x in
	   h1 `contains` r /\
           (forall (b:Type) (#rel:preorder b) (r':mref b rel). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r')           /\
	   (forall (b:Type) (#rel:preorder b) (r':mref b rel). (r'.addr <> r.addr /\ h0 `contains` r') ==> h1 `contains` r') /\
	   (forall (b:Type) (#rel:preorder b) (r':mref b rel). r' `unused_in` h0 <==> r' `unused_in` h1)))
  = ()

(*
 * update of an unused mreference
 *)
private let lemma_upd_unused_test
  (#a:Type) (#rel:preorder a) (h0:lheap) (r:mref a rel) (x:a)
  :Lemma (r `unused_in` h0 ==>
          (let h1 = upd h0 r x in
	   h1 `contains` r /\
           (forall (b:Type) (rel:preorder b) (r':mref b rel). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
	   (forall (b:Type) (rel:preorder b) (r':mref b rel). h0 `contains` r' ==> h1 `contains` r')             /\
	   (forall (b:Type) (rel:preorder b) (r':mref b rel). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1))))
  = ()

(*
 * alloc and alloc_mm behaves just like upd of an unmapped mreference
 *)
private let lemma_alloc_test (#a:Type) (rel:preorder a) (h0:lheap) (x:a) (mm:bool)
  :Lemma (let (r, h1) = alloc rel h0 x mm in
          r `unused_in` h0 /\
	  h1 `contains` r  /\
          is_mm r = mm     /\
          (forall (b:Type) (rel:preorder b) (r':mref b rel). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
          (forall (b:Type) (rel:preorder b) (r':mref b rel). h0 `contains` r' ==> h1 `contains` r')             /\
	  (forall (b:Type) (rel:preorder b) (r':mref b rel). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1)))
  = ()

private let lemma_alloc_fresh_test (#a:Type) (rel:preorder a) (h0:lheap) (x:a) (mm:bool)
  :Lemma (let r, h1 = alloc rel h0 x mm in
          fresh r h0 h1 /\ modifies Set.empty h0 h1)
  = ()

let lemma_ref_unused_iff_addr_unused #a #rel h r = ()
let lemma_contains_implies_used #a #rel h r = ()
let lemma_distinct_addrs_distinct_types #a #b #rel1 #rel2 h r1 r2 = ()
let lemma_distinct_addrs_distinct_preorders u = ()
let lemma_distinct_addrs_distinct_mm u = ()
let lemma_distinct_addrs_unused #a #b #rel1 #rel2 h r1 r2 = ()

let lemma_alloc #a rel lh0 x mm =
  let r, lh1 = alloc rel lh0 x mm in
  let lh1' = upd lh0 r x in
  assert (equal lh1 lh1')

let lemma_free_mm_sel #a #b #rel1 #rel2 h0 r1 r2 = ()
let lemma_free_mm_contains #a #b #rel1 #rel2 h0 r1 r2 = ()
let lemma_free_mm_unused #a #b #rel1 #rel2 h0 r1 r2 = ()
let lemma_free_addr_unused_in #a #rel h r n = ()
let lemma_sel_same_addr' #a #b h r1 r2 = ()
let lemma_sel_same_addr #a #rel h r1 r2 = ()
let lemma_sel_upd1 #a #rel h r1 x r2 = ()
let lemma_sel_upd2 #a #b #rel1 #rel2 h r1 r2 x = ()
let lemma_mref_injectivity = ()
let lemma_in_dom_emp #a #rel r = ()
let lemma_upd_contains #a #rel h r x = ()
let lemma_well_typed_upd_contains #a #b #rel1 #rel2 h r1 x r2 = ()
let lemma_unused_upd_contains #a #b #rel1 #rel2 h r1 x r2 = ()
let lemma_upd_contains_different_addr #a #b #rel1 #rel2 h r1 x r2 = ()
let lemma_upd_unused #a #b #rel1 #rel2 h r1 x r2 = ()
let lemma_contains_upd_modifies #a #rel h r x = ()
let lemma_contains_upd_modifies_classification #a #rel h r x = ()
let lemma_contains_upd_modifies_only_label #a #rel h r x = ()
let lemma_unused_upd_modifies #a #rel h r x = ()

let lemma_sel_equals_sel_tot_for_contained_refs #a #rel h r = ()
let lemma_upd_equals_upd_tot_for_contained_refs #a #rel h r x = ()
let lemma_modifies_and_equal_dom_sel_diff_addr #a #rel s h0 h1 r = ()

// let lemma_heap_equality_upd_same_addr #a #rel h (r1:mref a rel) (r2:mref a rel) x =
//   assert (equal (upd h r1 x) (upd h r2 x))

// let lemma_heap_equality_cancel_same_mref_upd #a #rel h r x y =
//   let h0 = upd (upd h r x) r y in
//   let h1 = upd h r y in
//   assert (equal h0 h1)

// let lemma_heap_equality_upd_with_sel #a #rel h r =
//   let h' = upd h r (sel h r) in
//   let Some (| _, _, _, _ |) = h.memory r.addr in
//   assert (equal h h')

// let lemma_heap_equality_commute_distinct_upds #a #b #rel_a #rel_b h r1 r2 x y =
//   let h0 = upd (upd h r1 x) r2 y in
//   let h1 = upd (upd h r2 y) r1 x in
//   assert (equal h0 h1)

let lemma_next_addr_upd_tot #_ #_ _ _ _ = ()
let lemma_next_addr_upd #_ #_ _ _ _ = ()
let lemma_next_addr_alloc #_ _ _ _ _ = ()
let lemma_next_addr_free_mm #_ #_ _ _ = ()
let lemma_next_addr_contained_refs_addr #_ #_ _ _ = ()

let lemma_declassify_tot #a #rel h0 l r = ()
let lemma_modifies_only_other_label #a #rel h0 h1 r = ()