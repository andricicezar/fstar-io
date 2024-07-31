module IFC.Heap.ST

open FStar.Tactics
open FStar.Set
open FStar.Preorder
open Monotonic.IFC.Heap

module W = FStar.Monotonic.Witnessed

val lheap_rel : preorder lheap
let lheap_rel (h1:lheap) (h2:lheap) =
  (* classic heap monotonicity: references cannot be deallocated *)
  (forall (a:Type0) (rel:preorder a) (r:mref a rel). 
    h1 `contains` r ==> (h2 `contains` r /\ rel (sel h1 r) (sel h2 r))) 
  
  /\

  (* references can only be declassified *)
  (forall (a:Type) (rel:preorder a) (r:mref a rel). 
    h1 `contains` r ==> (label_of r h1) `label_gte` (label_of r h2))

type lheap_predicate = lheap -> Type0

new_effect GST = STATE_h lheap

let gst_pre           = st_pre_h lheap
let gst_post' (a:Type) (pre:Type) = st_post_h' lheap a pre
let gst_post  (a:Type) = st_post_h lheap a
let gst_wp (a:Type)   = st_wp_h lheap a

unfold let lift_div_gst (a:Type) (wp:pure_wp a) (p:gst_post a) (h:lheap) = wp (fun a -> p a h)
sub_effect DIV ~> GST = lift_div_gst

let stable (p:lheap_predicate) =
  forall (h1:lheap) (h2:lheap). (p h1 /\ lheap_rel h1 h2) ==> p h2

[@@"opaque_to_smt"]
let witnessed (p:lheap_predicate) = W.witnessed lheap_rel p

private
assume val gst_get: unit    -> GST lheap (fun p h0 -> p h0 h0)
private
assume val gst_put: h1:lheap -> GST unit (fun p h0 -> lheap_rel h0 h1 /\ p () h1)

assume val gst_witness: p:lheap_predicate -> GST unit (fun post h0 -> p h0 /\ stable p /\ (witnessed p ==> post () h0))
assume val gst_recall:  p:lheap_predicate -> GST unit (fun post h0 -> witnessed p /\ (p h0 ==> post () h0))

val lemma_functoriality (p:lheap_predicate{stable p /\ witnessed p}) 
                        (q:lheap_predicate{stable q /\ (forall (h:lheap). p h ==> q h)})
  :Lemma (ensures (witnessed q))
let lemma_functoriality p q =
  reveal_opaque (`%witnessed) witnessed;
  W.lemma_witnessed_weakening lheap_rel p q

let st_pre   = gst_pre
let st_post' = gst_post'
let st_post  = gst_post
let st_wp    = gst_wp

new_effect STATE = GST

unfold let lift_gst_state (a:Type) (wp:gst_wp a) = wp
sub_effect GST ~> STATE = lift_gst_state

effect State (a:Type) (wp:st_wp a) = STATE a wp

effect ST (a:Type) (pre:st_pre) (post: (h:lheap -> Tot (st_post' a (pre h)))) =
  STATE a (fun (p:st_post a) (h:lheap) -> pre h /\ (forall a h1. post h a h1 ==> p a h1))
effect St (a:Type) = ST a (fun h -> True) (fun h0 r h1 -> True)

let contains_pred (#a:Type0) (#rel:preorder a) (r:mref a rel) = fun lh -> lh `contains` r

let contains_stable (#a:Type0) (#rel:preorder a) (r:mref a rel) : Lemma (stable (contains_pred r)) 
  [SMTPat (contains_pred r)]=
  assert (stable (contains_pred r)) by (
    norm [delta_only [`%stable;`%lheap_rel]; iota]
  )

type mref (a:Type0) (rel:preorder a) = 
  r:(mref a rel){is_mm r = false /\ witnessed (contains_pred r)}
  (** ^ we could define our own ref type that contains that they are low *)

let recall (#a:Type) (#rel:preorder a) (r:mref a rel) :STATE unit (fun p lh -> lh `contains` r ==> p () lh)
  = gst_recall (contains_pred r)  

let alloc_post (#a:Type) (#rel:preorder a) (init:a) (h0:lheap) (r:mref a rel) (h1:lheap) : Type0 =
  fresh r h0 h1 /\ 
  modifies Set.empty h0 h1 /\
  modifies_classification Set.empty h0 h1 /\
  sel h1 r == init /\ 
  label_of r h1 == High


let alloc (#a:Type) (#rel:preorder a) (init:a)
: ST (mref a rel) (fun h -> True) (alloc_post #a #rel init)
= let h0 = gst_get () in
  let r, h1 = alloc rel h0 init false in
  assert (lheap_rel h0 h1) by (norm [delta_only [`%lheap_rel]; iota]);
  gst_put h1;
  gst_witness (contains_pred r);
  r

let read (#a:Type) (#rel:preorder a) (r:mref a rel) : STATE a (fun p h -> p (sel h r) h)
= let h0 = gst_get () in
  gst_recall (contains_pred r);
  lemma_sel_equals_sel_tot_for_contained_refs h0 r;
  sel_tot h0 r    

let write_post (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a) (h0:lheap) () (h1:lheap) : Type0 =
  // h1 == (upd h0 r v) /\
  rel (sel h0 r) v /\ 
  h0 `contains` r /\
  modifies (Set.singleton (addr_of r)) h0 h1 /\ 
  equal_dom h0 h1 /\
  modifies_classification Set.empty h0 h1 /\
  sel h1 r == v

let write (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
: ST unit
  (fun h -> rel (sel h r) v)
  (write_post #a #rel r v)
= let h0 = gst_get () in
  gst_recall (contains_pred r);
  let h1 = upd_tot h0 r v in
  lemma_distinct_addrs_distinct_preorders ();
  lemma_distinct_addrs_distinct_mm ();
  lemma_upd_equals_upd_tot_for_contained_refs h0 r v;
  assert (lheap_rel h0 h1) by (norm [delta_only [`%lheap_rel]; iota]);
  gst_put h1

let modifies_none (h0:lheap) (h1:lheap) = modifies Set.empty h0 h1

let declassify_post (#a:Type) (#rel:preorder a) (r:mref a rel) (l:label) (h0:lheap) () (h1:lheap) : Type0 =
  h1 `contains` r /\
  equal_dom h0 h1 /\ (* TODO: define equal_heaps *)
  modifies_none h0 h1 /\
  modifies_classification (Set.singleton (addr_of r)) h0 h1 /\ 
  label_of r h1 == l

let declassify (#a:Type) (#rel:preorder a) (r:mref a rel) (l:label)
: ST unit
  (fun h -> label_of r h `label_gte` l)
  (declassify_post #a #rel r l)
=
  let h0 = gst_get () in
  gst_recall (contains_pred r);
  let h1 = declassify_tot #a #rel h0 l r in
  assert (lheap_rel h0 h1) by (norm [delta_only [`%lheap_rel]; iota]);
  gst_put h1


let op_Bang (#a:Type) (#rel:preorder a) (r:mref a rel)
  : STATE a (fun p h -> p (sel h r) h)
= read #a #rel r

let op_Colon_Equals (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
: ST unit
  (fun h -> rel (sel h r) v)
  (write_post #a #rel r v)
= write #a #rel r v

type ref (a:Type0) = mref a (FStar.Heap.trivial_preorder a)

let get (u:unit) :ST (FStar.Ghost.erased lheap) (fun h -> True) (fun h0 h h1 -> h0==h1 /\ (FStar.Ghost.reveal h)==h1) =
  gst_get ()

let is_low_pred (#a:Type0) (r:ref a) = fun lh -> lh `contains` r /\ label_of r lh == Low

let is_low_pred_stable (#a:Type0) (r:ref a) : Lemma (stable (is_low_pred r))
  [SMTPat (is_low_pred r)] =  
  assert (stable (is_low_pred r)) by (
    norm [delta_only [`%stable;`%lheap_rel]; iota]
  )

type lref (a:Type0) = 
  r:(ref a){witnessed (is_low_pred r)}

let declassify_low (#a:Type) (r:ref a)
: ST (lref a)
  (fun h -> label_of r h `label_gte` Low)
  (fun h0 _ h1 -> declassify_post r Low h0 () h1)
=
  declassify r Low;
  gst_witness (is_low_pred r);
  r

// val lemma_modifies_only_label_trans
//   (l:label) (h0 h1 h2:lheap)
//   : Lemma (
//     (lheap_rel h0 h1 /\ lheap_rel h1 h2 /\
//     modifies_only_label l h0 h1 /\ modifies_only_label l h1 h2) ==>
//       modifies_only_label l h0 h2)
//   [SMTPat (modifies_only_label l h0 h1); SMTPat (modifies_only_label l h1 h2)]
// let lemma_modifies_only_label_trans _ _ _ _ = ()
