module Labeled.MST

open FStar.Tactics
open FStar.Set
open FStar.Preorder
open Labeled.Monotonic.Heap
open MST

module W = FStar.Monotonic.Witnessed

val lheap_rel : preorder lheap
let lheap_rel (h1:lheap) (h2:lheap) = 
  (* classic heap monotonicity: references cannot be deallocated *)
  (forall (a:Type0) (rel:preorder a) (r:mref a rel). 
    h1 `contains` r ==> (h2 `contains` r /\ rel (sel h1 r) (sel h2 r))) 
  
  /\

  (* TODO: can this part of the relation be moved at the reference level? do we need all references to be labeled? *)
  (* references can only be declassified *)
  (forall (a:Type) (rel:preorder a) (r:mref a rel). 
    h1 `contains` r ==> (label_of r h1) `label_gte` (label_of r h2))

type lheap_predicate = lheap -> Type0

let heap_state : tstate = { t = lheap; rel = lheap_rel }

let stable (p:lheap_predicate) = stable p heap_state.rel

let _mst a wp = mst heap_state a wp
let _mst_bind a b wp_v wp_f v f = mst_bind #heap_state #a #b #wp_v #wp_f v f
let _mst_return a x = mst_return #heap_state #a x

let _mst_subcomp a (wp1:st_wp heap_state.t a) (wp2:st_wp heap_state.t a) v:
  Pure (_mst a wp2) (requires (wp1 ⊑ wp2)) (ensures (fun _ -> True)) = 
  mst_subcomp #heap_state #a #wp1 #wp2 v

let _mst_if_then_else (a : Type u#a)
  (#wp1 : st_wp heap_state.t a)
  (#wp2 : st_wp heap_state.t a)
  (f : _mst a wp1) (g : _mst a wp2) (b : bool) : Type =
  _mst a (st_if_then_else heap_state.t a b wp1 wp2)

total
reifiable
reflectable
effect {
  STATEwp (a:Type) (wp : st_wp heap_state.t a)
  with {
       repr       = _mst
     ; return     = _mst_return
     ; bind       = _mst_bind
     ; subcomp    = _mst_subcomp
     ; if_then_else = _mst_if_then_else
     }
}

unfold
let wp_lift_pure_st (w : pure_wp 'a) : st_wp heap_state.t 'a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fun p h -> w (fun r -> p r h)

val lift_pure_mst :
  a: Type u#a ->
  w: pure_wp a ->
  f: (eqtype_as_type unit -> PURE a w) ->
  Tot (_mst a (wp_lift_pure_st w))
let lift_pure_mst a w f =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs = partial_return heap_state (as_requires w) in
  let rhs = (fun (pre:(squash (as_requires w))) -> _mst_return a (f pre)) in
  let m = _mst_bind _ _ _ _ lhs rhs in
  _mst_subcomp _ _ _ m

sub_effect PURE ~> STATEwp = lift_pure_mst

private
let _get () : STATEwp lheap get_wp = 
  STATEwp?.reflect (mst_get ())

private
let _put (h1:lheap) : STATEwp unit (put_wp h1) = 
  STATEwp?.reflect (mst_put h1)

type heap_predicate = lheap -> Type0

[@@"opaque_to_smt"]
let witnessed (pred:heap_predicate{stable pred}) : Type0 = W.witnessed heap_state.rel pred

let mst_witness (pred:heap_predicate) : STATEwp unit (fun p h -> pred h /\ stable pred /\ (witnessed pred ==> p () h)) = 
  STATEwp?.reflect (mst_witness pred)

let mst_recall (pred:heap_predicate{stable pred}) : STATEwp unit (fun p h -> witnessed pred /\ (pred h ==> p () h)) = 
  STATEwp?.reflect (mst_recall pred)

(** *** From here it is mostly a COPY-PASTE from FStar.ST **)
let st_pre           = st_pre_h lheap
let st_post' (a:Type) (pre:Type) = st_post_h' lheap a pre
let st_post  (a:Type) = st_post_h lheap a
let st_wp (a:Type)   = st_wp_h lheap a

effect ST (a:Type) (pre:st_pre) (post: (h:lheap -> Tot (st_post' a (pre h)))) =
  STATEwp a (fun (p:st_post a) (h:lheap) -> pre h /\ (forall a h1. h `lheap_rel` h1 /\ post h a h1 ==> p a h1))
effect St (a:Type) = ST a (fun h -> True) (fun h0 r h1 -> True)

// unfold let lift_div_gst (a:Type) (wp:pure_wp a) (p:gst_post a) (h:lheap) = wp (fun a -> p a h)
// sub_effect DIV ~> GST = lift_div_gst

val lemma_functoriality (p:lheap_predicate{stable p /\ witnessed p}) 
                        (q:lheap_predicate{stable q /\ (forall (h:lheap). p h ==> q h)})
  :Lemma (ensures (witnessed q))
let lemma_functoriality p q =
  reveal_opaque (`%witnessed) witnessed;
  W.lemma_witnessed_weakening lheap_rel p q

let contains_pred (#a:Type0) (#rel:preorder a) (r:mref a rel) = fun lh -> lh `contains` r /\ is_mm r = false

let contains_stable (#a:Type0) (#rel:preorder a) (r:mref a rel) : Lemma (stable (contains_pred r)) 
  [SMTPat (contains_pred r)] by (unfold_def (`stable)) = ()

type mref (a:Type0) (rel:preorder a) = 
  mref a rel

let alloc_post (#a:Type) (#rel:preorder a) (init:a) (h0:lheap) (r:mref a rel) (h1:lheap) : Type0 =
  fresh r h0 h1 /\ 
  h1 == upd h0 r init /\ 
  modifies Set.empty h0 h1 /\
  modifies_classification Set.empty h0 h1 /\
  sel h1 r == init /\ 
  label_of r h1 == High /\
  is_mm r == false


let alloc (#a:Type) (#rel:preorder a) (init:a)
: ST (mref a rel) (fun h -> True) (alloc_post #a #rel init)
= let h0 = _get () in
  let r, h1 = alloc rel h0 init false in
  assert (lheap_rel h0 h1) by (norm [delta_only [`%lheap_rel]; iota]);
  _put h1;
  r

let read (#a:Type) (#rel:preorder a) (r:mref a rel) : STATEwp a (fun p h -> contains_pred r h /\ p (sel h r) h)
= let h0 = _get () in
  lemma_sel_equals_sel_tot_for_contained_refs h0 r;
  sel_tot h0 r    

let write_post (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a) (h0:lheap) () (h1:lheap) : Type0 =
  // h1 == (upd h0 r v) /\
  rel (sel h0 r) v /\ 
  h0 `contains` r /\
  modifies (Set.singleton (addr_of r)) h0 h1 /\ 
  modifies_only_label (label_of r h0) h0 h1 /\
  equal_dom h0 h1 /\
  modifies_classification Set.empty h0 h1 /\
  sel h1 r == v

let write (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
: ST unit
  (fun h -> contains_pred r h /\ rel (sel h r) v)
  (write_post #a #rel r v)
= let h0 = _get () in
  let h1 = upd_tot h0 r v in
  lemma_distinct_addrs_distinct_preorders ();
  lemma_distinct_addrs_distinct_mm ();
  lemma_upd_equals_upd_tot_for_contained_refs h0 r v;
  assert (lheap_rel h0 h1) by (norm [delta_only [`%lheap_rel]; iota]);
  _put h1

let modifies_none (h0:lheap) (h1:lheap) = modifies Set.empty h0 h1

let declassify_post (#a:Type) (#rel:preorder a) (r:mref a rel) (l:label) (h0:lheap) () (h1:lheap) : Type0 =
  h1 `contains` r /\
  equal_dom h0 h1 /\
  modifies_none h0 h1 /\
  modifies_classification (only r) h0 h1 /\ 
  label_of r h1 == l

let declassify (#a:Type) (#rel:preorder a) (r:mref a rel) (l:label)
: ST unit
  (fun h -> contains_pred r h /\ label_of r h `label_gte` l)
  (declassify_post #a #rel r l)
=
  let h0 = _get () in
  let h1 = declassify_tot #a #rel h0 l r in
  assert (lheap_rel h0 h1) by (norm [delta_only [`%lheap_rel]; iota]);
  _put h1


let op_Bang (#a:Type) (#rel:preorder a) (r:mref a rel)
  : STATEwp a (fun p h -> contains_pred r h /\ p (sel h r) h)
= read #a #rel r

let op_Colon_Equals (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
: ST unit
  (fun h -> contains_pred r h /\ rel (sel h r) v)
  (write_post #a #rel r v)
= write #a #rel r v

type ref (a:Type0) = mref a (FStar.Heap.trivial_preorder a)

let get (u:unit) :ST (FStar.Ghost.erased lheap) (fun h -> True) (fun h0 h h1 -> h0==h1 /\ (FStar.Ghost.reveal h)==h1) =
  _get ()

let is_low_pred (#a:Type0) (#rel:preorder a) (r:mref a rel) = fun h -> contains_pred r h /\ label_of r h == Low

let is_low_pred_stable (#a:Type0) (r:ref a) : Lemma (stable (is_low_pred r))
  [SMTPat (is_low_pred r)] by (unfold_def (`stable)) = ()

let declassify_low (#a:Type) (r:ref a)
: ST (ref a)
  (fun h -> contains_pred r h /\ label_of r h `label_gte` Low)
  (fun h0 r' h1 -> 
    r == r' /\
    contains_pred r' h1 /\
    is_low_pred r' h1 /\
    declassify_post r' Low h0 () h1)
=
  declassify r Low;
  r


val lemma_modifies_only_label_trans
   (l:label) (h0 h1 h2:lheap)
   : Lemma
     (requires 
      modifies_classification Set.empty h0 h1 /\ 
      lheap_rel h0 h1 /\ 
      lheap_rel h1 h2 /\
      modifies_only_label l h0 h1 /\ 
      modifies_only_label l h1 h2)
     (ensures modifies_only_label l h0 h2)
let lemma_modifies_only_label_trans l h0 h1 h2 = 
  assert (unmodified_common h0 h1);
  assert (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (sel h1 r)} 
  (h0 `contains` r /\ ~(label_of r h0 == l)) ==> sel h0 r == sel h1 r);
  assert (unmodified_common h0 h2);
  introduce forall (a:Type) (rel:preorder a) (r:Labeled.Monotonic.Heap.mref a rel).
    (h0 `contains` r /\ ~(label_of r h0 == l)) ==> sel h0 r == sel h2 r
  with begin
    introduce (h0 `contains` r /\ ~(label_of r h0 == l)) 
      ==> sel h0 r == sel h2 r
    with _. begin
      ()
    end
  end;
  ()