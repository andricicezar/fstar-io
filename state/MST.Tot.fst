module MST.Tot


open FStar.Tactics
open FStar.Preorder
open FStar.Monotonic.Heap
open MST.Repr

module W = FStar.Monotonic.Witnessed

(* Total state effect --- the heap is first-order *)

let st_pre   = st_pre_h   heap
let st_post' = st_post_h' heap
let st_post  = st_post_h  heap
let st_wp    = st_mwp_h   heap

val mheap : (a:Type u#a) -> st_wp a -> Type u#(max 1 a)
let mheap = mst

val mheap_bind :
  (a : Type u#a) ->
  (b : Type u#b) ->
  (wp_v : st_wp a) ->
  wp_f: (a -> st_wp b) ->
  (v : mheap a wp_v) ->
  (f : (x:a -> mheap b (wp_f x))) ->
  Tot (mheap b (st_bind_wp heap a b wp_v wp_f))
let mheap_bind a b wp_v wp_f v f = mst_bind #a #b #wp_v #wp_f v f

val mheap_return : (a:Type) -> (x:a) -> mheap a (st_return heap a x)
let mheap_return a = mst_return #a


val mheap_subcomp :
  (a : Type u#a) ->
  (wp1 : st_wp a) ->
  (wp2 : st_wp a) ->
  (v : mheap a wp1) ->
  Pure (mheap a wp2) (requires (wp1 ⊑ wp2)) (ensures (fun _ -> True))
let mheap_subcomp a wp1 wp2 = mst_subcomp #a #wp1 #wp2

let mheap_if_then_else (a : Type u#a)
  (#wp1 : st_wp a)
  (#wp2 : st_wp a)
  (f : mheap a wp1) (g : mheap a wp2) (b : bool) : Type =
  mheap a (st_if_then_else heap a b wp1 wp2)

[@@ top_level_effect]
total
reifiable
reflectable
effect {
  STATEwp (a:Type) (wp : st_wp a)
  with {
       repr       = mheap
     ; return     = mheap_return
     ; bind       = mheap_bind
     ; subcomp    = mheap_subcomp
     ; if_then_else = mheap_if_then_else
     }
}

effect ST (a:Type) (pre:st_pre) (post: (h:heap -> Tot (st_post' a (pre h)))) =
  STATEwp a (fun (p:st_post a) (h0:heap) -> pre h0 /\ (forall a h1. h0 `heap_rel` h1 /\ post h0 a h1 ==> p a h1))
effect St (a:Type) = ST a (fun h -> True) (fun h0 r h1 -> True)

unfold
let wp_lift_pure_st (w : pure_wp 'a) : st_wp 'a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fun p h -> w (fun r -> p r h)

val lift_pure_mst :
  a: Type u#a ->
  w: pure_wp a ->
  f: (eqtype_as_type unit -> PURE a w) ->
  Tot (mheap a (wp_lift_pure_st w))
let lift_pure_mst a w f =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs = partial_return (as_requires w) in
  let rhs = (fun (pre:(squash (as_requires w))) -> mheap_return a (f pre)) in
  let m = mheap_bind _ _ _ _ lhs rhs in
  mheap_subcomp _ _ _ m

sub_effect PURE ~> STATEwp = lift_pure_mst

let contains_pred (#a:Type) (#rel:preorder a) (r:mref a rel) = fun h -> h `contains` r

let witness (pred:heap_predicate) : STATEwp unit (fun p h -> pred h /\ stable pred /\ (witnessed pred ==> p () h)) =
  STATEwp?.reflect (mst_witness pred)

let recall (pred:heap_predicate_stable) : STATEwp unit (fun p h -> witnessed pred /\ (pred h ==> p () h)) =
  STATEwp?.reflect (mst_recall pred)

let alloc (#a:Type) (#rel:preorder a) (init:a) :
  ST (mref a rel) (fun h -> True) (alloc_post init)
= STATEwp?.reflect (mst_alloc init)

let read (#a:Type) (#rel:preorder a) (r:mref a rel) :
  STATEwp a (fun p h0 -> h0 `contains` r /\ p (sel h0 r) h0)
= STATEwp?.reflect (mst_read r)

let write (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a) :
  ST unit
    (fun h0 -> h0 `contains` r /\ rel (sel h0 r) v)
    (write_post #a #rel r v)
= STATEwp?.reflect (mst_write r v)

let op_Bang (#a:Type) (#rel:preorder a) (r:mref a rel)
  : STATEwp a (fun p h0 -> h0 `contains` r /\ p (sel h0 r) h0)
= read #a #rel r

let op_Colon_Equals (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
  : ST unit
    (fun h0 -> h0 `contains` r /\ rel (sel h0 r) v)
    (write_post r v)
= write #a #rel r v

type ref (a:Type0) = mref a (FStar.Heap.trivial_preorder a)

noeq type linkedList (a: Type0) : Type0 =
| LLNil : linkedList a
| LLCons : v:a -> next:ref (linkedList a) -> linkedList a
