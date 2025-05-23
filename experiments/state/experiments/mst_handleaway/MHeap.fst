module MHeap

open FStar.Tactics
open MST.Repr
open FStar.Preorder
open FStar.Monotonic.Heap

module W = FStar.Monotonic.Witnessed

(* Total state effect --- the heap is first-order *)

let heap_rel (h1:heap) (h2:heap) =
  forall (a:Type0) (rel:preorder a) (r:mref a rel). h1 `contains` r ==>
    (h2 `contains` r /\ rel (sel h1 r) (sel h2 r))

type heap_predicate = heap -> Type0
let stable (pred:heap -> Type0) = stable pred heap_rel

[@@"opaque_to_smt"]
let witnessed (pred:heap_predicate{stable pred}) : Type0 = W.witnessed heap_rel pred

let contains_pred (#a:Type) (#rel:preorder a) (r:mref a rel) = fun h -> h `contains` r

type ref (a:Type0) = 
  r:(mref a (FStar.Heap.trivial_preorder a)){ is_mm r = false } // no way to produce: witnessed (contains_pred r)

let heap_state : tstate = { 
  t = heap; 
  rel = heap_rel;
  ref = ref;
  
  contains = (fun #a h r -> h `contains` r);
  alloc = (fun #a h0 v -> 
    let (r, h1) = alloc (FStar.Heap.trivial_preorder a) h0 v false in
    (r, h1)
  );
  update = (fun #a h r v -> 
    admit ();
    upd_tot h r v
  );
  select = (fun #a h r -> sel_tot h r);
}


let st_pre   = st_pre_h   heap_state.t
let st_post' = st_post_h' heap_state.t
let st_post  = st_post_h  heap_state.t
let st_wp    = st_mwp_h   heap_state.t

val mheap : (a:Type u#a) -> st_wp a -> Type u#(max 1 a)
let mheap = mst heap_state

val mheap_bind :
  (a : Type u#a) ->
  (b : Type u#b) ->
  (wp_v : st_wp a) ->
  wp_f: (a -> st_wp b) ->
  (v : mheap a wp_v) ->
  (f : (x:a -> mheap b (wp_f x))) ->
  Tot (mheap b (st_bind_wp heap_state.t a b wp_v wp_f))
let mheap_bind a b wp_v wp_f v f = mst_bind #heap_state #a #b #wp_v #wp_f v f

val mheap_return : (a:Type) -> (x:a) -> mheap a (st_return heap_state.t a x)
let mheap_return a = mst_return #heap_state #a


val mheap_subcomp :
  (a : Type u#a) ->
  (wp1 : st_wp a) ->
  (wp2 : st_wp a) ->
  (v : mheap a wp1) ->
  Pure (mheap a wp2) (requires (wp1 ⊑ wp2)) (ensures (fun _ -> True))
let mheap_subcomp a wp1 wp2 = mst_subcomp #heap_state #a #wp1 #wp2

let mheap_if_then_else (a : Type u#a)
  (#wp1 : st_wp a)
  (#wp2 : st_wp a)
  (f : mheap a wp1) (g : mheap a wp2) (b : bool) : Type =
  mheap a (st_if_then_else heap_state.t a b wp1 wp2)

let mheap_require (pre:pure_pre) : mheap (squash pre) (partial_call_wp pre) =
  mst_require pre

let mheap_alloc #a (v:a) : mheap (heap_state.ref a) (alloc_wp v) =
  mst_alloc v

let mheap_read #a (r:heap_state.ref a) : mheap a (read_wp r) =
  mst_read r

let mheap_write #a (r:heap_state.ref a) (v:a) : mheap unit (write_wp r v) =
  mst_write r v

let mheap_witness (pred:heap_predicate{stable pred}) : mheap unit (fun p h -> pred h /\ (witnessed pred ==> p () h)) =
  reveal_opaque (`%witnessed) witnessed;
  mst_witness pred

let mheap_recall (pred:heap_predicate{stable pred}) : mheap unit (fun p h -> witnessed pred /\ (pred h ==> p () h)) =
  mst_recall pred


(** ** END Section 4: Dijkstra Monad **)
