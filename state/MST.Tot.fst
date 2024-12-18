module MST.Tot


open FStar.Tactics
open MST.Repr
open FStar.Preorder
open FStar.Monotonic.Heap

module W = FStar.Monotonic.Witnessed

(* Total state effect --- the heap is first-order *)

let heap_rel (h1:heap) (h2:heap) =
  forall (a:Type0) (rel:preorder a) (r:mref a rel). h1 `contains` r ==>
    (h2 `contains` r /\ rel (sel h1 r) (sel h2 r))

let heap_state : tstate = { t = heap; rel = heap_rel }

let stable (pred:heap_state.t -> Type0) = stable pred heap_state.rel

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
  let lhs = partial_return heap_state (as_requires w) in
  let rhs = (fun (pre:(squash (as_requires w))) -> mheap_return a (f pre)) in
  let m = mheap_bind _ _ _ _ lhs rhs in
  mheap_subcomp _ _ _ m

sub_effect PURE ~> STATEwp = lift_pure_mst

let get () : STATEwp heap (get_wp #heap_state) = 
  STATEwp?.reflect (mst_get ())

let put (h1:heap) : STATEwp unit (put_wp #heap_state h1) = 
  STATEwp?.reflect (mst_put h1)

type heap_predicate = heap -> Type0

[@@"opaque_to_smt"]
let witnessed (pred:heap_predicate{stable pred}) : Type0 = W.witnessed heap_state.rel pred

let witness (pred:heap_predicate) : STATEwp unit (fun p h -> pred h /\ stable pred /\ (witnessed pred ==> p () h)) = 
  STATEwp?.reflect (mst_witness pred)

let recall (pred:heap_predicate{stable pred}) : STATEwp unit (fun p h -> witnessed pred /\ (pred h ==> p () h)) = 
  STATEwp?.reflect (mst_recall pred)

(** *** From here it is mostly a COPY-PASTE from FStar.ST **)
effect ST (a:Type) (pre:st_pre) (post: (h:heap -> Tot (st_post' a (pre h)))) =
  STATEwp a (fun (p:st_post a) (h:heap) -> pre h /\ (forall a h1. post h a h1 ==> p a h1))
effect St (a:Type) = ST a (fun h -> True) (fun h0 r h1 -> True)


let contains_pred (#a:Type) (#rel:preorder a) (r:mref a rel) = fun h -> h `contains` r

type mref (a:Type0) (rel:preorder a) =
  r:Heap.mref a rel{is_mm r = false /\ witnessed (contains_pred r)}

let alloc (#a:Type) (#rel:preorder a) (init:a) :
  ST (mref a rel)
      (fun h -> True)
      (fun h0 r h1 -> fresh r h0 h1 /\ modifies Set.empty h0 h1 /\ sel h1 r == init)
  = let h0 = get () in
    let r, h1 = alloc rel h0 init false in
    put h1;
    witness (contains_pred r);
    r

let read (#a:Type) (#rel:preorder a) (r:mref a rel) :STATEwp a (fun p h -> p (sel h r) h)
  = let h0 = get () in
    recall (contains_pred r);
    Heap.lemma_sel_equals_sel_tot_for_contained_refs h0 r;
    sel_tot h0 r

let write (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
  : ST unit
    (fun h -> rel (sel h r) v)
    (fun h0 x h1 -> rel (sel h0 r) v /\ h0 `contains` r /\
                 modifies (Set.singleton (addr_of r)) h0 h1 /\ equal_dom h0 h1 /\
                 sel h1 r == v)
  = let h0 = get () in
    recall (contains_pred r);
    let h1 = upd_tot h0 r v in
    Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ();
    Heap.lemma_upd_equals_upd_tot_for_contained_refs h0 r v;
    put h1

let op_Bang (#a:Type) (#rel:preorder a) (r:mref a rel)
  : STATEwp a (fun p h -> p (sel h r) h)
= read #a #rel r

let op_Colon_Equals (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
  : ST unit
    (fun h -> rel (sel h r) v)
    (fun h0 x h1 -> rel (sel h0 r) v /\ h0 `contains` r /\
                 modifies (Set.singleton (addr_of r)) h0 h1 /\ equal_dom h0 h1 /\
                 sel h1 r == v)
= write #a #rel r v

type ref (a:Type0) = mref a (FStar.Heap.trivial_preorder a)
