module MST.Tot

open MST
open FStar.Preorder
open FStar.Monotonic.Heap

module W = FStar.Monotonic.Witnessed
  
let st_pre           = st_pre_h heap
let st_post' (a:Type) (pre:Type) = st_post_h' heap a pre
let st_post  (a:Type) = st_post_h heap a
let st_wp (a:Type)   = st_wp_h heap a

(* Total state effect --- this means that the heap is first-order *)

let heap_rel (h1:heap) (h2:heap) =
  forall (a:Type0) (rel:preorder a) (r:mref a rel). h1 `contains` r ==>
    (h2 `contains` r /\ rel (sel h1 r) (sel h2 r))

let heap_state : tstate = { t = heap; rel = heap_rel }

let stable (pred:heap_state.t -> Type0) = stable pred heap_state.rel

let _mst a (wp:st_wp a) = mst heap_state a wp
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

let get () : STATEwp heap get_wp = 
  STATEwp?.reflect (mst_get ())

let put (h1:heap) : STATEwp unit (put_wp h1) = 
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


let contains_pred (#a:Type) (#rel:FStar.Preorder.preorder a) (r:mref a rel) = fun h -> h `contains` r

type mref (a:Type0) (rel:FStar.Preorder.preorder a) =
  r:Heap.mref a rel{is_mm r = false /\ witnessed (contains_pred r)}

let alloc (#a:Type) (#rel:FStar.Preorder.preorder a) (init:a)
  :ST (mref a rel)
      (fun h -> True)
      (fun h0 r h1 -> fresh r h0 h1 /\ modifies Set.empty h0 h1 /\ sel h1 r == init)
  = let h0 = get () in
    let r, h1 = alloc rel h0 init false in
    put h1;
    witness (contains_pred r);
    r

let read (#a:Type) (#rel:FStar.Preorder.preorder a) (r:mref a rel) :STATEwp a (fun p h -> p (sel h r) h)
  = let h0 = get () in
    recall (contains_pred r);
    Heap.lemma_sel_equals_sel_tot_for_contained_refs h0 r;
    sel_tot h0 r

let write (#a:Type) (#rel:FStar.Preorder.preorder a) (r:mref a rel) (v:a)
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

let op_Bang (#a:Type) (#rel:FStar.Preorder.preorder a) (r:mref a rel)
  : STATEwp a (fun p h -> p (sel h r) h)
= read #a #rel r

let op_Colon_Equals (#a:Type) (#rel:FStar.Preorder.preorder a) (r:mref a rel) (v:a)
  : ST unit
    (fun h -> rel (sel h r) v)
    (fun h0 x h1 -> rel (sel h0 r) v /\ h0 `contains` r /\
                 modifies (Set.singleton (addr_of r)) h0 h1 /\ equal_dom h0 h1 /\
                 sel h1 r == v)
= write #a #rel r v

type ref (a:Type0) = mref a (FStar.Heap.trivial_preorder a)
