module MST.Soundness

open FStar.Preorder
open FStar.Monotonic.Heap
open SharedRefs { lemma_eq_addrs_eq_all, lemma_eq_ref_types_eq_value_types }

let heap_rel (h1:heap) (h2:heap) =
  forall (a:Type0) (rel:preorder a) (r:mref a rel). h1 `contains` r ==>
    (h2 `contains` r /\ rel (sel h1 r) (sel h2 r))

let stable (pred: heap -> Type0) = stable pred heap_rel

type heap_predicate_stable =
  pred:(heap -> Type0){forall h0 h1. pred h0 /\ h0 `heap_rel` h1 ==> pred h1}

let state_wp a = (a -> heap -> Type0) -> (heap -> Type0)

let state_wp_return (x:'a) : state_wp 'a = fun p h0 -> p x h0
let state_wp_bind (m:state_wp 'a) (k:'a -> state_wp 'b) : state_wp 'b =
  fun p h0 -> m (fun r h1 -> k r p h1) h0

let state_wp_stronger (wp1 wp2:state_wp 'a) : Type0 =
  forall p h0. wp2 p h0 ==> wp1 p h0

noeq
type mst_repr (a:Type) =
| Return : a -> mst_repr a 
| Read : #b:Type0 -> #rel: preorder b -> r: mref b rel -> cont:(b -> mst_repr a) -> mst_repr a
| Write : #b:Type0 -> #rel: preorder b -> r: mref b rel -> v:b -> cont:mst_repr a -> mst_repr a
| Alloc : #b:Type0 -> #rel: preorder b -> init: b -> cont:(mref b rel -> mst_repr a) -> mst_repr a
| Witness : pred:heap_predicate_stable -> (unit -> mst_repr a) -> mst_repr a
| Recall : pred:heap_predicate_stable -> (unit -> mst_repr a) -> mst_repr a

unfold
let read_wp (#a:Type) (#rel:preorder a) (r:mref a rel) : state_wp a =
  fun p h0 -> h0 `contains` r /\ p (sel h0 r) h0

let write_post #a #rel (r:mref a rel) (v:a) h0 () h1 : Type0 =
  h0 `contains` r /\
  h1 == upd h0 r v /\
  rel (sel h0 r) v /\
  modifies (Set.singleton (addr_of r)) h0 h1 /\ equal_dom h0 h1 /\
  sel h1 r == v

unfold
let write_wp (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
  : state_wp unit =
  fun p h0 ->
    h0 `contains` r /\ rel (sel h0 r) v /\
    (h0 `heap_rel` (upd h0 r v) /\ write_post r v h0 () (upd h0 r v) ==> p () (upd h0 r v))

let alloc_post #a #rel init h0 (r:mref a rel) h1 : Type0 =
  fresh r h0 h1 /\ modifies Set.empty h0 h1 /\ sel h1 r == init /\
  h1 == upd h0 r init /\ is_mm r == false /\
  addr_of r == next_addr h0 /\
  next_addr h1 > next_addr h0

unfold
let alloc_wp (#a:Type) (#rel:preorder a) (init:a) : state_wp (mref a rel) =
  fun p h0 ->
    (forall r. h0 `heap_rel` (upd h0 r init) /\ alloc_post init h0 r (upd h0 r init) ==> p r (upd h0 r init))

unfold
let witness_wp (witnessed:(heap -> Type0) -> Type0) (pred:(heap -> Type0)) : state_wp unit =
  fun p h -> pred h /\ stable pred /\ (witnessed pred ==> p () h)

unfold
let recall_wp (witnessed:(heap -> Type0) -> Type0) (pred:(heap -> Type0)) : state_wp unit =
  fun p h -> witnessed pred /\ (pred h ==> p () h)

let rec theta (witnessed:(heap -> Type0) -> Type0) (m:mst_repr 'a) : state_wp 'a =
  match m with
  | Return x -> state_wp_return x
  | Read r k ->
      st_bind_wp heap _ _ (read_wp r) (fun r -> theta witnessed (k r))
  | Write r v k ->
      st_bind_wp heap _ _ (write_wp r v) (fun _ -> theta witnessed k)
  | Alloc init k ->
      st_bind_wp heap _ _ (alloc_wp init) (fun r -> theta witnessed (k r))
  | Witness pred k -> state_wp_bind (witness_wp witnessed pred) (fun r -> theta witnessed (k r))
  | Recall pred k -> state_wp_bind (recall_wp witnessed pred) (fun r -> theta witnessed (k r))

module S = FStar.TSet

let rec witnessed_before #a (preds:S.set heap_predicate_stable) (m:mst_repr a) : Tot Type0 (decreases m) =
  match m with
  | Return _ -> True
  | Read r k -> forall v . preds `witnessed_before` (k v)
  | Write r v k -> preds `witnessed_before` k
  | Alloc init k -> forall r . preds `witnessed_before` (k r)
  | Witness pred k -> (S.union preds (S.singleton pred)) `witnessed_before` (k ())
  | Recall pred k -> pred `S.mem` preds /\ preds `witnessed_before` (k ())

type heap_w_preds =
  hp:(heap * S.set heap_predicate_stable){forall (pred:heap_predicate_stable). pred `S.mem` (snd hp) ==> pred (fst hp)}
  
val witnessed_trivial : (heap -> Type0) -> Type0
let witnessed_trivial pred = True // trivial instance of witnessed tokens

let rec run_mst_with_preds #a 
  (wp:state_wp a) 
  (m:mst_repr a{theta witnessed_trivial m `state_wp_stronger` wp}) 
  (post:(a -> heap -> Type0)) 
  (h0:heap_w_preds{wp post (fst h0) /\ (snd h0) `witnessed_before` m}) 
: Tot (r:(a * heap_w_preds){post (fst r) (fst (snd r))}) 
=
  match m with
  | Return v -> (v, h0)
  | Read #_ #b #rel r k -> 
      lemma_sel_equals_sel_tot_for_contained_refs (fst h0) r;
      run_mst_with_preds (theta witnessed_trivial (k (sel_tot (fst h0) r))) (k (sel_tot (fst h0) r)) post h0
  | Write #_ #b #rel r v k -> 
      lemma_upd_equals_upd_tot_for_contained_refs (fst h0) r v;
      introduce forall (a':Type0) (rel':preorder a') (r':mref a' rel'). fst h0 `contains` r' ==> 
        (upd (fst h0) r v `contains` r' /\ rel' (sel (fst h0) r') (sel (upd (fst h0) r v) r')) with
      begin
        introduce fst h0 `contains` r' /\ addr_of r = addr_of r' ==> 
          (upd (fst h0) r v `contains` r' /\ rel' (sel (fst h0) r') (sel (upd (fst h0) r v) r')) with _.
        begin
          lemma_eq_addrs_eq_all r r' (fst h0)
        end
      end;
      run_mst_with_preds (theta witnessed_trivial k) k post (upd_tot (fst h0) r v, snd h0)
  | Alloc #_ #b #rel init k -> 
      let (r,h) = alloc rel (fst h0) init false in
      lemma_upd_equals_upd_tot_for_contained_refs h r init;
      assert (fst h0 `heap_rel` upd (fst h0) r init);
      lemma_alloc rel (fst h0) init false;
      lemma_next_addr_alloc rel (fst h0) init false;
      run_mst_with_preds (theta witnessed_trivial (k r)) (k r) post (h,snd h0)
  | Witness pred k -> 
      let hp = S.union (snd h0) (S.singleton pred) in
      run_mst_with_preds (theta witnessed_trivial (k ())) (k ()) post (fst h0, hp)
  | Recall pred k -> 
      run_mst_with_preds (theta witnessed_trivial (k ())) (k ()) post h0

let run_mst #a 
  (wp:state_wp a) 
  (m:mst_repr a{theta witnessed_trivial m `state_wp_stronger` wp /\ S.empty `witnessed_before` m}) 
  (post:(a -> heap -> Type0)) 
  (h0:heap{wp post h0}) 
: Tot (vh:(a * heap){post (fst vh) (snd vh)}) 
=
  let (v, h1) = run_mst_with_preds wp m post (h0, S.empty) in
  (v, fst h1)
  
let soundness_with_preds #a (m:mst_repr a) (wp:state_wp a) (preds:S.set heap_predicate_stable) 
: Lemma
    (requires ((forall witnessed. theta witnessed m `state_wp_stronger` wp) /\ preds `witnessed_before` m))
    (ensures  (forall post h0. wp post h0 /\ (forall (pred:heap_predicate_stable). pred `S.mem` preds ==> pred h0) ==> 
                            (let (r,h1p) = run_mst_with_preds wp m post (h0, preds) in post r (fst h1p)))) 
=
  () 

let soundness_whole_program #a (m:mst_repr a) (wp:state_wp a) 
: Lemma 
    (requires ((forall witnessed. theta witnessed m `state_wp_stronger` wp) /\ S.empty `witnessed_before` m)) 
    (ensures  (forall post h0. wp post h0 ==> (let (r,h1) = run_mst wp m post h0 in post r h1))) 
=
  ()
