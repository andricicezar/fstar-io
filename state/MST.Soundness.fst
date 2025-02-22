module MST.Soundness

open FStar.Preorder
open FStar.Monotonic.Heap

(** CA&DA: This can be proved trivially in FStar.Monotonic.Heap.fst **)
assume
val lemma_eq_addrs_eq_all #a #rela #b #relb (r1:mref a rela) (r2:mref b relb) (h:heap) : Lemma
  (requires (h `contains` r1 /\ h `contains` r2 /\ addr_of r1 == addr_of r2))
  (ensures (a == b /\ rela == relb /\ is_mm r1 == is_mm r2 /\ sel h r1 == sel h r2))
(** DA: In my FStar.Monotonic.Heap.fst **)
(*
let lemma_eq_addrs_eq_all _ _ _ = ()
*)

(** DA: This can be proved trivially in FStar.Monotonic.Heap.fst **)
assume
val lemma_eq_ref_types_eq_value_types #a #b (#rela:preorder a) (#relb : preorder b) (r:mref a rela)
  : Lemma (requires (mref a rela == mref b relb))
          (ensures  (a == b))
(** DA: In my FStar.Monotonic.Heap.fst **)
(*
let lemma_eq_ref_types_eq_value_types _ = ()
*)

let heap_rel (h1:heap) (h2:heap) =
  forall (a:Type0) (rel:preorder a) (r:mref a rel). h1 `contains` r ==>
    (h2 `contains` r /\ rel (sel h1 r) (sel h2 r))

let stable (pred: heap -> Type0) = stable pred heap_rel

type stable_pred =
  pred:(heap -> Type0){forall h0 h1. pred h0 /\ h0 `heap_rel` h1 ==> pred h1}

let state_wp a = (a -> heap -> Type0) -> (heap -> Type0)

let state_wp_return (x:'a) : state_wp 'a = fun p s0 -> p x s0
let state_wp_bind (m:state_wp 'a) (k:'a -> state_wp 'b) : state_wp 'b =
  fun p s0 -> m (fun r s1 -> k r p s1) s0

let state_wp_stronger (wp1 wp2:state_wp 'a) : Type0 =
  forall p s0. wp2 p s0 ==> wp1 p s0

noeq
type mst_repr (a:Type) =
| Return : a -> mst_repr a 
| Read : #b:Type0 -> #rel: preorder b -> r: mref b rel -> cont:(b -> mst_repr a) -> mst_repr a
| Write : #b:Type0 -> #rel: preorder b -> r: mref b rel -> v:b -> cont:mst_repr a -> mst_repr a
| Alloc : #b:Type0 -> #rel: preorder b -> init: b -> cont:(mref b rel -> mst_repr a) -> mst_repr a
| Witness : pred:stable_pred -> (unit -> mst_repr a) -> mst_repr a
| Recall : pred:stable_pred -> (unit -> mst_repr a) -> mst_repr a

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

let rec witnessed_before #a (preds:S.set stable_pred) (m:mst_repr a) : Tot Type0 (decreases m) =
  match m with
  | Return _ -> True
  | Read r k -> forall v . preds `witnessed_before` (k v)
  | Write r v k -> preds `witnessed_before` k
  | Alloc init k -> forall r . preds `witnessed_before` (k r)
  | Witness pred k -> (S.union preds (S.singleton pred)) `witnessed_before` (k ())
  | Recall pred k -> pred `S.mem` preds /\ preds `witnessed_before` (k ())

type heap_w_preds =
  sp:(heap * S.set stable_pred){forall (pred:stable_pred). pred `S.mem` (snd sp) ==> pred (fst sp)}
  
val witnessed_trivial : (heap -> Type0) -> Type0
let witnessed_trivial pred = True // trivial instance of witnessed tokens

let rec run_mst_with_preds #a 
  (m:mst_repr a) 
  (wp:(state_wp a){theta witnessed_trivial m `state_wp_stronger` wp}) 
  (post:(a -> heap -> Type0)) 
  (s0:heap_w_preds{wp post (fst s0) /\ (snd s0) `witnessed_before` m}) 
: Tot (r:(a * heap_w_preds){post (fst r) (fst (snd r))}) 
=
  match m with
  | Return x -> (x, s0)
  | Read #_ #b #rel r k -> 
      lemma_sel_equals_sel_tot_for_contained_refs (fst s0) r;
      run_mst_with_preds (k (sel_tot (fst s0) r)) (theta witnessed_trivial (k (sel_tot (fst s0) r))) post s0
  | Write #_ #b #rel r v k -> 
      lemma_upd_equals_upd_tot_for_contained_refs (fst s0) r v;
      introduce forall (a':Type0) (rel':preorder a') (r':mref a' rel'). fst s0 `contains` r' ==> 
        (upd (fst s0) r v `contains` r' /\ rel' (sel (fst s0) r') (sel (upd (fst s0) r v) r')) with
      begin
        introduce fst s0 `contains` r' /\ addr_of r = addr_of r' ==> 
          (upd (fst s0) r v `contains` r' /\ rel' (sel (fst s0) r') (sel (upd (fst s0) r v) r')) with _.
        begin
          lemma_eq_addrs_eq_all r r' (fst s0)
        end
      end;
      run_mst_with_preds k (theta witnessed_trivial k) post (upd_tot (fst s0) r v, snd s0)
  | Alloc #_ #b #rel init k -> 
      let (r,h) = alloc rel (fst s0) init false in
      lemma_upd_equals_upd_tot_for_contained_refs h r init;
      assert (fst s0 `heap_rel` upd (fst s0) r init);
      lemma_alloc rel (fst s0) init false;
      lemma_next_addr_alloc rel (fst s0) init false;
      run_mst_with_preds (k r) (theta witnessed_trivial (k r)) post (h,snd s0)
  | Witness pred k -> 
    let lp = S.union (snd s0) (S.singleton pred) in
    run_mst_with_preds (k ()) (theta witnessed_trivial (k ())) post (fst s0, lp)
  | Recall pred k -> 
    run_mst_with_preds (k ()) (theta witnessed_trivial (k ())) post s0

let run_mst #a 
  (m:mst_repr a{S.empty `witnessed_before` m}) 
  (wp:(state_wp a){theta witnessed_trivial m `state_wp_stronger` wp}) 
  (post:(a -> heap -> Type0)) 
  (s0:heap{wp post s0}) 
: Tot (r:(a * heap){post (fst r) (snd r)}) 
=
  let (r, s1p) = run_mst_with_preds m wp post (s0, S.empty) in
  (r, fst s1p)
  
let soundness_with_preds #a (m:mst_repr a) (wp:state_wp a) (preds:S.set stable_pred) 
: Lemma
    (requires ((forall witnessed. theta witnessed m `state_wp_stronger` wp) /\ preds `witnessed_before` m))
    (ensures  (forall post s0. wp post s0 /\ (forall (pred:stable_pred). pred `S.mem` preds ==> pred s0) ==> 
                            (let (r,s1p) = run_mst_with_preds m wp post (s0, preds) in post r (fst s1p)))) 
=
  () 

let soundness_whole_program #a (m:mst_repr a) (wp:state_wp a) 
: Lemma 
    (requires ((forall witnessed. theta witnessed m `state_wp_stronger` wp) /\ S.empty `witnessed_before` m)) 
    (ensures  (forall post s0. wp post s0 ==> (let (r,s1) = run_mst m wp post s0 in post r s1))) 
=
  ()
