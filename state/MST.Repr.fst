module MST.Repr


open FStar.Tactics
open FStar.Calc
open FStar.Preorder
open FStar.Monotonic.Heap

module W = FStar.Monotonic.Witnessed

(**
  File structured as follows:
  0. Prerequisties about heap and references
  1. Spec monad
  2. Free monad
  3. Define theta and proofs that is a lax morphism
  4. Define Dijkstra Monad
**)

(** ** START Section 0: heaps and references **)

type mref (a:Type0) (rel:preorder a) =
  r:Heap.mref a rel {is_mm r = false}

let heap_rel (h1:heap) (h2:heap) =
  forall (a:Type0) (rel:preorder a) (r:mref a rel). h1 `contains` r ==>
    (h2 `contains` r /\ rel (sel h1 r) (sel h2 r))

let stable (pred: heap -> Type0) = stable pred heap_rel

type heap_predicate = heap -> Type0
type heap_predicate_stable = pred:heap_predicate {stable pred}

[@@"opaque_to_smt"]
let witnessed (pred:heap_predicate_stable) : Type0 = W.witnessed heap_rel pred

(** ** END Section 0: heaps and references **)

(** ** START Section 1: specification monad **)

(** Most of it defined in FStar.Pervasives, here just adding monotonicity *)
unfold
let st_post_ord (#heap:Type) (p1 p2:st_post_h heap 'a) =
  forall r h. p1 r h ==> p2 r h

unfold
let st_wp_monotonic (heap:Type) (wp:st_wp_h heap 'a) =
  forall p1 p2. (p1 `st_post_ord` p2) ==> (forall h. wp p1 h ==> wp p2 h)

let st_mwp_h (heap a: Type) = wp:(st_wp_h heap a){st_wp_monotonic heap wp}

unfold
let (⊑) #heap #a wp1 wp2 = st_stronger heap a wp2 wp1

(** ** END Section 1: specification monad **)



(** ** START Section 2: free monad **)

noeq
type free (a:Type u#a) : Type u#(max 1 a) =
| Read : #b:Type0 -> #rel: preorder b -> r: mref b rel -> cont:(b -> free a) -> free a
| Write : #b:Type0 -> #rel: preorder b -> r: mref b rel -> v:b -> cont:free a -> free a
| Alloc : #b:Type0 -> #rel: preorder b -> init: b -> cont:(mref b rel -> free a) -> free a
| Witness : p:heap_predicate_stable -> cont:(unit -> free a) -> free a
| Recall : p:heap_predicate_stable -> cont:(unit -> free a) -> free a

| PartialCall : (pre:pure_pre) -> cont:((squash pre) -> free a) -> free a
| Return : a -> free a

let free_return (a:Type u#a) (x:a) : free a =
  Return x

let rec free_bind
  (#a:Type u#a)
  (#b:Type u#b)
  (l : free a)
  (k : a -> free b) :
  free b =
  match l with
  | Return x -> k x
  | Read r cont -> Read r (fun x -> free_bind (cont x) k)
  | Write r v cont -> Write r v (free_bind cont k)
  | Alloc init cont -> Alloc init (fun x -> free_bind (cont x) k)
  | Witness pred cont -> Witness pred (fun _ -> free_bind (cont ()) k)
  | Recall pred cont -> Recall pred (fun _ -> free_bind (cont ()) k)
  | PartialCall pre fnc -> PartialCall pre (fun _ -> free_bind (fnc ()) k)

(** ** END Section 2: free monad **)

(** ** START Section 3: theta **)

unfold
let partial_call_wp (pre:pure_pre) : st_mwp_h heap (squash pre) =
  let wp' : st_wp_h heap (squash pre) = fun p h0 -> pre /\ p () h0 in
  assert (st_wp_monotonic heap wp');
  wp'

unfold
let read_wp (#a:Type) (#rel:preorder a) (r:mref a rel) : st_mwp_h heap a =
  fun p h0 -> h0 `contains` r /\ p (sel h0 r) h0

let write_post #a #rel (r:mref a rel) (v:a) h0 () h1 : Type0 =
  h0 `contains` r /\
  h1 == upd_tot h0 r v /\
  rel (sel h0 r) v /\
  modifies (Set.singleton (addr_of r)) h0 h1 /\ equal_dom h0 h1 /\
  sel h1 r == v

unfold
let write_wp (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
  : st_mwp_h heap unit =
  fun p h0 ->
    h0 `contains` r /\ rel (sel h0 r) v /\
    (forall a h1. h0 `heap_rel` h1 /\ write_post r v h0 a h1 ==> p a h1)

let alloc_post #a #rel init h0 (r:mref a rel) h1 : Type0 =
  fresh r h0 h1 /\ modifies Set.empty h0 h1 /\ sel h1 r == init /\
  h1 == upd h0 r init /\ is_mm r == false /\
  addr_of r == next_addr h0 /\
  next_addr h1 > next_addr h0

unfold
let alloc_wp (#a:Type) (#rel:preorder a) (init:a) : st_mwp_h heap (mref a rel) =
  fun p h0 ->
    (forall a h1. h0 `heap_rel` h1 /\ alloc_post init h0 a h1 ==> p a h1)

unfold
let witness_wp (pred:heap_predicate) : st_mwp_h heap unit =
  fun p h -> pred h /\ stable pred /\ (witnessed pred ==> p () h)

unfold
let recall_wp (pred:heap_predicate_stable) : st_mwp_h heap unit =
  fun p h -> witnessed pred /\ (pred h ==> p () h)

val theta : #a:Type u#a -> free a -> st_mwp_h heap a
let rec theta #a m =
  match m with
  | Return x -> st_return heap _ x
  | PartialCall pre k ->
      st_bind_wp heap _ _ (partial_call_wp pre) (fun r -> theta (k r))
  | Read r k ->
      st_bind_wp heap _ _ (read_wp r) (fun r -> theta (k r))
  | Write r v k ->
      st_bind_wp heap _ _ (write_wp r v) (fun _ -> theta k)
  | Alloc init k ->
      st_bind_wp heap _ _ (alloc_wp init) (fun r -> theta (k r))
  | Witness pred k ->
      st_bind_wp heap _ _ (witness_wp pred) (fun r -> theta (k r))
  | Recall pred k ->
      st_bind_wp heap _ _ (recall_wp pred) (fun r -> theta (k r))

let lemma_theta_is_monad_morphism_ret (v:'a) :
  Lemma (theta (free_return 'a v) == st_return heap 'a v) by (compute ()) = ()


#push-options "--split_queries always"
let rec lemma_theta_is_lax_morphism_bind
  (#a:Type u#a) (#b:Type u#b) (m:free a) (f:a -> free b) :
  Lemma
    (theta (free_bind m f) ⊑ st_bind_wp heap a b (theta m) (fun x -> theta (f x))) =
  match m with
  | Return x -> ()
  | Read r k ->
    begin
      calc (⊑) {
        theta (free_bind (Read r k) f) ;
        ⊑ {}
        st_bind_wp heap _ _ (read_wp r) (fun r -> theta (free_bind (k r) f)) ;
        ⊑ {
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun x -> st_bind_wp heap _ _ (theta (k x)) (fun x -> theta (f x)) in
          introduce forall x. lhs x ⊑ rhs x with begin
            lemma_theta_is_lax_morphism_bind (k x) f
          end
        }
        st_bind_wp heap _ _ (read_wp r) (fun x -> st_bind_wp heap _ _ (theta (k x)) (fun x -> theta (f x))) ;
        ⊑ {}
        st_bind_wp heap a b (theta (Read r k)) (fun x -> theta (f x)) ;
      }
    end
  | Write r v k ->
    begin
      calc (⊑) {
        theta (free_bind (Write r v k) f) ;
        ⊑ {}
        st_bind_wp heap _ _ (write_wp r v) (fun _ -> theta (free_bind k f)) ;
        ⊑ { lemma_theta_is_lax_morphism_bind k f }
        st_bind_wp heap _ _ (write_wp r v) (fun _ -> st_bind_wp heap _ _ (theta k) (fun x -> theta (f x))) ;
        ⊑ {}
        st_bind_wp heap a b (theta (Write r v k)) (fun x -> theta (f x)) ;
      }
    end
  | Alloc init k ->
    begin
      calc (⊑) {
        theta (free_bind (Alloc init k) f) ;
        ⊑ {}
        st_bind_wp heap _ _ (alloc_wp init) (fun r -> theta (free_bind (k r) f)) ;
        ⊑ {
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun x -> st_bind_wp heap _ _ (theta (k x)) (fun x -> theta (f x)) in
          introduce forall x. lhs x ⊑ rhs x with begin
            lemma_theta_is_lax_morphism_bind (k x) f
          end
        }
        st_bind_wp heap _ _ (alloc_wp init) (fun x -> st_bind_wp heap _ _ (theta (k x)) (fun x -> theta (f x))) ;
        ⊑ {}
        st_bind_wp heap a b (theta (Alloc init k)) (fun x -> theta (f x)) ;
      }
    end
  | Witness pred k -> begin
    calc (⊑) {
      theta (free_bind (Witness pred k) f);
      ⊑ {}
      st_bind_wp heap unit b (witness_wp pred) (fun r -> theta (free_bind (k r) f));
      ⊑ {
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp heap a b (theta (k r)) (fun x -> theta (f x)) in
          introduce forall r. lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b (k r) f
          end
          }
      st_bind_wp heap unit b (witness_wp pred) (fun r -> st_bind_wp heap a b (theta (k r)) (fun x -> theta (f x)));
      ⊑ {}
      st_bind_wp heap a b (theta (Witness pred k)) (fun x -> theta (f x));
    }
  end
  | Recall pred k -> begin
    calc (⊑) {
      theta (free_bind (Recall pred k) f);
      ⊑ {}
      st_bind_wp heap unit b (recall_wp pred) (fun r -> theta (free_bind (k r) f));
      ⊑ {
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp heap a b (theta (k r)) (fun x -> theta (f x)) in
          introduce forall r. lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b (k r) f
          end
          }
      st_bind_wp heap unit b (recall_wp pred) (fun r -> st_bind_wp heap a b (theta (k r)) (fun x -> theta (f x)));
      ⊑ {}
      st_bind_wp heap a b (theta (Recall pred k)) (fun x -> theta (f x));
    }
  end
  | PartialCall pre k -> begin
    calc (⊑) {
      theta (free_bind (PartialCall pre k) f);
      ⊑ {}
      st_bind_wp heap (squash pre) b (partial_call_wp pre) (fun r -> theta (free_bind (k r) f));
      ⊑ {
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun r -> st_bind_wp heap a b (theta (k r)) (fun x -> theta (f x)) in
          introduce forall (r:squash pre). lhs r ⊑ rhs r with begin
            lemma_theta_is_lax_morphism_bind #a #b (k r) f
          end
          }
      st_bind_wp heap (squash pre) b (partial_call_wp pre) (fun r -> st_bind_wp heap a b (theta (k r)) (fun x -> theta (f x)));
      ⊑ {}
      st_bind_wp heap a b (theta (PartialCall pre k)) (fun x -> theta (f x));
    }
  end
#pop-options

(** ** END Section 3: theta **)

(** ** START Section 4: Dijkstra Monad **)

let mst (a:Type) (wp:st_mwp_h heap a)=
  m:(free a){theta m ⊑ wp}

let mst_return (#a:Type) (x:a) : mst a (st_return heap _ x) =
  free_return a x

let mst_bind
  (#a : Type u#a)
  (#b : Type u#b)
  (#wp_v : st_mwp_h heap a)
  (#wp_f: a -> st_mwp_h heap b)
  (v : mst a wp_v)
  (f : (x:a -> mst b (wp_f x))) :
  Tot (mst b (st_bind_wp heap a b wp_v wp_f)) =
  lemma_theta_is_lax_morphism_bind v f;
  free_bind v f

let mst_subcomp
  (#a : Type u#a)
  (#wp1 : st_mwp_h heap a)
  (#wp2 : st_mwp_h heap a)
  (v : mst a wp1)
  :
  Pure (mst a wp2) (requires (wp1 ⊑ wp2)) (ensures (fun _ -> True)) =
  v

let partial_return (pre:pure_pre) : mst (squash pre) (partial_call_wp pre) =
  PartialCall pre (Return)

let mst_read (#a:Type) (#rel:preorder a) (r:mref a rel) : mst a (read_wp r) =
  Read r Return

let mst_write (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a) : mst unit (write_wp r v) =
  Write r v (Return ())

let mst_alloc (#a:Type) (#rel:preorder a) (init:a) : mst (mref a rel) (alloc_wp init) =
  Alloc init Return

let mst_witness (pred:heap_predicate_stable) : mst unit (witness_wp pred) =
  Witness pred Return

let mst_recall (pred:heap_predicate_stable) : mst unit (recall_wp pred) =
  Recall pred Return

(** ** END Section 4: Dijkstra Monad **)
