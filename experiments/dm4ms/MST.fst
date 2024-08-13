module MST

open WMonad


open FStar.Tactics
module W = FStar.Monotonic.Witnessed

noeq type mheap = {
  t: Type0;
  rel: FStar.Preorder.preorder t;
}

let stable (#heap) (pred:heap.t -> Type0) =
  forall h1 h2. (pred h1 /\ h1 `heap.rel` h2) ==> pred h2

noeq
type free (heap:mheap) (a:Type u#a) : Type u#(max 1 a) =
| Get : cont:(heap.t -> free heap a) -> free heap a
| Put : heap.t -> cont:(unit -> free heap a) -> free heap a
| Witness : p:(heap.t -> Type0) -> cont:(unit -> free heap a) -> free heap a
| Recall : p:(heap.t -> Type0) -> cont:(unit -> free heap a) -> free heap a

| PartialCall : (pre:pure_pre) -> cont:((squash pre) -> free u#a heap a) -> free heap a
| Return : a -> free heap a

let free_return (heap:mheap) (a:Type) (x:a) : free heap a =
  Return x

let rec free_bind
  (heap:mheap)
  (a:Type u#a)
  (b:Type u#b)
  (l : free heap a)
  (k : a -> free heap b) :
  free heap b =
  match l with
  | Return x -> k x
  | Get cont -> Get (fun x -> free_bind heap a b (cont x) k)
  | Put h cont -> Put h (fun _ -> free_bind heap a b (cont ()) k)
  | Witness pred cont -> Witness pred (fun _ -> free_bind heap a b (cont ()) k)
  | Recall pred cont -> Recall pred (fun _ -> free_bind heap a b (cont ()) k)
  | PartialCall pre fnc ->
      PartialCall pre (fun _ ->
        free_bind heap a b (fnc ()) k)

let partial_call_wp (heap:Type0) (pre:pure_pre) : st_wp_h heap (squash pre) = 
  fun p h0 -> pre /\ p () h0

val theta : #a:Type u#a -> #heap:mheap -> free heap a -> st_wp_h heap.t a
let rec theta #a #heap m =
  match m with
  | Return x -> st_return heap.t _ x
  | PartialCall pre k ->
      st_bind_wp heap.t _ _ (partial_call_wp heap.t pre) (fun r -> theta (k r))
  | Get k ->
      st_bind_wp heap.t _ _ (fun p h -> p h h) (fun r -> theta (k r))
  | Put h1 k ->
      st_bind_wp heap.t _ _ (fun p h0 -> h0 `heap.rel` h1 /\ p () h1) (fun r -> theta (k r))
  | Witness pred k ->
      st_bind_wp heap.t _ _ (fun p h -> pred h /\ stable pred /\ (W.witnessed heap.rel pred ==> p () h)) (fun r -> theta (k r))
  | Recall pred k ->
      st_bind_wp heap.t _ _ (fun p h -> W.witnessed heap.rel pred /\ (pred h ==> p () h)) (fun r -> theta (k r))

let mst (heap:mheap) (a:Type) (wp:st_wp_h heap.t a)=
  m:(free heap a){theta m ⊑ wp}

let mst_return heap (a:Type) (x:a) : mst heap a (st_return heap.t _ x) =
  free_return heap a x

let mst_bind
  (#heap:mheap)
  (#a : Type u#a)
  (#b : Type u#b)
  (#wp_v : st_wp_h heap.t a)
  (#wp_f: a -> st_wp_h heap.t b)
  (v : mst heap a wp_v)
  (f : (x:a -> mst heap b (wp_f x))) :
  Tot (mst heap b (st_bind_wp heap.t a b wp_v wp_f)) =
  admit (); (* TODO: prove monad morphism *)
  free_bind heap a b v f

let mst_subcomp
  (#heap:mheap)
  (#a : Type u#a)
  (#wp1 : st_wp_h heap.t a)
  (#wp2 : st_wp_h heap.t a)
  (v : mst heap a wp1)
  :
  Pure (mst heap a wp2) (requires (wp1 ⊑ wp2)) (ensures (fun _ -> True)) =
  v

let partial_return heap (pre:pure_pre) : mst heap (squash pre) (partial_call_wp heap.t pre) =
  PartialCall pre (Return)

let get #heap () : mst heap heap.t (fun p h0 -> p h0 h0) =
  Get Return

let put #heap (h1:heap.t) : mst heap unit (fun p h0 -> (h0 `heap.rel` h1) /\ p () h1) =
  Put h1 Return

let witness #heap (pred:heap.t -> Type0) : mst heap unit (fun p h -> pred h /\ stable pred /\ (W.witnessed heap.rel pred ==> p () h)) =
  Witness pred Return

let recall #heap (pred:heap.t -> Type0) : mst heap unit (fun p h -> W.witnessed heap.rel pred /\ (pred h ==> p () h)) =
  Recall pred Return

let nat_heap = {
  t = nat;
  rel = (fun x y -> x <= y == true);
}

(* TODO: why is this failing?
let test () : mst nat_heap unit (fun p h0 -> forall h1. p () h1) =
  mst_subcomp #_ #_ #_ #_ (
  mst_bind #nat_heap #nat #unit #_ #_ (get ())
    (fun h0 -> 
      let h1 = h0 + 1 in 
      put h1))
*)
// put(get() + 1); witness (fun s -> s > 0); let f () = recall (fun s -> s > 0); 1 / get() in f () 0
