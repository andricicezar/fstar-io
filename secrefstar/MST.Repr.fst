module MST.Repr


open FStar.Tactics
open FStar.Calc
open FStar.Preorder
open FStar.Monotonic.Heap
open FStar.Ghost

open Free
module G = GuardedDMFree

module W = FStar.Monotonic.Witnessed

(**
  File structured as follows:
  0. Prerequisties about heap and references
  1. Spec monad
  2. Free monad (instantiation of lib's two-channel free monad)
  3. Define theta and proofs that is a lax morphism
  4. Define Dijkstra Monad
**)

(** ** START Section 0: heaps and references **)

(**
type mref (a:Type0) (rel:preorder a) =
  r:Heap.mref a rel {is_mm r = false}**)

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

(** The MST commands, as indexed command types for lib's free monad.
    The commands with Type0 results go on the first channel (summed with
    the guard commands of lib.GuardedDMFree, which play the role the old
    PartialCall constructor played); get_heap, whose result erased heap
    lives in Type u#1, goes on the second channel, whose index universe is
    independent of the first channel's. *)
noeq
type mst_cmds : Type0 -> Type u#1 =
| CRead    : #b:Type0 -> #rel:preorder b -> mref b rel -> mst_cmds b
| CWrite   : #b:Type0 -> #rel:preorder b -> mref b rel -> b -> mst_cmds unit
| CAlloc   : #b:Type0 -> #rel:preorder b -> b -> mst_cmds (mref b rel)
| CWitness : heap_predicate_stable -> mst_cmds unit
| CRecall  : heap_predicate_stable -> mst_cmds unit

noeq
type heap_cmds : Type u#1 -> Type u#1 =
| CGetHeap : heap_cmds (erased heap)

(** The carrier: lib's two-channel free monad. *)
let free (a:Type u#a) : Type u#(max 2 a) =
  Free.free (cmd_sum G.guard_cmd mst_cmds) heap_cmds a

let free_return (a:Type u#a) (x:a) : free a =
  Free.free_return x

let free_bind (#a:Type u#a) (#b:Type u#b) (l:free a) (k:a -> free b) : free b =
  Free.free_bind l k

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
  h1 == upd h0 r v /\
  rel (sel h0 r) v /\
  modifies (Set.singleton (addr_of r)) h0 h1 /\ equal_dom h0 h1 /\
  sel h1 r == v

unfold
let write_wp (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
  : st_mwp_h heap unit =
  fun p h0 ->
    h0 `contains` r /\ rel (sel h0 r) v /\
    (forall a. h0 `heap_rel` (upd h0 r v) /\ write_post r v h0 a (upd h0 r v) ==> p a (upd h0 r v))

let alloc_post #a #rel init h0 (r:mref a rel) h1 : Type0 =
  fresh r h0 h1 /\ modifies Set.empty h0 h1 /\ sel h1 r == init /\
  h1 == upd h0 r init /\ is_mm r == false /\
  addr_of r == next_addr h0 /\
  next_addr h1 > next_addr h0

unfold
let alloc_wp (#a:Type) (#rel:preorder a) (init:a) : st_mwp_h heap (mref a rel) =
  fun p h0 ->
    (forall r. h0 `heap_rel` (upd h0 r init) /\ alloc_post init h0 r (upd h0 r init) ==> p r (upd h0 r init))

unfold
let witness_wp (pred:heap_predicate) : st_mwp_h heap unit =
  fun p h -> pred h /\ stable pred /\ (witnessed pred ==> p () h)

unfold
let recall_wp (pred:heap_predicate_stable) : st_mwp_h heap unit =
  fun p h -> witnessed pred /\ (pred h ==> p () h)

unfold
let get_heap_wp : st_mwp_h heap (erased heap) =
  fun p h0 -> p (hide h0) h0

(** State-based WP of a first-channel command (guards + mst_cmds).
    (Note: destructing the command inside a `Call1` pattern trips universe
    inference, so the dispatch lives in a helper where `r` is a regular
    binder.) *)
let cmd_st_wp (#r:Type0) (op:cmd_sum G.guard_cmd mst_cmds r) : st_mwp_h heap r =
  match op with
  | CmdL (G.GCmd pre)          -> partial_call_wp pre
  | CmdR (CRead #b #rel r)     -> read_wp r
  | CmdR (CWrite #b #rel r v)  -> write_wp r v
  | CmdR (CAlloc #b #rel init) -> alloc_wp #b #rel init
  | CmdR (CWitness pred)       -> witness_wp pred
  | CmdR (CRecall pred)        -> recall_wp pred

(** State-based WP of a second-channel command (get_heap). *)
let heap_cmd_st_wp (#r:Type u#1) (op:heap_cmds r) : st_mwp_h heap r =
  match op with
  | CGetHeap -> get_heap_wp

val theta : #a:Type u#a -> free a -> st_mwp_h heap a
let rec theta #a m =
  match m with
  | Return x -> st_return heap _ x
  | Call1 op k ->
      st_bind_wp heap _ _ (cmd_st_wp op) (fun r -> theta (k r))
  | Call2 op k ->
      st_bind_wp heap _ _ (heap_cmd_st_wp op) (fun r -> theta (k r))

let lemma_theta_is_monad_morphism_ret (v:'a) :
  Lemma (theta (free_return 'a v) == st_return heap 'a v) by (compute ()) = ()


#push-options "--split_queries always"
let rec lemma_theta_is_lax_morphism_bind
  (#a:Type u#a) (#b:Type u#b) (m:free a) (f:a -> free b) :
  Lemma
    (theta (free_bind m f) ⊑ st_bind_wp heap a b (theta m) (fun x -> theta (f x))) =
  match m with
  | Return x -> ()
  | Call1 op k ->
    begin
      calc (⊑) {
        theta (free_bind (Call1 op k) f) ;
        ⊑ {}
        st_bind_wp heap _ _ (cmd_st_wp op) (fun r -> theta (free_bind (k r) f)) ;
        ⊑ {
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun x -> st_bind_wp heap _ _ (theta (k x)) (fun x -> theta (f x)) in
          introduce forall x. lhs x ⊑ rhs x with begin
            lemma_theta_is_lax_morphism_bind (k x) f
          end
        }
        st_bind_wp heap _ _ (cmd_st_wp op) (fun x -> st_bind_wp heap _ _ (theta (k x)) (fun x -> theta (f x))) ;
        ⊑ {}
        st_bind_wp heap a b (theta (Call1 op k)) (fun x -> theta (f x)) ;
      }
    end
  | Call2 op k ->
    begin
      calc (⊑) {
        theta (free_bind (Call2 op k) f) ;
        ⊑ {}
        st_bind_wp heap _ _ (heap_cmd_st_wp op) (fun r -> theta (free_bind (k r) f)) ;
        ⊑ {
          let lhs = fun r -> theta (free_bind (k r) f) in
          let rhs = fun x -> st_bind_wp heap _ _ (theta (k x)) (fun x -> theta (f x)) in
          introduce forall x. lhs x ⊑ rhs x with begin
            lemma_theta_is_lax_morphism_bind (k x) f
          end
        }
        st_bind_wp heap _ _ (heap_cmd_st_wp op) (fun x -> st_bind_wp heap _ _ (theta (k x)) (fun x -> theta (f x))) ;
        ⊑ {}
        st_bind_wp heap a b (theta (Call2 op k)) (fun x -> theta (f x)) ;
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
  Call1 (CmdL (G.GCmd pre)) Return

let mst_read (#a:Type) (#rel:preorder a) (r:mref a rel) : mst a (read_wp r) =
  Call1 (CmdR (CRead r)) Return

let mst_write (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a) : mst unit (write_wp r v) =
  Call1 (CmdR (CWrite r v)) Return

let mst_alloc (#a:Type) (#rel:preorder a) (init:a) : mst (mref a rel) (alloc_wp init) =
  Call1 (CmdR (CAlloc init)) Return

let mst_witness (pred:heap_predicate_stable) : mst unit (witness_wp pred) =
  Call1 (CmdR (CWitness pred)) Return

let mst_recall (pred:heap_predicate_stable) : mst unit (recall_wp pred) =
  Call1 (CmdR (CRecall pred)) Return

let mst_get_heap : mst (erased heap) get_heap_wp =
  Call2 CGetHeap Return

(** ** END Section 4: Dijkstra Monad **)
