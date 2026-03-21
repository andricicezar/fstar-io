module MST.Repr


open FStar.Tactics
open FStar.Calc
open FStar.Preorder
open FStar.Monotonic.Heap
open FStar.Ghost

open Free
open Hist
open DMFree

module W = FStar.Monotonic.Witnessed

(**
  File structured as follows:
  0. Prerequisites about heap and references
  1. Spec monad (state-based WPs, kept for reference and lifting)
  2. MST commands (indexed event type for the generic free monad)
  3. Hist-based command WPs (mst_event ADT + lift to state WPs)
  4. Dijkstra Monad (instantiation of DMFree)
**)

(** ** START Section 0: heaps and references **)

let heap_rel (h1:heap) (h2:heap) =
  forall (a:Type0) (rel:preorder a) (r:mref a rel). h1 `contains` r ==>
    (h2 `contains` r /\ rel (sel h1 r) (sel h2 r))

let stable (pred: heap -> Type0) = stable pred heap_rel

type heap_predicate = heap -> Type0
type heap_predicate_stable = pred:heap_predicate {stable pred}

[@@"opaque_to_smt"]
let witnessed (pred:heap_predicate_stable) : Type0 = W.witnessed heap_rel pred

(** ** END Section 0: heaps and references **)

(** ** START Section 1: specification monad (state-based, kept for reference) **)

(** Most of it defined in FStar.Pervasives, here just adding monotonicity *)
unfold
let st_post_ord (#heap:Type) (p1 p2:st_post_h heap 'a) =
  forall r h. p1 r h ==> p2 r h

unfold
let st_wp_monotonic (heap:Type) (wp:st_wp_h heap 'a) =
  forall p1 p2. (p1 `st_post_ord` p2) ==> (forall h. wp p1 h ==> wp p2 h)

let st_mwp_h (heap a: Type) = wp:(st_wp_h heap a){st_wp_monotonic heap wp}

unfold
let st_ord #a (wp1 wp2:st_mwp_h heap a) = st_stronger heap a wp2 wp1

(** ** END Section 1: specification monad **)



(** ** START Section 2: MST commands **)

noeq
type mst_cmds : Type0 -> Type u#1 =
| CRead    : #b:Type0 -> #rel:preorder b -> mref b rel -> mst_cmds b
| CWrite   : #b:Type0 -> #rel:preorder b -> mref b rel -> b -> mst_cmds unit
| CAlloc   : #b:Type0 -> #rel:preorder b -> b -> mst_cmds (mref b rel)
| CWitness : heap_predicate_stable -> mst_cmds unit
| CRecall  : heap_predicate_stable -> mst_cmds unit
(* CGetHeap cannot be part of the GADT because erased heap : Type (not Type0).
   heap lives at universe 1 because it stores values of arbitrary Type0 types.
   We provide mst_get_heap as an assumed primitive at the DM level instead. *)

(** ** END Section 2: MST commands **)

(** ** START Section 3: hist-based command WPs **)

(** Events distinguish heap-preserving from heap-modifying operations.
    - EvNoOp: the heap is unchanged (read, witness, recall)
    - EvUpdate h': the heap was updated to h' (write, alloc)
    The initial history [EvUpdate h0] encodes the starting heap.
    current_heap walks the history to find the most recent heap state.
    apply_events folds a local trace to compute the final heap. **)

noeq
type mst_event =
  | EvNoOp  : mst_event
  | EvUpdate : heap -> mst_event

let rec current_heap (h:list mst_event) : GTot heap =
  match h with
  | [] -> emp
  | EvUpdate h' :: _ -> h'
  | EvNoOp :: rest -> current_heap rest

let rec apply_events (h0:heap) (lt:list mst_event) : GTot heap (decreases lt) =
  match lt with
  | [] -> h0
  | EvNoOp :: rest -> apply_events h0 rest
  | EvUpdate h' :: rest -> apply_events h' rest

(** State-based WP definitions (kept for reference and for lift_hist_to_st) **)

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
  (addr_of r) `addr_unused_in` h0 /\
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

(** Hist-based command WPs for DMFree instantiation.
    Each command emits one event. **)

unfold
let mst_ev_wp (_c:caller) (#r:Type0) (cmd:mst_cmds r) : hist #mst_event r =
  fun (p : hist_post #mst_event r) (h : list mst_event) ->
    let h0 = current_heap h in
    match cmd with
    | CRead #b #rel ref -> h0 `contains` ref /\ p [EvNoOp] (sel h0 ref)
    | CWrite #b #rel ref v ->
        h0 `contains` ref /\ rel (sel h0 ref) v /\
        p [EvUpdate (upd h0 ref v)] ()
    | CAlloc #b #rel init ->
        (forall (r:mref b rel). alloc_post init h0 r (upd h0 r init) ==> p [EvUpdate (upd h0 r init)] r)
    | CWitness pred ->
        pred h0 /\ stable pred /\ (witnessed pred ==> p [EvNoOp] ())
    | CRecall pred ->
        witnessed pred /\ (pred h0 ==> p [EvNoOp] ())

(** ** END Section 3: hist-based command WPs **)

(** ** START Section 4: Dijkstra Monad (instantiation of DMFree) **)

let mst (a:Type) (wp:hist #mst_event a) =
  dm mst_cmds mst_event mst_ev_wp a wp

let mst_return (#a:Type) (x:a) : mst a (hist_return #a #mst_event x) =
  dm_return mst_ev_wp x

#push-options "--z3rlimit 40"
let mst_bind
  (#a : Type)
  (#b : Type)
  (#wp_v : hist #mst_event a)
  (#wp_f: a -> hist #mst_event b)
  (v : mst a wp_v)
  (f : (x:a -> mst b (wp_f x))) :
  Tot (mst b (hist_bind wp_v wp_f)) =
  dm_bind mst_ev_wp wp_v wp_f v f
#pop-options

let mst_subcomp
  (#a : Type)
  (#wp1 : hist #mst_event a)
  (#wp2 : hist #mst_event a)
  (v : mst a wp1)
  :
  Pure (mst a wp2) (requires (wp1 ⊑ wp2)) (ensures (fun _ -> True)) =
  dm_subcomp mst_ev_wp wp1 wp2 v

let partial_return (pre:pure_pre) : mst (squash pre) (partial_call_wp #mst_event pre) =
  dm_partial_return mst_ev_wp pre

let mst_read (#a:Type) (#rel:preorder a) (r:mref a rel) : mst a (mst_ev_wp Prog (CRead r)) =
  Call Prog (CRead r) Return

let mst_write (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a) : mst unit (mst_ev_wp Prog (CWrite r v)) =
  Call Prog (CWrite r v) (fun _ -> Return ())

let mst_alloc (#a:Type) (#rel:preorder a) (init:a) : mst (mref a rel) (mst_ev_wp Prog (CAlloc init)) =
  Call Prog (CAlloc init) Return

let mst_witness (pred:heap_predicate_stable) : mst unit (mst_ev_wp Prog (CWitness pred)) =
  Call Prog (CWitness pred) (fun _ -> Return ())

let mst_recall (pred:heap_predicate_stable) : mst unit (mst_ev_wp Prog (CRecall pred)) =
  Call Prog (CRecall pred) (fun _ -> Return ())

(* CGetHeap returns erased heap : Type (universe 1), which cannot be an index
   of mst_cmds : Type0 -> Type u#1. This is because F*'s heap stores values of
   arbitrary Type0, forcing heap itself to universe 1. We assume mst_get_heap
   as a primitive — its soundness follows from the semantics of get_heap_wp. *)
unfold
let get_heap_hist_wp : hist #mst_event (erased heap) =
  fun p h -> let h0 = current_heap h in p [EvNoOp] (hide h0)

assume val mst_get_heap : mst (erased heap) get_heap_hist_wp

(** Lifting from hist-based WPs to state-based WPs.
    Converts a hist WP over mst_event events to a state-based WP.
    The initial history [EvUpdate h0] encodes the starting heap.
    apply_events folds the local trace to compute the final heap. **)

let lift_hist_to_st (#a:Type) (wp:hist #mst_event a) : st_mwp_h heap a =
  fun (p:st_post_h heap a) (h0:heap) ->
    wp (fun lt r -> p r (apply_events h0 lt)) [EvUpdate h0]

(** ** END Section 4: Dijkstra Monad **)
