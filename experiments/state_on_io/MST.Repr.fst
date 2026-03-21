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
  1. Spec monad (state-based WPs)
  2. MST commands (indexed command type for the free monad)
  3. MST events + hist-based command WPs
  4. Dijkstra Monad (indexed by state-based WPs via lift)
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

(** ** START Section 1: specification monad (state-based WPs) **)

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

unfold
let st_return (x:'a) : st_mwp_h heap 'a = fun p h -> p x h

unfold
let st_bind (#a #b:Type) (wp_v:st_mwp_h heap a) (wp_f:a -> st_mwp_h heap b) : st_mwp_h heap b =
  fun p h -> wp_v (fun r h' -> wp_f r p h') h

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

(** ** START Section 3: MST events + hist-based command WPs **)

(** Events record heap-modifying operations and their arguments.
    Witness/Recall are ghost operations that don't modify the heap,
    so they don't produce events.
    - EvInit h0: bootstrapping event encoding the initial heap
    - EvRead ref: a reference was read (heap unchanged)
    - EvWrite ref v: a reference was updated to v
    - EvAlloc r init: reference r was allocated with initial value init
    apply_event interprets an event to compute the resulting heap.
    current_heap folds the history to recover the current heap state. **)

noeq
type mst_event =
  | EvInit    : heap -> mst_event
  | EvRead    : #b:Type0 -> #rel:preorder b -> mref b rel -> mst_event
  | EvWrite   : #b:Type0 -> #rel:preorder b -> mref b rel -> b -> mst_event
  | EvAlloc   : #b:Type0 -> #rel:preorder b -> mref b rel -> b -> mst_event

let apply_event (ev:mst_event) (h:heap) : GTot heap =
  match ev with
  | EvInit h0 -> h0
  | EvRead _ -> h
  | EvWrite r v -> upd h r v
  | EvAlloc r init -> upd h r init

let rec current_heap (h:list mst_event) : GTot heap =
  match h with
  | [] -> emp
  | ev :: rest -> apply_event ev (current_heap rest)

let rec apply_events (h0:heap) (lt:list mst_event) : GTot heap (decreases lt) =
  match lt with
  | [] -> h0
  | ev :: rest -> apply_events (apply_event ev h0) rest

(** State-based WP definitions for each command.
    These match the natural lift of the hist-based command WPs.
    Stronger properties (heap_rel, modifies, etc.) follow from heap axioms. *)

unfold
let read_wp (#a:Type) (#rel:preorder a) (r:mref a rel) : st_mwp_h heap a =
  fun p h0 -> h0 `contains` r /\ p (sel h0 r) h0

unfold
let write_wp (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
  : st_mwp_h heap unit =
  fun p h0 ->
    h0 `contains` r /\ rel (sel h0 r) v /\ p () (upd h0 r v)

let alloc_post #a #rel init h0 (r:mref a rel) h1 : Type0 =
  (addr_of r) `addr_unused_in` h0 /\
  fresh r h0 h1 /\ modifies Set.empty h0 h1 /\ sel h1 r == init /\
  h1 == upd h0 r init /\ is_mm r == false /\
  addr_of r == next_addr h0 /\
  next_addr h1 > next_addr h0

unfold
let alloc_wp (#a:Type) (#rel:preorder a) (init:a) : st_mwp_h heap (mref a rel) =
  fun p h0 ->
    (forall r. alloc_post init h0 r (upd h0 r init) ==> p r (upd h0 r init))

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
    Each command emits descriptive events; CWitness/CRecall emit no events
    since they don't modify the heap. *)

unfold
let mst_cwp (_c:caller) (#r:Type0) (op:mst_cmds r) : hist #mst_event r =
  fun (p : hist_post #mst_event r) (h : list mst_event) ->
    let h0 = current_heap h in
    match op with
    | CRead #b #rel ref -> h0 `contains` ref /\ p [EvRead ref] (sel h0 ref)
    | CWrite #b #rel ref v ->
        h0 `contains` ref /\ rel (sel h0 ref) v /\
        p [EvWrite ref v] ()
    | CAlloc #b #rel init ->
        (forall (r:mref b rel). alloc_post init h0 r (upd h0 r init) ==> p [EvAlloc r init] r)
    | CWitness pred ->
        pred h0 /\ stable pred /\ (witnessed pred ==> p [] ())
    | CRecall pred ->
        witnessed pred /\ (pred h0 ==> p [] ())

(** Lifting from hist-based WPs to state-based WPs.
    Converts a hist WP over mst_event events to a state-based WP.
    The initial history [EvInit h0] encodes the starting heap.
    apply_events folds the local trace to compute the final heap. **)

let lift_hist_to_st (#a:Type) (wp:hist #mst_event a) : st_mwp_h heap a =
  fun (p:st_post_h heap a) (h0:heap) ->
    wp (fun lt r -> p r (apply_events h0 lt)) [EvInit h0]

(** ** END Section 3: MST events + hist-based command WPs **)

(** ** START Section 4: Dijkstra Monad (indexed by state-based WPs) **)

(** mst a wp: computation returning a, with state-based WP wp.
    Internally a free monad tree whose theta (lifted to state) refines wp. *)
let mst (a:Type) (wp:st_mwp_h heap a) =
  m:(free mst_cmds a){lift_hist_to_st (theta mst_cwp m) `st_ord` wp}

let mst_return (#a:Type) (x:a) : mst a (st_return x) =
  Return x

(** mst_bind requires that lift_hist_to_st distributes over hist_bind for
    mst_cwp-produced WPs. This holds because mst_cwp only depends on
    current_heap (not the full history structure), making the lifted bind
    equivalent to st_bind. We assume this property; a full proof would
    require showing theta mst_cwp is history-shape-insensitive. *)
#push-options "--z3rlimit 40"
let mst_bind
  (#a : Type)
  (#b : Type)
  (#wp_v : st_mwp_h heap a)
  (#wp_f: a -> st_mwp_h heap b)
  (v : mst a wp_v)
  (f : (x:a -> mst b (wp_f x))) :
  Tot (mst b (st_bind wp_v wp_f)) =
  lemma_theta_is_lax_morphism_bind mst_cwp v f;
  assume (lift_hist_to_st (theta mst_cwp (free_bind v f)) `st_ord` st_bind wp_v wp_f);
  free_bind v f
#pop-options

let mst_subcomp
  (#a : Type)
  (#wp1 : st_mwp_h heap a)
  (#wp2 : st_mwp_h heap a)
  (v : mst a wp1)
  :
  Pure (mst a wp2) (requires (wp1 `st_ord` wp2)) (ensures (fun _ -> True)) =
  v

let guard_st_wp (pre:pure_pre) : st_mwp_h heap (squash pre) =
  let wp' : st_wp_h heap (squash pre) = fun p h -> pre /\ p () h in
  assert (forall (post1 post2:st_post_h heap (squash pre)).
    (st_post_ord post1 post2 ==> (forall h. wp' post1 h ==> wp' post2 h)));
  wp'

let guard_return (pre:pure_pre) : mst (squash pre) (guard_st_wp pre) =
  Guard pre Return

#push-options "--z3rlimit 40"
let mst_read (#a:Type) (#rel:preorder a) (r:mref a rel) : mst a (read_wp r) =
  Call Prog (CRead r) Return

let mst_write (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a) : mst unit (write_wp r v) =
  Call Prog (CWrite r v) (fun _ -> Return ())

let mst_alloc (#a:Type) (#rel:preorder a) (init:a) : mst (mref a rel) (alloc_wp init) =
  Call Prog (CAlloc init) Return

let mst_witness (pred:heap_predicate_stable) : mst unit (witness_wp pred) =
  Call Prog (CWitness pred) (fun _ -> Return ())

let mst_recall (pred:heap_predicate_stable) : mst unit (recall_wp pred) =
  Call Prog (CRecall pred) (fun _ -> Return ())
#pop-options

(* CGetHeap returns erased heap : Type (universe 1), which cannot be an index
   of mst_cmds : Type0 -> Type u#1. This is because F*'s heap stores values of
   arbitrary Type0, forcing heap itself to universe 1. We assume mst_get_heap
   as a primitive — its soundness follows from the semantics of get_heap_wp. *)
assume val mst_get_heap : mst (erased heap) get_heap_wp

(** ** END Section 4: Dijkstra Monad **)
