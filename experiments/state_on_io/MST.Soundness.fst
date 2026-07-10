module MST.Soundness

(** Soundness of an MST Dijkstra monad, in the style of
    secrefstar/MST.Soundness.fst.

    Like the original, this file is a standalone model: it does not depend
    on MST.Repr, but defines its own copies of the MST commands and their
    state-based WPs. Unlike the original (which also defines its own free
    monad), the representation here is built from the free monad of this
    development: the two-channel `Free.free`, with mst_cmds on the first
    channel and heap_cmds (get_heap) on the second. Like the original, the
    guards (PartialCall there) are out of scope.

    theta is defined parameterized by an abstract `witnessed`
    predicate-transformer: soundness of witness/recall relies on the
    parametricity of programs in `witnessed`. The interpreter instantiates
    it with the trivial instance and maintains instead the set of
    predicates witnessed so far (all of which hold of the current heap, and
    keep holding by stability), while `witnessed_before` requires every
    recall to be preceded by a witness. *)

open FStar.Preorder
open FStar.Monotonic.Heap
open FStar.Ghost

open Free

module S = FStar.TSet

(** Local copy of the LabeledRefs lemma used by the secrefstar proof.
    There it is proved by friending FStar.Monotonic.Heap; here it follows
    from the distinct-addresses lemmas of the interface (their
    contrapositives give the type/preorder/mm equalities, after which
    lemma_sel_same_addr fires by its SMT pattern). *)
let lemma_eq_addrs_eq_all #a #rela #b #relb (r1:mref a rela) (r2:mref b relb) (h:heap) : Lemma
  (requires (h `contains` r1 /\ h `contains` r2 /\ addr_of r1 == addr_of r2))
  (ensures (a == b /\ rela == relb /\ is_mm r1 == is_mm r2 /\ sel h r1 == sel h r2)) =
  lemma_distinct_addrs_distinct_preorders ();
  lemma_distinct_addrs_distinct_mm ()

let heap_rel (h1:heap) (h2:heap) =
  forall (a:Type0) (rel:preorder a) (r:mref a rel). h1 `contains` r ==>
    (h2 `contains` r /\ rel (sel h1 r) (sel h2 r))

let stable (pred: heap -> Type0) = stable pred heap_rel

type heap_predicate = heap -> Type0
type heap_predicate_stable = pred:heap_predicate {stable pred}

(** The MST commands (as in MST.Repr). *)
noeq
type mst_cmds : Type0 -> Type u#1 =
| CRead    : #b:Type0 -> #rel:preorder b -> mref b rel -> mst_cmds b
| CWrite   : #b:Type0 -> #rel:preorder b -> mref b rel -> b -> mst_cmds unit
| CAlloc   : #b:Type0 -> #rel:preorder b -> b -> mst_cmds (mref b rel)
| CWitness : heap_predicate_stable -> mst_cmds unit
| CRecall  : heap_predicate_stable -> mst_cmds unit

(** get_heap: its result (erased heap) lives at universe 1, so it goes on
    the second channel of the free monad. *)
noeq
type heap_cmds : Type u#1 -> Type u#1 =
| CGetHeap : heap_cmds (erased heap)

(** The representation: the two-channel free monad of this development. *)
let mst_repr (a:Type) = free mst_cmds heap_cmds a

let state_wp a = (a -> heap -> Type0) -> (heap -> Type0)

let state_wp_return (x:'a) : state_wp 'a = fun p h0 -> p x h0
let state_wp_bind (m:state_wp 'a) (k:'a -> state_wp 'b) : state_wp 'b =
  fun p h0 -> m (fun r h1 -> k r p h1) h0

let state_wp_stronger (wp1 wp2:state_wp 'a) : Type0 =
  forall p h0. wp2 p h0 ==> wp1 p h0

(** State-based WPs of the commands (as in MST.Repr), with witness/recall
    parameterized by `witnessed`. *)

unfold
let read_wp (#a:Type) (#rel:preorder a) (r:mref a rel) : state_wp a =
  fun p h0 -> h0 `contains` r /\ p (sel h0 r) h0

unfold
let write_wp (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a) : state_wp unit =
  fun p h0 ->
    h0 `contains` r /\ rel (sel h0 r) v /\ p () (upd h0 r v)

let alloc_post #a #rel init h0 (r:mref a rel) h1 : Type0 =
  (addr_of r) `addr_unused_in` h0 /\
  fresh r h0 h1 /\ modifies Set.empty h0 h1 /\ sel h1 r == init /\
  h1 == upd h0 r init /\ is_mm r == false /\
  addr_of r == next_addr h0 /\
  next_addr h1 > next_addr h0

unfold
let alloc_wp (#a:Type) (#rel:preorder a) (init:a) : state_wp (mref a rel) =
  fun p h0 ->
    (forall r. alloc_post init h0 r (upd h0 r init) ==> p r (upd h0 r init))

unfold
let witness_wp (witnessed:heap_predicate_stable -> Type0) (pred:heap_predicate_stable) : state_wp unit =
  fun p h -> pred h /\ stable pred /\ (witnessed pred ==> p () h)

unfold
let recall_wp (witnessed:heap_predicate_stable -> Type0) (pred:heap_predicate_stable) : state_wp unit =
  fun p h -> witnessed pred /\ (pred h ==> p () h)

unfold
let get_heap_wp : state_wp (erased heap) =
  fun p h0 -> p (hide h0) h0

(** State-based WP of a first-channel command.
    (Note: destructing the command inside a `Call1` pattern trips universe
    inference, so the dispatch lives in a helper where `r` is a regular
    binder, like in MIO.satisfies.) *)
let cmd_st_wp (witnessed:heap_predicate_stable -> Type0) (#r:Type0) (op:mst_cmds r) : state_wp r =
  match op with
  | CRead #b #rel ref      -> read_wp ref
  | CWrite #b #rel ref v   -> write_wp ref v
  | CAlloc #b #rel init    -> alloc_wp #b #rel init
  | CWitness pred          -> witness_wp witnessed pred
  | CRecall pred           -> recall_wp witnessed pred

(** State-based WP of a second-channel command (get_heap). *)
let heap_cmd_st_wp (#r:Type u#1) (op:heap_cmds r) : state_wp r =
  match op with
  | CGetHeap -> get_heap_wp

let rec theta (witnessed:heap_predicate_stable -> Type0) #a (m:mst_repr a)
  : Tot (state_wp a) (decreases m) =
  match m with
  | Return x -> state_wp_return x
  | Call1 _ op k -> state_wp_bind (cmd_st_wp witnessed op) (fun x -> theta witnessed (k x))
  | Call2 _ op k -> state_wp_bind (heap_cmd_st_wp op) (fun x -> theta witnessed (k x))

(** Every recall must be preceded by a witness of the same predicate. *)
let rec witnessed_before #a (preds:S.set heap_predicate_stable) (m:mst_repr a) : Tot Type0 (decreases m) =
  match m with
  | Return _ -> True
  | Call1 _ op k ->
    (match op with
     | CWitness pred -> (S.union preds (S.singleton pred)) `witnessed_before` (k ())
     | CRecall pred  -> pred `S.mem` preds /\ preds `witnessed_before` (k ())
     | _             -> forall x. preds `witnessed_before` (k x))
  | Call2 _ _ k -> forall x. preds `witnessed_before` (k x)

type heap_w_preds =
  hp:(heap & S.set heap_predicate_stable){forall (pred:heap_predicate_stable). pred `S.mem` (snd hp) ==> pred (fst hp)}

val witnessed_trivial : heap_predicate_stable -> Type0
let witnessed_trivial pred = True // trivial instance of witnessed tokens

#push-options "--z3rlimit 40"
let rec run_mst_with_preds #a
  (wp:state_wp a)
  (m:mst_repr a{theta witnessed_trivial m `state_wp_stronger` wp})
  (post:(a -> heap -> Type0))
  (h0:heap_w_preds{wp post (fst h0) /\ (snd h0) `witnessed_before` m})
: Tot (r:(a & heap_w_preds){post (fst r) (fst (snd r))}) (decreases m)
=
  match m with
  | Return v -> (v, h0)
  | Call1 _ op k ->
    (match op with
     | CRead #b #rel r ->
         lemma_sel_equals_sel_tot_for_contained_refs (fst h0) r;
         let v = sel_tot (fst h0) r in
         run_mst_with_preds (theta witnessed_trivial (k v)) (k v) post h0
     | CWrite #b #rel r v ->
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
         assert (fst h0 `heap_rel` upd (fst h0) r v);
         run_mst_with_preds (theta witnessed_trivial (k ())) (k ()) post (upd_tot (fst h0) r v, snd h0)
     | CAlloc #b #rel init ->
         let (r, h) = alloc rel (fst h0) init false in
         lemma_upd_equals_upd_tot_for_contained_refs h r init;
         assert (fst h0 `heap_rel` upd (fst h0) r init);
         lemma_alloc rel (fst h0) init false;
         lemma_next_addr_alloc rel (fst h0) init false;
         run_mst_with_preds (theta witnessed_trivial (k r)) (k r) post (h, snd h0)
     | CWitness pred ->
         let hp = S.union (snd h0) (S.singleton pred) in
         run_mst_with_preds (theta witnessed_trivial (k ())) (k ()) post (fst h0, hp)
     | CRecall pred ->
         run_mst_with_preds (theta witnessed_trivial (k ())) (k ()) post h0)
  | Call2 _ op k ->
    (match op with
     | CGetHeap ->
         (* coerce_eq avoids the (ghost) reveal coercion the elaborator
            inserts when applying k directly to an erased value *)
         let h = coerce_eq () (hide (fst h0)) in
         run_mst_with_preds (theta witnessed_trivial (k h)) (k h) post h0)
#pop-options

let run_mst #a
  (wp:state_wp a)
  (m:mst_repr a{theta witnessed_trivial m `state_wp_stronger` wp /\ S.empty `witnessed_before` m})
  (post:(a -> heap -> Type0))
  (h0:heap{wp post h0})
: Tot (vh:(a & heap){post (fst vh) (snd vh)})
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
