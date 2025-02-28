module SharedRefs

friend FStar.Monotonic.Heap

let lemma_eq_addrs_eq_all _ _ _ = ()
let lemma_eq_ref_types_eq_value_types _ = ()

(** Popular vote for this, instead of the top-level effectful call **)
assume val secret_map : map_sharedT

let map_shared = FStar.Ghost.hide secret_map

inline_for_extraction
let share = (fun #a #p sr ->
    let h0 = get_heap () in
    lemma_next_addr_contained_refs_addr h0 sr ;
    let m = !secret_map in
    let m' = (fun p -> if p = addr_of sr then Shared else m p) in
    secret_map := m';
    let h1 = get_heap () in
    lemma_next_addr_upd h0 secret_map m'
  )

let lemma_fresh_ref_not_shared = (fun #a #rel r h -> ())

let lemma_unmodified_map_implies_same_shared_status (ms:Set.set nat) (h0 h1:heap) :
    Lemma (h0 `contains` secret_map /\ h0 `heap_rel` h1 /\ ~(addr_of secret_map `Set.mem` ms) /\ modifies ms h0 h1 ==>
      (forall #a #rel (r:mref a rel). is_shared r h0 <==> is_shared r h1)) =
    introduce h0 `contains` secret_map /\ h0 `heap_rel` h1 /\ ~(addr_of secret_map `Set.mem` ms) /\ modifies ms h0 h1 ==> (forall #a #rel (r:mref a rel). is_shared r h0 <==> is_shared r h1) with _. begin
      introduce forall a rel (r:mref a rel). is_shared r h0 <==> is_shared r h1 with begin
        introduce is_shared r h0 ==> is_shared r h1 with _. ();
        introduce is_shared r h1 ==> is_shared r h0 with _. ()
      end
    end

let lemma_same_addr_same_sharing_status = (fun ra rb h -> ())


inline_for_extraction
let encapsulate = (fun #a #p r ->
    let h0 = get_heap () in
    lemma_next_addr_contained_refs_addr h0 r ;
    let m = !secret_map in
    let m' = (fun p -> if p = addr_of r then Encapsulated else m p) in
    secret_map := m';
    let h1 = get_heap () in
    lemma_next_addr_upd h0 secret_map m'
  )
