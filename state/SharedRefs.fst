module SharedRefs

let lemma_eq_addrs_eq_all _ _ _ = admit ()
let lemma_eq_ref_types_eq_value_types _ = admit ()

(**
private (** TODO: is this necessary? **)
let secret_map : map_sharedT = (** In Pulse, this can be a ghost reference and `share` can be a ghost computation *)
  alloc (fun _ -> false)
**)
(** Popular vote for this, instead of the top-level effectful call **)
assume val secret_map : map_sharedT

let map_shared = FStar.Ghost.hide secret_map

let share = (fun #a #p sr ->
    let h0 = get () in
    lemma_next_addr_contained_refs_addr h0 sr;
    let m = !secret_map in
    let m' = (fun p -> if p = addr_of sr then true else m p) in
    secret_map := m';
    let h1 = get () in
    lemma_next_addr_upd_tot h0 secret_map m'
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
