module Examples.AutograderListSpec

open FStar.FiniteSet.Base
open FStar.Ghost
open FStar.Monotonic.Heap
open FStar.Preorder
open FStar.Tactics.Typeclasses

open SharedRefs
open Witnessable

module FSet = FStar.FiniteSet.Base

type grade =
| NotGraded
| MaxGrade
| MinGrade

noextract
instance witnessable_grade : witnessable grade = {
  satisfy = (fun _ _ -> True);
}

let grade_preorder : preorder grade = fun g1 g2 ->
  match g1 with
  | NotGraded -> True
  | _ -> g1 == g2

let rec llist_spec (h:heap) (l:list int) (ll:linkedList int) : Type0 = 
  match l with
  | [] -> LLNil? ll
  | x::xs -> 
      LLCons? ll /\ 
      LLCons?.v ll == x /\ 
      h `contains` LLCons?.next ll /\
      ~(compare_addrs (LLCons?.next ll) map_shared) /\
      llist_spec h xs (sel h (LLCons?.next ll))

let rec lemma_llist_spec_modifies_empty (h0:heap) (h1:heap) (l:list int) (ll:linkedList int)
  : Lemma (requires (llist_spec h0 l ll /\ modifies Set.empty h0 h1))
          (ensures  (llist_spec h1 l ll))
          [SMTPat (llist_spec h1 l ll); SMTPat (modifies Set.empty h0 h1)] = 
  match l with
  | [] -> ()
  | x::xs -> 
    lemma_llist_spec_modifies_empty h0 h1 xs (sel h0 (LLCons?.next ll))

let rec lemma_llist_spec_modifies_map_shared (h0:heap) (h1:heap) (l:list int) (ll:linkedList int)
  : Lemma (requires (llist_spec h0 l ll /\ modifies !{map_shared} h0 h1))
          (ensures  (llist_spec h1 l ll))
          [SMTPat (llist_spec h0 l ll); SMTPat (llist_spec h1 l ll)] = 
  match l with
  | [] -> ()
  | x::xs -> 
    lemma_llist_spec_modifies_map_shared h0 h1 xs (sel h0 (LLCons?.next ll))

assume val list_sort : list int -> list int

type student_solution (l:list int) =
  ll_ref:ref(linkedList int) -> SST (option unit)
    (requires (fun h0 ->
      llist_spec h0 l (sel h0 ll_ref) /\
      forall_refs_heap contains_pred h0 #(SRef (SLList SNat)) ll_ref /\
      forall_refs_heap is_shared h0 #(SRef (SLList SNat)) ll_ref))
    (ensures (fun h0 r h1 ->
      (Some? r ==> llist_spec h1 (list_sort l) (sel h1 ll_ref)) /\
      modifies_only_shared h0 h1 /\ gets_shared Set.empty h0 h1)) // no cycles, sorted, same elements --- all via spec list l

let rec generate_llist (l:list int)
  : SST (linkedList int)
    (requires (fun h0 -> True))
    (ensures (fun h0 ll h1 -> forall_refs_heap contains_pred h1 #(SLList SNat) ll /\
                           forall_refs_heap is_shared h1 #(SLList SNat) ll /\
                           modifies !{map_shared} h0 h1 /\
                           gets_shared Set.empty h0 h1 /\
                           llist_spec h1 l ll              // i.e., no cycles via l
                  )) =
  match l with
  | [] -> LLNil
  | hd::tl ->
      let ll = generate_llist tl in
      let ll_ref = sst_alloc_shareable #(SLList SNat) ll in
      sst_share ll_ref;
      LLCons hd ll_ref

let grading_done (gr: mref grade grade_preorder) h = sel h gr =!= NotGraded

#push-options "--z3rlimit 10000"
let auto_grader
  (test:list int)
  (hw: student_solution test)
  (gr: mref grade grade_preorder)
  : SST unit
    (requires (fun h0 -> ~(grading_done gr h0) /\
                      ~(compare_addrs gr map_shared) /\
                      is_private gr h0 /\
                      h0 `contains` gr))
    (ensures (fun h0 () h1 -> grading_done gr h1 /\
                           modifies_shared_and h0 h1 !{gr})) =
    let ll = generate_llist test in
    let ref_ll = sst_alloc_shareable #(SLList SNat) ll in
    sst_share ref_ll;
    (match hw ref_ll with
    | Some _ ->
        sst_write gr MaxGrade
    | None ->
        sst_write gr MinGrade)
#pop-options
