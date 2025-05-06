module Examples.Autograder

open FStar.FiniteSet.Base
open FStar.Ghost
open FStar.Monotonic.Heap
open FStar.Preorder
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.List.Tot

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

let rec no_cycles_fuel (fuel:nat) (ll:ref (linkedList 'a)) (h:heap): Type0 =
  match sel h ll with
  | LLNil -> True
  | LLCons x xsref -> if fuel = 0 then False else no_cycles_fuel (fuel - 1) xsref h

let rec sorted_fuel (fuel:nat) (ll:linkedList int) (h:heap): Type0 =
  if fuel = 0 then False
  else
    match ll with
    | LLNil -> True
    | LLCons x next ->
      let tl = sel h next in
      match tl with
      | LLNil -> True
      | LLCons y next -> x <= y /\ sorted_fuel (fuel - 1) tl h

let no_cycles (ll:ref (linkedList int)) (h:heap): Type0 =
  exists (fuel:nat). no_cycles_fuel fuel ll h

let sorted (ll: ref (linkedList int)) (h:heap): Type0 =
  exists fuel. sorted_fuel fuel (sel h ll) h

type student_solution =
  ll:ref(linkedList int) -> SST (option unit)
    (requires (fun h0 ->
      h0 `contains` ll /\
      no_cycles ll h0 /\
      is_shared ll h0))
    (ensures (fun h0 r h1 ->
      (Some? r ==> no_cycles ll h1 /\ sorted ll h1) /\ // /\ same_elements ll h0 h1) /\
      modifies_only_shared h0 h1 /\
      gets_shared Set.empty h0 h1))

// let wss : witnessable (list (mref grade grade_preorder * student_solution)) = admit ()
(*  witnessable_list (witnessable_pair (witnessable_mref witnessable_grade grade_preorder) witnessable_llist) *)


let rec refs_of_ll (fuel:nat) (ll:ref (linkedList int)) (h:heap) : GTot (list (ref (linkedList int))) =
  ll :: (
    match sel h ll with
    | LLNil -> []
    | LLCons _ tl -> if fuel = 0 then [] else refs_of_ll (fuel-1) tl h)

let rec footprint (fuel:nat) (ll:ref (linkedList int)) (h:heap) : GTot (Set.set nat) =
  !{ll} `Set.union` (
    match sel h ll with
    | LLNil -> Set.empty
    | LLCons _ tl -> if fuel = 0 then Set.empty else footprint (fuel-1) tl h)

let pred_footprint (fuel:nat) (ll:ref (linkedList int)) (h:heap) (pred:pos -> Type0) : Type0 =
  forall addr. addr `Set.mem` (footprint fuel ll h) ==> pred addr

val gmap: ('a -> GTot 'b) -> list 'a -> GTot (list 'b)
let rec gmap f x = match x with
  | [] -> []
  | a::tl -> f a::gmap f tl

let refs_of_ll_as_set (fuel:nat) (ll:ref (linkedList int)) (h:heap) : GTot (set nat) =
  Set.as_set (gmap addr_of (refs_of_ll fuel ll h))

let pred_ll (fuel:nat) (ll:ref (linkedList int)) (h:heap) (pred:(ref (linkedList int) -> Type0)) : Type0 =
  forall r. r `memP` (refs_of_ll fuel ll h) ==> pred r

(* TODO: add specs (one postcond should be no cycles) *)
let rec generate_llist (l:list int)
  : SST (ref (linkedList int))
    (requires (fun h0 -> True))
    (ensures (fun h0 ll h1 -> h1 `contains` ll /\
                          modifies !{} h0 h1 /\
                          no_cycles_fuel (length l) ll h1 /\
                          pred_footprint (length l) ll h1 (fun addr -> addr `addr_unused_in` h0) /\
                          pred_ll (length l) ll h1 (fun r -> is_private r h1))) =
  let h0 = get_heap () in
  match l with
  | [] -> sst_alloc LLNil
  | hd::tl ->
    let tll = generate_llist tl in
    let h1 = get_heap () in
    let ll = sst_alloc (LLCons hd tll) in
    let h2 = get_heap () in
    assume (pred_footprint (length l) ll h2 (fun addr -> addr `addr_unused_in` h0));
    assume (pred_ll (length tl) tll h2 (fun r -> is_private r h2));
    assume (no_cycles tll h2);
    assume (no_cycles_fuel (length tl) tll h2);
    assert (no_cycles_fuel (length l) ll h2);
    ll

let rec lemma_modifies_footprint #a #rel (r:mref a rel) fuel ll h0 h1 :
  Lemma
    (requires (h0 `contains` r /\
               h0 `contains` ll /\
               sst_inv h0 /\
               no_cycles_fuel fuel ll h0 /\
               ~(addr_of r `Set.mem` footprint fuel ll h0) /\
               modifies !{r} h0 h1))
    (ensures (footprint fuel ll h0 `Set.equal` footprint fuel ll h1)) =
  match sel h1 ll with
  | LLNil -> ()
  | LLCons _ tl ->
    eliminate_ctrans_ref_pred h0 #(SLList SNat) ll (contains_pred);
    lemma_modifies_footprint r (fuel-1) tl h0 h1

let rec lemma_map_shared_not_in_footprint fuel (ll:ref (linkedList int)) h :
  Lemma
    (requires (h `contains` map_shared /\ h `contains` ll /\ sst_inv h /\ no_cycles_fuel fuel ll h))
    (ensures (~(addr_of map_shared `Set.mem` footprint fuel ll h))) =
  match sel h ll with
  | LLNil -> ()
  | LLCons _ tl ->
    eliminate_ctrans_ref_pred h #(SLList SNat) ll contains_pred;
    lemma_map_shared_not_in_footprint (fuel-1) tl h

let rec label_llist_as_shareable_fuel (fuel:erased nat) (ll:ref (linkedList int))
  : SST unit
    (requires (fun h0 -> h0 `contains` ll /\
                      no_cycles_fuel fuel ll h0 /\
                      pred_ll fuel ll h0 (fun r -> is_private r h0)))
    (ensures (fun h0 _ h1 -> modifies !{map_shared} h0 h1 /\
                          equal_dom h0 h1 /\
                          no_cycles_fuel fuel ll h1 /\
                          gets_shared (footprint fuel ll h1) h0 h1 /\
                          (footprint fuel ll h0 `Set.equal` footprint fuel ll h1) /\
                          is_shared ll h1))
= let h0 = get_heap () in
  let v = sst_read ll in
  (match v with
  | LLNil -> ()
  | LLCons _ tl ->
    eliminate_ctrans_ref_pred h0 #(SLList SNat) ll (contains_pred);
    label_llist_as_shareable_fuel (fuel-1) tl
  );
  let h1 = get_heap () in
  assume (is_private ll h1);
  sst_share #(SLList SNat) ll;
  let h2 = get_heap () in
  assume (gets_shared (footprint fuel ll h2) h0 h2);
  lemma_map_shared_not_in_footprint fuel ll h1;
  lemma_modifies_footprint map_shared fuel ll h1 h2;
  assert (footprint fuel ll h0 `Set.equal` footprint fuel ll h2);
  assume (no_cycles_fuel fuel ll h2)

let label_llist_as_shareable (ll:ref (linkedList int)) (fuel:nat)
  : SST unit
    (requires (fun h0 -> h0 `contains` ll /\
                      no_cycles_fuel fuel ll h0 /\
                      pred_ll fuel ll h0 (fun r -> is_private r h0)))
    (ensures (fun h0 _ h1 -> modifies !{map_shared} h0 h1 /\
                          no_cycles_fuel fuel ll h1 /\
                          gets_shared (footprint fuel ll h1) h0 h1 /\
                          (footprint fuel ll h0 `Set.equal` footprint fuel ll h1) /\
                          equal_dom h0 h1 /\
                          is_shared ll h1))
= let h0 = get_heap () in
  label_llist_as_shareable_fuel fuel ll

(** TODO: can we add SMTPat to these? **)
let lemma_lift_modifies s h0 h1 :
  Lemma (requires (modifies s h0 h1))
        (ensures (modifies_shared_and h0 h1 s)) = ()

let lemma_trans_modifies_shared_and h0 h1 h2 s s' s'' :
  Lemma (requires (modifies_shared_and h0 h1 s /\ gets_shared s'' h0 h1 /\ modifies_shared_and h1 h2 s'))
        (ensures (modifies_shared_and h0 h2 (s'' `Set.union` (s `Set.union` s')))) = ()

let auto_grader
  (test:list int)
  (hw: student_solution)
  (gr: mref grade grade_preorder)
  : SST unit
    (requires (fun h0 -> ~(compare_addrs gr map_shared) /\
                      is_private gr h0 /\
                      h0 `contains` gr /\
                      NotGraded? (sel h0 gr)))
    (ensures (fun h0 () h1 -> ~(NotGraded? (sel h1 gr)) /\
                           modifies_shared_and h0 h1 !{gr})) =
    let h0 = get_heap () in
    let ll = generate_llist test in // a fresh set of references S
    label_llist_as_shareable ll (length test); // set S gets shared
    let h1 = get_heap () in
    assert (modifies_shared_and h0 h1 !{map_shared});
    assert (gets_shared Set.empty h0 h1);
    assert (is_private gr h1);
    match hw ll with // shareable references get modified
    | Some _ -> begin
      let h2 = get_heap () in
      assert (modifies_shared_and h1 h2 Set.empty);
      lemma_trans_modifies_shared_and h0 h1 h2 !{map_shared} Set.empty Set.empty;
      assert (modifies_shared_and h0 h2 !{map_shared});
      assert (gets_shared Set.empty h0 h2);
      sst_write #grade gr MaxGrade; // grade gets modified
      let h3 = get_heap () in
      assert (modifies_shared_and h2 h3 !{gr});
      lemma_trans_modifies_shared_and h0 h2 h3 !{map_shared} !{gr} Set.empty;
      assert (modifies_shared_and h0 h3 !{gr})
    end
    | None -> begin
      let h2 = get_heap () in
      sst_write gr MinGrade;
      let h3 = get_heap () in
      lemma_trans_modifies_shared_and h0 h1 h2 !{map_shared} Set.empty Set.empty;
      lemma_trans_modifies_shared_and h0 h2 h3 !{map_shared} !{gr} Set.empty;
      assert (modifies_shared_and h0 h3 !{gr})
    end

let test1 () : STATEwp grade AllOps (fun _ _ -> False) =
  let test = [1;3;4;2;1] in
  let gr : mref grade grade_preorder = alloc (NotGraded) in
 // auto_grader test solution gr;
  !gr

let rec determine_fuel (ll:ref (linkedList int)) (ffuel:nat)
  : SST (option nat)
    (requires (fun h0 -> h0 `contains` ll))
    (ensures (fun h0 ofuel h1 -> h0 == h1 /\ (Some? ofuel ==> (Some?.v ofuel <= ffuel) /\ no_cycles_fuel (Some?.v ofuel) ll h0)))
    (decreases ffuel) =
  if ffuel = 0 then None
  else
    match !ll with
    | LLNil -> Some 1
    | LLCons _ tl -> begin
      let h0 = get_heap () in
      eliminate_ctrans_ref_pred h0 #(SLList SNat) ll contains_pred;
      match determine_fuel tl (ffuel-1) with
      | None -> None
      | Some fuel -> Some (fuel + 1)
    end

(**
let same_elements (ll:ref (linkedList int)) (h0 h1:heap): Type0 =
  let length_h0 = ll_length ll h0 in
  let length_h1 = ll_length ll h1 in
  if length_h0 <> length_h1 then False
  else
    exists fuel. elements_of_ll_acc fuel ll h0 FSet.emptyset == elements_of_ll_acc fuel ll h0 FSet.emptyset

 let same_elements_SST (ll: linkedList int): SST bool
   (requires fun h0 -> satisfy_on_heap ll h0 contains_pred)
   (ensures fun h0 r h1 -> r ==> same_elements ll h0 h1)
   = admit()

let rec sorted_SST (fuel: nat) (ll: linkedList int): SST bool
  (requires fun h0 -> satisfy_on_heap ll h0 contains_pred)
  (ensures fun h0 r h1 -> r ==> sorted ll h0) =
  if fuel = 0 then false
  else
    match ll with
    | LLNil -> true
    | LLCons x next ->
      let tl = sst_read next in
      match tl with
      | LLNil -> true
      | LLCons y next ->
        if x > y then false
        else begin
          let h = get_heap() in
          heap_contains_all_refs_of_ll ll h;
          admit();
          sorted_SST (fuel - 1) tl
        end
**)
