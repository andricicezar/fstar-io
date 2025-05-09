module Examples.Autograder

open FStar.FiniteSet.Base
open FStar.Ghost
open FStar.Monotonic.Heap
open FStar.Preorder
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.List.Tot

open LabeledRefs
open Witnessable
open HigherOrderContracts
open PolyIface
open Compiler
open SpecTree

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

let no_cycles (ll:ref (linkedList int)) (h:heap): Type0 =
  exists (fuel:nat). no_cycles_fuel fuel ll h

let rec determine_fuel (ll:ref (linkedList int)) (ffuel:nat)
  : LR (option nat)
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

let rec sorted_fuel (fuel:nat) (ll:ref (linkedList int)) (h:heap): Type0 =
  if fuel = 0 then False
  else
    match sel h ll with
    | LLNil -> True
    | LLCons x next ->
      match sel h next with
      | LLNil -> True
      | LLCons y _ -> x <= y /\ sorted_fuel (fuel-1) next h

let sorted (ll: ref (linkedList int)) (h:heap): Type0 =
  exists (fuel:nat). sorted_fuel fuel ll h

let rec sorted_LR (fuel: nat) (ll: ref (linkedList int)): LR bool
  (requires fun h0 -> h0 `contains` ll)
  (ensures fun h0 r h1 -> h0 == h1 /\ (r ==> sorted_fuel fuel ll h0)) =
  let h = get_heap () in
  if fuel = 0 then false
  else begin
    match lr_read ll with
    | LLNil -> true
    | LLCons x next -> begin
      eliminate_ctrans_ref_pred h #(SLList SNat) ll contains_pred;
      match lr_read next with
      | LLNil -> true
      | LLCons y _ ->
        if x <= y then sorted_LR (fuel-1) next
        else false
    end
  end

let rec ll_as_list (fuel:nat) (ll:ref (linkedList 'a)) (h:heap) : GTot (list 'a) =
  match sel h ll with
  | LLNil -> []
  | LLCons hd tl -> if fuel = 0 then [hd] else hd :: ll_as_list (fuel-1) tl h

let rec ll_as_list_LR (fuel:nat) (ll:ref (linkedList int)) : LR (list int)
  (requires (fun h0 -> h0 `contains` ll))
  (ensures (fun h0 r h1 -> h0 == h1 /\ r == ll_as_list fuel ll h1)) =
  let h = get_heap () in
  eliminate_ctrans_ref_pred h #(SLList SNat) ll contains_pred;
  match lr_read ll with
  | LLNil -> []
  | LLCons hd tl -> if fuel = 0 then [hd] else hd :: ll_as_list_LR (fuel-1) tl

val sort_list (l:list int) : list int
let sort_list l = sortWith (compare_of_bool (<)) l

let same_elements (ll:ref (linkedList int)) (h0 h1:heap) : Type0 =
  sort_list (ll_as_list 10000 ll h0) == sort_list (ll_as_list 10000 ll h1)
  // not that nice that fuel is fixed to a big number, but it suffices

type student_solution =
  ll:ref (linkedList int) -> LR (resexn unit)
    (requires (fun h0 ->
      h0 `contains` ll /\
      no_cycles ll h0 /\
      is_shareable ll h0))
    (ensures (fun h0 r h1 ->
      (Inl? r ==> no_cycles ll h1 /\ sorted ll h1 /\ same_elements ll h0 h1) /\
      modifies_only_shared_and_encapsulated h0 h1 /\
      gets_shared Set.empty h0 h1))

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

let pred_ll (fuel:nat) (ll:ref (linkedList int)) (h:heap) (pred:(ref (linkedList int) -> Type0)) : Type0 =
  forall r. r `memP` (refs_of_ll fuel ll h) ==> pred r

let rec lemma_map_shared_no_cycles fuel (ll:ref (linkedList int)) h0 h1 :
  Lemma
    (requires (h0 `contains` map_shared /\
               h0 `contains` ll /\
               lr_inv h0 /\
               modifies !{map_shared} h0 h1 /\
               no_cycles_fuel fuel ll h0))
    (ensures (no_cycles_fuel fuel ll h1)) =
  match sel h0 ll with
  | LLNil -> ()
  | LLCons _ tl ->
    eliminate_ctrans_ref_pred h0 #(SLList SNat) ll contains_pred;
    lemma_map_shared_no_cycles (fuel-1) tl h0 h1

let rec lemma_modifies_footprint #a #rel (r:mref a rel) fuel ll h0 h1 :
  Lemma
    (requires (h0 `contains` r /\
               h0 `contains` ll /\
               lr_inv h0 /\
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
    (requires (h `contains` map_shared /\ h `contains` ll /\ lr_inv h /\ no_cycles_fuel fuel ll h))
    (ensures (~(addr_of map_shared `Set.mem` footprint fuel ll h))) =
  match sel h ll with
  | LLNil -> ()
  | LLCons _ tl ->
    eliminate_ctrans_ref_pred h #(SLList SNat) ll contains_pred;
    lemma_map_shared_not_in_footprint (fuel-1) tl h

let rec lemma_pred_ll (fuel:nat) (ll:ref (linkedList int)) h0 h1 :
  Lemma
    (requires (h0 `contains` ll /\
               lr_inv h0 /\
               pred_ll fuel ll h0 (fun r -> is_private r h0) /\
               modifies Set.empty h0 h1 /\
               no_cycles_fuel fuel ll h0))
    (ensures (pred_ll fuel ll h1 (fun r -> is_private r h1))) =
  match sel h0 ll with
  | LLNil -> ()
  | LLCons _ tl ->
    eliminate_ctrans_ref_pred h0 #(SLList SNat) ll contains_pred;
    lemma_pred_ll (fuel-1) tl h0 h1

(* TODO: add specs (one postcond should be no cycles) *)
let rec generate_llist (l:list int)
  : LR (ref (linkedList int))
    (requires (fun h0 -> True))
    (ensures (fun h0 ll h1 -> h1 `contains` ll /\
                          modifies !{} h0 h1 /\
                          no_cycles_fuel (length l) ll h1 /\
                          pred_footprint (length l) ll h1 (fun addr -> addr `addr_unused_in` h0) /\
                          pred_ll (length l) ll h1 (fun r -> is_private r h1))) =
  let h0 = get_heap () in
  match l with
  | [] -> lr_alloc LLNil
  | hd::tl ->
    let tll = generate_llist tl in
    let h1 = get_heap () in
    let ll = lr_alloc (LLCons hd tll) in
    let h2 = get_heap () in
    lemma_modifies_footprint map_shared (length tl) tll h1 h2;
    lemma_map_shared_no_cycles (length tl) tll h1 h2;
    assert (pred_footprint (length l) ll h2 (fun addr -> addr `addr_unused_in` h0));
    assert (pred_ll (length tl) tll h1 (fun r -> is_private r h1));
    lemma_pred_ll (length tl) tll h1 h2;
    assert (pred_ll (length tl) tll h2 (fun r -> is_private r h2));
    assert (no_cycles tll h2);
    assert (no_cycles_fuel (length tl) tll h2);
    assert (no_cycles_fuel (length l) ll h2);
    ll

let rec label_llist_as_shareable_fuel (fuel:erased nat) (ll:ref (linkedList int))
  : LR unit
    (requires (fun h0 -> h0 `contains` ll /\
                      no_cycles_fuel fuel ll h0 /\
                      pred_ll fuel ll h0 (fun r -> is_private r h0)))
    (ensures (fun h0 _ h1 -> modifies !{map_shared} h0 h1 /\
                          equal_dom h0 h1 /\
                          no_cycles_fuel fuel ll h1 /\
                          gets_shared (footprint fuel ll h1) h0 h1 /\
                          (footprint fuel ll h0 `Set.equal` footprint fuel ll h1) /\
                          is_shareable ll h1))
= let h0 = get_heap () in
  let v = lr_read ll in
  (match v with
  | LLNil -> ()
  | LLCons _ tl ->
    eliminate_ctrans_ref_pred h0 #(SLList SNat) ll (contains_pred);
    label_llist_as_shareable_fuel (fuel-1) tl
  );
  lemma_map_shared_not_in_footprint fuel ll h0;
  let h1 = get_heap () in
  lemma_modifies_footprint map_shared fuel ll h0 h1;
  assert (is_private ll h1 \/ is_shareable ll h1);
  label_shareable #(SLList SNat) ll;
  let h2 = get_heap () in
  lemma_modifies_footprint map_shared fuel ll h1 h2;
  assert (gets_shared (footprint fuel ll h2) h0 h2);
  assert (footprint fuel ll h0 `Set.equal` footprint fuel ll h2);
  lemma_map_shared_no_cycles fuel ll h1 h2

let label_llist_as_shareable (ll:ref (linkedList int)) (fuel:nat)
  : LR unit
    (requires (fun h0 -> h0 `contains` ll /\
                      no_cycles_fuel fuel ll h0 /\
                      pred_ll fuel ll h0 (fun r -> is_private r h0)))
    (ensures (fun h0 _ h1 -> modifies !{map_shared} h0 h1 /\
                          no_cycles_fuel fuel ll h1 /\
                          gets_shared (footprint fuel ll h1) h0 h1 /\
                          (footprint fuel ll h0 `Set.equal` footprint fuel ll h1) /\
                          equal_dom h0 h1 /\
                          is_shareable ll h1))
= let h0 = get_heap () in
  label_llist_as_shareable_fuel fuel ll

let lemma_lift_modifies s h0 h1 :
  Lemma (requires (modifies s h0 h1))
        (ensures (modifies_shared_and h0 h1 s)) = ()

let lemma_trans_modifies_shared_and h0 h1 h2 s s' s'' :
  Lemma (requires (modifies_shared_and h0 h1 s /\ gets_shared s'' h0 h1 /\ modifies_shared_and h1 h2 s'))
        (ensures (modifies_shared_and h0 h2 (s'' `Set.union` (s `Set.union` s')))) = ()

let lemma_trans_modifies_shared_and_encapsulated_and h0 h1 h2 s s' s'' :
  Lemma (requires (modifies_shared_and_encapsulated_and h0 h1 s /\
                   gets_shared s'' h0 h1 /\
                   modifies_shared_and_encapsulated_and h1 h2 s'))
        (ensures (modifies_shared_and_encapsulated_and h0 h2 (s'' `Set.union` (s `Set.union` s')))) = ()

#push-options "--split_queries always"
let auto_grader
  (test:list int)
  (hw: student_solution)
  (gr: mref grade grade_preorder)
  : LR unit
    (requires (fun h0 -> ~(compare_addrs gr map_shared) /\
                      is_private gr h0 /\
                      h0 `contains` gr /\
                      NotGraded? (sel h0 gr)))
    (ensures (fun h0 () h1 -> ~(NotGraded? (sel h1 gr)) /\
                           modifies_shared_and_encapsulated_and h0 h1 !{gr})) =
    let h0 = get_heap () in
    let ll = generate_llist test in // a fresh set of references S
    label_llist_as_shareable ll (length test); // set S gets shared
    let h1 = get_heap () in
    assert (modifies_shared_and_encapsulated_and h0 h1 !{map_shared});
    assert (gets_shared Set.empty h0 h1);
    assert (is_private gr h1);
    match hw ll with // shareable references get modified
    | Inl _ -> begin
      let h2 = get_heap () in
      assert (modifies_shared_and_encapsulated_and h1 h2 Set.empty);
      lemma_trans_modifies_shared_and_encapsulated_and h0 h1 h2 !{map_shared} Set.empty Set.empty;
      assert (modifies_shared_and_encapsulated_and h0 h2 !{map_shared});
      assert (gets_shared Set.empty h0 h2);
      lr_write #grade gr MaxGrade; // grade gets modified
      let h3 = get_heap () in
      assert (modifies_shared_and_encapsulated_and h2 h3 !{gr});
      lemma_trans_modifies_shared_and_encapsulated_and h0 h2 h3 !{map_shared} !{gr} Set.empty;
      assert (modifies_shared_and_encapsulated_and h0 h3 !{gr})
    end
    | Inr _ -> begin
      let h2 = get_heap () in
      lr_write gr MinGrade;
      let h3 = get_heap () in
      lemma_trans_modifies_shared_and_encapsulated_and h0 h1 h2 !{map_shared} Set.empty Set.empty;
      lemma_trans_modifies_shared_and_encapsulated_and h0 h2 h3 !{map_shared} !{gr} Set.empty;
      assert (modifies_shared_and_encapsulated_and h0 h3 !{gr})
    end
#pop-options

let test1 () : STATEwp grade AllOps (fun _ _ -> False) =
  let test = [1;3;4;2;1] in
  let gr : mref grade grade_preorder = alloc (NotGraded) in
 // auto_grader test solution gr;
  !gr

type student_solution_a3p (a3p:threep) =
  ll:ref (linkedList int) -> ST (resexn unit)
    (requires (fun h0 -> inv a3p h0 /\ satisfy ll (prref a3p) /\ no_cycles ll h0))
    (ensures (fun h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1 /\ (Inl? r ==> no_cycles ll h1 /\ sorted ll h1 /\ same_elements ll h0 h1)))

let student_solution_spec (a3p:threep) : spec =
 Spec false true
   (ref (linkedList int)) (witnessable_ref (linkedList int) #(witnessable_llist int))
   (fun ll h0 -> inv a3p h0 /\ satisfy ll (prref a3p) /\ no_cycles ll h0)
   unit
   witnessable_unit
   (fun ll h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1 /\ (Inl? r ==> no_cycles ll h1 /\ sorted ll h1 /\ same_elements ll h0 h1))

let student_solution_safe_importable a3p : safe_importable_to a3p (student_solution_a3p a3p) (Node (U00 (student_solution_spec a3p)) Leaf Leaf) =
  safe_importable_arrow_err00 a3p
    (ref (linkedList int)) Leaf #(exportable_ref a3p (linkedList int))
    unit Leaf #(safe_importable_is_importable a3p unit Leaf #(safe_importable_unit a3p))
    (fun ll h0 -> inv a3p h0 /\ satisfy ll (prref a3p) /\ no_cycles ll h0)
    (fun ll h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1 /\ (Inl? r ==> no_cycles ll h1 /\ sorted ll h1 /\ same_elements ll h0 h1))

let student_solution_hoc : hoc c3p (student_solution_spec c3p) =
  EnforcePost
    (fun _ -> ())
    (fun _ _ -> ())
    (fun ll ->
       let ll : ref (linkedList int) = ll in
       recall (contains_pred ll);
       let l0 = ll_as_list_LR 10000 ll in
       let eh0 = get_heap () in
       let check : cb_check c3p (ref (linkedList int)) (resexn unit) (fun x -> lr_pre (fun h0 -> satisfy x (prref_c) /\ no_cycles ll h0)) (fun x -> lr_post _ _ (fun h0 r h1 -> (Inl? r ==> no_cycles ll h1 /\ sorted ll h1 /\ same_elements ll h0 h1))) ll eh0 =
         (fun res ->
           let h1 = get_heap () in
           recall (contains_pred ll);
           match determine_fuel ll 10000 with
           | None -> Inr (Contract_failure "Linked list contains cycles")
           | Some fuel -> begin
                assert (no_cycles ll h1);
                if sorted_LR fuel ll then begin
                  let l1 = ll_as_list_LR 10000 ll in
                  if sort_list l0 = sort_list l1 then Inl ()
                  else Inr (Contract_failure "Linked list has different elements")
                end else Inr (Contract_failure "Linked list is not sorted")
           end) in
       (| eh0, check |))

let student_solution_pkhoc : pck_uhoc c3p =
  (| U00 (student_solution_spec c3p), U00hoc student_solution_hoc |)

let student_solution_tree : hoc_tree c3p (Node (U00 (student_solution_spec c3p)) Leaf Leaf) =
  Node student_solution_pkhoc Leaf Leaf

let sit : src_interface1 = {
  specs = (fun a3p -> Node (U00 (student_solution_spec a3p)) Leaf Leaf);
  hocs = student_solution_tree;
  ct = student_solution_a3p;
  c_ct = student_solution_safe_importable;
  psi = fun _ _ _ -> True
}

val unverified_student_hw_sort : ctx_tgt1 (comp_int_src_tgt1 sit)
let unverified_student_hw_sort #a3p my_read my_write my_alloc =
  let rec sort (fuel:nat) (l:ref (linkedList int)) : ST unit (pre_poly_arrow a3p l) (post_poly_arrow a3p) =
    if fuel = 0 then () else begin
      let cl : linkedList int = my_read #(SLList SNat) l in
      match cl with | LLNil -> ()
      | LLCons x tl -> begin
         sort (fuel-1) tl;
         let ctl : linkedList int = my_read #(SLList SNat) tl in
         match ctl with | LLNil -> ()
         | LLCons x' tl' ->
           if x <= x' then ()
           else begin
             let new_tl = my_alloc #(SLList SNat) (LLCons x tl') in
             my_write #(SLList SNat) l (LLCons x' new_tl);
             sort (fuel-1) new_tl;
             ()
           end
      end
    end
  in
  (fun l -> sort 10000 l; Inl ())

val prog : prog_src1 sit
let prog (ss:student_solution_a3p c3p) =
  let ss' : student_solution = fun (ll:ref (linkedList int)) ->
    witness (contains_pred ll);
    witness (is_shareable ll);
    ss ll
  in
  let test = [1;2;3;4;5;6] in
  let gr = lr_alloc #grade #grade_preorder NotGraded in
  auto_grader test ss' gr;
  match lr_read gr with
  | NotGraded -> -2
  | MinGrade -> -1
  | MaxGrade -> 0

(* Calling SecRef* on it *)

let compiled_prog =
  compile_pprog1 #sit prog

let whole_prog : whole_tgt1 =
  link_tgt1 compiled_prog unverified_student_hw_sort

let r = whole_prog ()
let _ =
  match r with
  | 0 -> FStar.IO.print_string "Max Grade!\n"
  | -1 -> FStar.IO.print_string "Min Grade!\n"
  | -2 -> FStar.IO.print_string "Not graded --- Impossible\n"
  | _ -> FStar.IO.print_string "Impossible\n"
