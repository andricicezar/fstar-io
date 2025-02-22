module Examples.Autograder

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

instance witnessable_grade : witnessable grade = {
  satisfy = (fun _ _ -> True);
  satisfy_on_heap = (fun _ _ _ -> True);
  satisfy_on_heap_monotonic = (fun _ _ _ _ -> ());
  pwitness = (fun _ _ -> (fun () -> ()));
}

let grade_preorder : preorder grade = fun g1 g2 ->
  match g1 with
  | NotGraded -> True
  | _ -> g1 == g2

(* let max_length = pow2 32 - 1 *)

(* TODO: two implementations of each : one with Type0 (pred) & one for HO contracts (ST effect) *)
let rec no_cycles_fuel (fuel:nat) (ll:linkedList int) (h:heap): Type0 =
  if fuel = 0 then False
  else
    match ll with
    | LLNil -> True
    | LLCons x xsref -> no_cycles_fuel (fuel - 1) (sel h xsref) h

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

let rec footprint_acc
  (l: linkedList int) 
  (h:heap)
  (hdom:(FSet.set nat){forall (a:Type) (rel:_) (r:mref a rel). h `contains` r ==> addr_of r `FSet.mem` hdom})
  (acc:(FSet.set nat){acc `FSet.subset` hdom}) : 
  GTot (FSet.set nat) (decreases (FSet.cardinality (hdom `FSet.difference` acc))) =
  match l with 
  | LLNil -> acc
  | LLCons x xsref -> 
    if addr_of xsref `FSet.mem` acc then acc
    else begin
      assume (h `contains` xsref); (* Turn this into a type refinement? *)
      let acc' = (acc `FSet.union` FSet.singleton (addr_of xsref)) in
      FSet.all_finite_set_facts_lemma ();
      footprint_acc (sel h xsref) h hdom acc' 
    end

let get_heap_domain h =
  FSet.all_finite_set_facts_lemma ();
  let rec aux (n:nat) : res:(FSet.set nat){forall i. 0 < i && i <= n ==> i `FSet.mem` res} =
    if n = 0 then FSet.emptyset else FSet.singleton n `FSet.union` (aux (n-1)) in
  aux (next_addr h - 1)

let footprint (l: linkedList int) (h:heap) : (GTot (FSet.set nat)) =
  let hdom = get_heap_domain h in
  FSet.all_finite_set_facts_lemma ();
  assert (FSet.emptyset `FSet.subset` hdom);
  assume (forall (a:Type) (rel:_) (r:mref a rel). h `contains` r ==> addr_of r `FSet.mem` hdom);
  footprint_acc l h hdom FSet.emptyset

let ll_length (ll: linkedList int) (h: heap): GTot int =
  cardinality (footprint ll h)

let no_cycles (ll:linkedList int) (h:heap): Type0 =
  let necess_fuel = ll_length ll h + 1 in
  no_cycles_fuel necess_fuel ll h

let sorted (ll: linkedList int) (h:heap): Type0 = 
  let necess_fuel = ll_length ll h + 1 in
  sorted_fuel necess_fuel ll h

let rec elements_of_ll_acc (fuel:nat) (ll:linkedList int) (h:heap) (acc: FSet.set int) : GTot (FSet.set int) =
  if fuel = 0 then acc
  else 
    match ll with 
    | LLNil -> acc
    | LLCons v next -> 
      let acc' = acc `union` singleton(v) in 
      let tail = sel h next in 
      elements_of_ll_acc (fuel - 1) tail h acc'

(* let elements_of_ll (fuel: nat) (ll:linkedList int) (h:heap) (acc: FSet.set int) : GTot (FSet.set int) = 
  elements_of_ll_acc fuel ll h FSet.emptyset *) (* Previously: fuel = max_length *)

let same_elements (ll:linkedList int) (h0 h1:heap): Type0 = 
  let length_h0 = ll_length ll h0 in
  let length_h1 = ll_length ll h1 in
  if length_h0 <> length_h1 then False
  else 
    let necess_fuel = length_h0 + 1 in
    elements_of_ll_acc necess_fuel ll h0 FSet.emptyset == elements_of_ll_acc necess_fuel ll h0 FSet.emptyset

let rec no_cycles_SST (fuel: nat) (ll: linkedList int): SST bool
  (requires fun h0 -> satisfy_on_heap ll h0 contains_pred)
  (ensures fun h0 r h1 -> h0 == h1 /\ (r ==> no_cycles ll h0)) = (* shouldn't it be <==> instead of ==>?) *)
  if fuel = 0 then false
  else
    match ll with
      | LLNil -> true
      | LLCons x xsref -> 
        let h0 = get_heap() in
        assert (h0 `contains` xsref);
        let tail : linkedList int = sst_read' xsref in
        let h1 = get_heap() in 
        assert (h0 == h1);
        assume (satisfy_on_heap (sel h0 xsref) h0 contains_pred); (* add lemma for this *)
        admit();
        no_cycles_SST (fuel - 1) tail

let sorted_SST (ll: linkedList int): SST bool 
  (requires fun h0 -> satisfy_on_heap ll h0 contains_pred)
  (ensures fun h0 r h1 -> r <==> sorted ll h0) 
  = admit()

let same_elements_SST (ll: linkedList int): SST bool 
  (requires fun h0 -> satisfy_on_heap ll h0 contains_pred)
  (ensures fun h0 r h1 -> r <==> same_elements ll h0 h1) 
  = admit()

type student_solution =
  ll_ref:ref(linkedList int) -> SST (option unit)
    (requires (fun h0 ->
      no_cycles (sel h0 ll_ref) h0 /\
      forall_refs_heap contains_pred h0 #(SRef (SLList SNat)) ll_ref /\ 
      forall_refs_heap is_shared h0 #(SRef (SLList SNat)) ll_ref))
    (ensures (fun h0 r h1 ->
      (Some? r ==> no_cycles (sel h1 ll_ref) h1 /\ sorted (sel h1 ll_ref) h1 /\ same_elements (sel h1 ll_ref) h0 h1) /\
      modifies_only_shared h0 h1 /\ gets_shared Set.empty h0 h1))

let wss : witnessable (list (mref grade grade_preorder * student_solution)) = admit ()
(*  witnessable_list (witnessable_pair (witnessable_mref witnessable_grade grade_preorder) witnessable_llist) *)

let grading_done (gr: mref grade grade_preorder) h = sel h gr =!= NotGraded

(* TODO: add specs (one postcond should be no cycles) *)
let rec generate_llist (l:list int)
  : SST (linkedList int)
    (requires (fun h0 -> True))
    (ensures (fun h0 r h1 -> satisfy_on_heap r h1 contains_pred
                  (* /\ exists fuel . no_cycles_fuel fuel r h1 *))) =
  match l with
  | [] -> LLNil
  | hd::tl -> LLCons hd (sst_alloc_shareable #(SLList SNat) (generate_llist tl))


let rec share_llist (l:linkedList int) 
  : SST unit 
    (requires (fun h0 -> satisfy_on_heap l h0 contains_pred /\ 
                         satisfy_on_heap l h0 is_private /\
                         no_cycles l h0))
    (fun h0 r h1 -> satisfy_on_heap r h1 is_shared) 
    (decreases ll_length l) = 
  match l with
  | LLNil -> ()
  | LLCons x next -> 
    let h0 = get_heap() in 
    assert (h0 `contains` next);
    assert (is_private next h0);
    (* assert(forall_refs_heap is_shared h0 #(SLList SNat) (sel h0 next)); *)
    share next; (* need to share ref starting from the end of the list? *)
    let h1 = get_heap() in
    assert (is_shared next h1);
    (* let h = get_heap() in *)
    let tl = read next in
    (* assert(exists fuel . no_cycles_fuel fuel l h0);
    assert(exists fuel . no_cycles_fuel fuel tl h0); *)
    admit();
    share_llist tl

let rec auto_grader
  (test:list int)
  (hw: student_solution) 
  (gr: mref grade grade_preorder)
  : SST unit
    (requires (fun h0 -> ~(grading_done gr h0))) (*TODO: add precond from paper *)
    (ensures (fun h0 () h1 -> grading_done gr h1 /\
              (forall (a:Type) (rel:FStar.Preorder.preorder a) (r:mref a rel) . 
                h0 `contains` r ==> kind_not_modified r h0 h1) /\ 
                modifies !{gr} h0 h1)) =
    let ll = generate_llist test in
    let ref_ll = sst_alloc_shareable #(SLList SNat) ll in 
    share ref_ll;
    admit();
    share_llist ll;
    (match hw ref_ll with
    | Some _ -> sst_write gr MaxGrade
    | None -> sst_write gr MinGrade)
