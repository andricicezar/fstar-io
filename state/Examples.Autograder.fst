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

noextract
instance witnessable_grade : witnessable grade = {
  satisfy = (fun _ _ -> True);
}

let grade_preorder : preorder grade = fun g1 g2 ->
  match g1 with
  | NotGraded -> True
  | _ -> g1 == g2

let max_fuel = pow2 32 - 1

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

let heap_contains_all_refs_of_ll (l: linkedList int) (h: heap): Lemma
  (requires satisfy_on_heap l h contains_pred)
  (ensures l == LLNil \/ satisfy_on_heap (sel h (LLCons?.next l)) h contains_pred) = admit()

(* Probably there are built in functions for these in ulib? *)
let rec search_elem_with_first_comp (v: int) (l: list (int * int)): option (int * int) =
  match l with
  | [] -> None
  | hd::tl ->
    if fst hd = v then Some hd
    else search_elem_with_first_comp v tl

let rec elements_of_ll_acc
  (fuel:nat)
  (ll:linkedList int)
  (h:heap)
  (acc: FSet.set (int * int)) : GTot (FSet.set (int * int)) =
  if fuel = 0 then acc
  else
    match ll with
    | LLNil -> acc
    | LLCons v next ->
        let w = search_elem_with_first_comp v (set_as_list acc) in
        let acc' =
        match w with
        | None -> acc `union` FSet.singleton(v, 1)
        | Some (v, m) -> ((v, m) `remove` acc) `union` singleton(v, m+1)
        in let tail = sel h next in
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
  (ensures fun h0 r h1 -> h0 == h1 /\ (r ==> no_cycles ll h0)) = (* ==> instead of <==> because this version uses fuel *)
  if fuel = 0 then false
  else
    match ll with
      | LLNil -> true
      | LLCons x xsref ->
        let h0 = get_heap() in
        assert (h0 `contains` xsref);
        let tail : linkedList int = sst_read xsref in
        let h1 = get_heap() in
        assert (h0 == h1);
        assume (satisfy_on_heap (sel h0 xsref) h0 contains_pred); (* add lemma for this *)
        admit(); (* second postcond fails *)
        no_cycles_SST (fuel - 1) tail

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

// let same_elements_SST (ll: linkedList int): SST bool
//   (requires fun h0 -> satisfy_on_heap ll h0 contains_pred)
//   (ensures fun h0 r h1 -> r ==> same_elements ll h0 h1)
//   = admit()

type student_solution =
  ll_ref:ref(linkedList int) -> SST (option unit)
    (requires (fun h0 ->
      //no_cycles (sel h0 ll_ref) h0 /\
      forall_refs_heap contains_pred h0 #(SRef (SLList SNat)) ll_ref /\
      forall_refs_heap is_shared h0 #(SRef (SLList SNat)) ll_ref))
    (ensures (fun h0 r h1 ->
      (Some? r ==> no_cycles (sel h1 ll_ref) h1 /\ sorted (sel h1 ll_ref) h1 /\ same_elements (sel h1 ll_ref) h0 h1) /\
      modifies_only_shared h0 h1 /\
      gets_shared Set.empty h0 h1))

// let wss : witnessable (list (mref grade grade_preorder * student_solution)) = admit ()
(*  witnessable_list (witnessable_pair (witnessable_mref witnessable_grade grade_preorder) witnessable_llist) *)

let grading_done (gr: mref grade grade_preorder) h = sel h gr =!= NotGraded

(* TODO: add specs (one postcond should be no cycles) *)
let rec generate_llist (l:list int)
  : SST (linkedList int)
    (requires (fun h0 -> True))
    (ensures (fun h0 r h1 -> forall_refs_heap contains_pred h1 #(SLList SNat) r /\
                          forall_refs_heap is_shared h1 #(SLList SNat) r /\
                          modifies !{map_shared} h0 h1
                  (* /\ exists fuel . no_cycles_fuel fuel r h1 *)
                  )) =
  match l with
  | [] -> LLNil
  | hd::tl ->
      let ll = generate_llist tl in
      let ll_ref = sst_alloc_shareable #(SLList SNat) ll in
      sst_share ll_ref;
      LLCons hd ll_ref

#push-options "--z3rlimit 10000"
let auto_grader
  (test:list int)
  (hw: student_solution)
  (gr: mref grade grade_preorder)
  : SST unit
    (requires (fun h0 -> ~(grading_done gr h0) /\
                      ~(compare_addrs gr map_shared) /\
                      is_private gr h0 /\
                      h0 `contains` gr /\
                      NotGraded? (sel h0 gr)))
    (ensures (fun h0 () h1 -> grading_done gr h1 /\
               modifies_shared_and h0 h1 !{gr})) =
    let ll = generate_llist test in
    let ref_ll = sst_alloc_shareable #(SLList SNat) ll in
    sst_share ref_ll;
    let h0 = get_heap () in
    (match hw ref_ll with
    | Some _ ->
        let h1 = get_heap () in
        assume (NotGraded? (sel h1 gr));
        assume (h1 `contains` gr);
        assume ((forall t. to_Type t == grade ==>
          forall_refs_heap contains_pred h1 #t MaxGrade /\
          (is_shared gr h1 ==> forall_refs_heap is_shared h1 #t MaxGrade)));
        //admit ();
        sst_write gr MaxGrade (** DA: Puzzled. All the pre-conditions of sst_write are assumed here, but still fails. *)
    | None ->
        admit ();
        sst_write gr MinGrade)
#pop-options

let test1 () : STATEwp grade AllOps (fun _ _ -> False) =
  let test = [1;3;4;2;1] in
  let gr = alloc (NotGraded) in
  auto_grader test solution gr;
  !gr
