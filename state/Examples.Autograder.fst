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

let max_fuel = pow2 32 - 1

(* TODO: two implementations of each : one with Type0 (pred) & one for HO contracts (ST effect) *)
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

let footprint (l: ref (linkedList int)) (h:heap) : (GTot (FSet.set nat)) =
  let hdom = get_heap_domain h in
  FSet.all_finite_set_facts_lemma ();
  assert (FSet.emptyset `FSet.subset` hdom);
  assume (forall (a:Type) (rel:_) (r:mref a rel). h `contains` r ==> addr_of r `FSet.mem` hdom);
  assume (h `contains` l);
  footprint_acc (sel h l) h hdom (FSet.singleton (addr_of l))

let ll_length (ll: ref (linkedList int)) (h: heap): GTot int =
  cardinality (footprint ll h)

let no_cycles (ll:ref (linkedList int)) (h:heap): Type0 =
  exists (fuel:nat). no_cycles_fuel fuel ll h

let sorted (ll: ref (linkedList int)) (h:heap): Type0 =
  exists fuel. sorted_fuel fuel (sel h ll) h

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

(**
let same_elements (ll:ref (linkedList int)) (h0 h1:heap): Type0 =
  let length_h0 = ll_length ll h0 in
  let length_h1 = ll_length ll h1 in
  if length_h0 <> length_h1 then False
  else
    exists fuel. elements_of_ll_acc fuel ll h0 FSet.emptyset == elements_of_ll_acc fuel ll h0 FSet.emptyset

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
**)
// let same_elements_SST (ll: linkedList int): SST bool
//   (requires fun h0 -> satisfy_on_heap ll h0 contains_pred)
//   (ensures fun h0 r h1 -> r ==> same_elements ll h0 h1)
//   = admit()

type student_solution =
  ll_ref:ref(linkedList int) -> SST (option unit)
    (requires (fun h0 ->
      //no_cycles (sel h0 ll_ref) h0 /\
      h0 `contains` ll_ref /\
      is_shared ll_ref h0))
    (ensures (fun h0 r h1 ->
      (Some? r ==> no_cycles ll_ref h1 /\ sorted ll_ref h1) /\ // /\ same_elements (sel h1 ll_ref) h0 h1) /\
      modifies_only_shared h0 h1 /\
      gets_shared Set.empty h0 h1))
// let wss : witnessable (list (mref grade grade_preorder * student_solution)) = admit ()
(*  witnessable_list (witnessable_pair (witnessable_mref witnessable_grade grade_preorder) witnessable_llist) *)

  (**
let rec no_cycles_acc (l:ref (linkedList int)) (h:heap) (s:set nat) : Type0 =
  (addr_of l `Set.mem` s ==> False) /\
  (~(addr_of l `Set.mem` s) ==> (
    match (sel h l) with
    | LLNil -> True
    | LLCons _ tl -> no_cycles_acc tl h (s `Set.union` !{l})
  ))**)

let rec footprint_fuel (fuel:nat) (ll:ref (linkedList int)) (h:heap) : GTot (Set.set nat) =
  if fuel = 0 then Set.empty else (
  !{ll} `Set.union` (
    match sel h ll with
    | LLNil -> Set.empty
    | LLCons _ tl -> footprint_fuel (fuel-1) tl h)
  )

let rec refs_of_ll (fuel:nat) (ll:ref (linkedList int)) (h:heap) : GTot (list (ref (linkedList int))) =
  ll :: (
    match sel h ll with
    | LLNil -> []
    | LLCons _ tl -> if fuel = 0 then [] else refs_of_ll (fuel-1) tl h)

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
                          pred_ll (length l) ll h1 (fun r -> fresh r h0 h1) /\
                          pred_ll (length l) ll h1 (fun r -> is_private r h1))) =
  let h0 = get_heap () in
  match l with
  | [] -> sst_alloc LLNil
  | hd::tl ->
    let tll = generate_llist tl in
    let h1 = get_heap () in
    let ll = sst_alloc (LLCons hd tll) in
    let h2 = get_heap () in
    assume (pred_ll (length tl) tll h2 (fun r -> fresh r h0 h2));
    assume (pred_ll (length tl) tll h2 (fun r -> is_private r h2));
    assume (no_cycles tll h2);
    assume (no_cycles_fuel (length tl) tll h2);
    assert (no_cycles_fuel (length l) ll h2);
    ll

let rec label_llist_as_shareable_fuel (fuel:erased nat) (ll:ref (linkedList int))
  : SST unit
    (requires (fun h0 -> h0 `contains` ll /\
                      no_cycles_fuel fuel ll h0 /\
                      pred_ll fuel ll h0 (fun r -> is_private r h0)
                      ))
    (ensures (fun h0 _ h1 -> modifies !{map_shared} h0 h1 /\
                          equal_dom h0 h1 /\
                          gets_shared (refs_of_ll_as_set fuel ll h1) h0 h1 /\
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
  assume (gets_shared (refs_of_ll_as_set fuel ll h2) h0 h2)

let rec determine_fuel_fuel (ll:ref (linkedList int)) (ffuel:nat)
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
      match determine_fuel_fuel tl (ffuel-1) with
      | None -> None
      | Some fuel -> Some (fuel + 1)
    end

let label_llist_as_shareable (ll:ref (linkedList int)) (fuel:nat)
  : SST unit
    (requires (fun h0 -> h0 `contains` ll /\
                      no_cycles_fuel fuel ll h0 /\
                      pred_ll fuel ll h0 (fun r -> is_private r h0)))
    (ensures (fun h0 _ h1 -> modifies !{map_shared} h0 h1 /\
                          gets_shared (refs_of_ll_as_set fuel ll h1) h0 h1 /\
                          equal_dom h0 h1 /\
                          is_shared ll h1))
= let h0 = get_heap () in
  label_llist_as_shareable_fuel fuel ll

(** TODO: can we add SMTPat to these? **)
let lemma_modifies_shared_and h0 h1 h2 s :
  Lemma (requires (modifies s h0 h1 /\ modifies_only_shared h1 h2))
        (ensures (modifies_shared_and h0 h2 s)) = admit ()

let lemma_modifies_shared_and' h0 h1 h2 s s' :
  Lemma (requires (modifies_shared_and h0 h1 s /\ modifies s' h1 h2))
        (ensures (modifies_shared_and h0 h2 (s `Set.union` s'))) = admit ()

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
    let ll = generate_llist test in
    label_llist_as_shareable ll (length test);
    let h1 = get_heap () in
    assume (~(addr_of gr `Set.mem` (refs_of_ll_as_set (length test) ll h1)));
    assert (is_private gr h1);
    match hw ll with
    | Some _ -> begin
      let h2 = get_heap () in
      sst_write #grade gr MaxGrade;
      let h3 = get_heap () in
      lemma_modifies_shared_and h0 h1 h2 !{map_shared};
      lemma_modifies_shared_and' h1 h2 h3 !{map_shared} !{gr};
      assert (modifies_shared_and h0 h3 !{gr})
    end
    | None -> begin
      let h2 = get_heap () in
      sst_write gr MinGrade;
      let h3 = get_heap () in
      lemma_modifies_shared_and h0 h1 h2 !{map_shared};
      lemma_modifies_shared_and' h1 h2 h3 !{map_shared} !{gr};
      assert (modifies_shared_and h0 h3 !{gr})
    end

let test1 () : STATEwp grade AllOps (fun _ _ -> False) =
  let test = [1;3;4;2;1] in
  let gr : mref grade grade_preorder = alloc (NotGraded) in
 // auto_grader test solution gr;
  !gr
