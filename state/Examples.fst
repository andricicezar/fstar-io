module Examples

open FStar.Preorder
open FStar.Tactics.Typeclasses
open FStar.FiniteSet.Base
open SharedRefs
open Witnessable

open FStar.Tactics
open FStar.Ghost

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

(* TODO: two implementations of each : one with Type0 (pred) & one for HO contracts (ST effect) *)

let no_cycles (ll: linkedList int) (h: heap) : Type0 = admit()
let sorted (ll: linkedList int) (h: heap) : Type0 = admit()

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

(* #push-options "--split_queries always"
let rec footprint_acc
  (#a: Type)
  (l: linkedList a)
  (h:heap)
  (hdom:(FSet.set nat){forall (a:Type) (rel:_) (r:mref a rel). h `contains` r ==> addr_of r `FSet.mem` hdom})
  (acc:(FSet.set nat){acc `FSet.subset` hdom}) :
  GTot (FSet.set nat) (decreases (FSet.cardinality (hdom `FSet.difference` acc))) =
  match l with
  | Nil -> acc
  | Cons x xsref ->
    if addr_of xsref `FSet.mem` acc then acc
    else begin
      assume (h `contains` xsref);
      let acc' = (acc `FSet.union` FSet.singleton (addr_of xsref)) in
      FSet.all_finite_set_facts_lemma ();
      assert (acc' `FSet.subset` hdom);
      assert ((hdom `FSet.difference` acc') `FSet.subset`
              (hdom `FSet.difference` acc));
      assert (~((hdom `FSet.difference` acc') `FSet.equal`
              (hdom `FSet.difference` acc)));
      assert (FSet.cardinality (hdom `FSet.difference` acc') <
              FSet.cardinality (hdom `FSet.difference` acc));
      footprint_acc (sel h xsref) h hdom acc'
    end
#pop-options *)

let elements_of_ll (ll:linkedList int) (h:heap) : Set.set int = admit()
(* elements_of_ll_acc ll h Set.empty *)

let same_elements (ll:linkedList int) (h0 h1:heap) = elements_of_ll ll h0 == elements_of_ll ll h1

type student_solution =
  ll:linkedList int -> SST (option unit)
    (requires (fun h0 ->
      no_cycles ll h0 /\
      forall_refs_heap contains_pred h0 #(SLList SNat) ll /\ forall_refs_heap is_shared h0 #(SLList SNat) ll))
    (ensures (fun h0 r h1 ->
      (Some? r ==> no_cycles ll h1 /\ sorted ll h1 /\ same_elements ll h0 h1) /\
      modifies_only_shared h0 h1 /\ gets_shared Set.empty h0 h1))

let wss : witnessable (list (mref grade grade_preorder * student_solution)) = admit ()
(*  witnessable_list (witnessable_pair (witnessable_mref witnessable_grade grade_preorder) witnessable_llist) *)

let rec grading_done (sts: list (mref grade grade_preorder * student_solution)) h =
  match sts with
  | [] -> True
  | hd::tl -> sel h (fst hd) =!= NotGraded /\ grading_done tl h

(* TODO: add specs (one postcond should be no cycles) *)
let rec generate_llist (l:list int)
  : SST (linkedList int)
    (requires (fun h0 -> True))
    (ensures (fun h0 r h1 -> satisfy_on_heap r h1 contains_pred)) =
  match l with
  | [] -> LLNil
  | hd::tl -> LLCons hd (sst_alloc #(SLList SNat) (generate_llist tl)) (* sst_alloc or sst_alloc'? *)

let rec deep_contains_ll (fuel: nat) (l: linkedList int) (h: heap): Type0 =
  if fuel = 0 then False
  else
    match l with
    | LLNil -> True
    | LLCons x xsref -> 
      h `contains` xsref /\ deep_contains_ll (fuel - 1) (sel h xsref) h  

let rec share_llist (l:linkedList int) 
  : SST unit 
    (requires (fun h0 -> (exists fuel . deep_contains_ll fuel l h0)))
    (fun h0 r h1 -> True) = 
  match l with
  | LLNil -> ()
  | LLCons x next -> 
    let h0 = get_heap() in 
    assert (h0 `contains` next);
    sst_share #(SRef (SLList SNat)) next;
    (* let h = get_heap() in *)
    let tl = read next in
    share_llist tl

let rec auto_grader
  (l:list int)
  (sts: list (mref grade grade_preorder * student_solution))
  : SST unit
    (requires (fun h0 -> wss.satisfy_on_heap sts h0 (fun r h0 -> ~(is_shared r h0))))
    (ensures (fun h0 () h1 ->
      wss.satisfy_on_heap sts h1 (fun r h0 -> ~(is_shared r h0)) /\
      grading_done sts h1
      )) =
  match sts with
  | [] -> ()
  | (gr, hw)::tl -> begin
    let ll = generate_llist l in
    share_llist ll;
    admit ();
    (match hw ll with
    | Some _ -> sst_write'' gr MaxGrade
    | None -> sst_write'' gr MinGrade);
    auto_grader l tl
  end
