module LinkedList

open FStar.Tactics
open FStar.Tactics.Typeclasses
open Labeled.Monotonic.Heap
open Labeled.MST
open FStar.Ghost

open Witnessable
open STLC
open TargetLang
open Translation

module FSet = FStar.FiniteSet.Base

(* Examples of linked lists *)

let empty_ll: linkedList int = Nil

let ll1 () : IST (linkedList int) (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  let r: ref (linkedList int) = ist_alloc #(TLList TNat) Nil in 
  Cons 13 r

let ll2 () : IST (linkedList int) (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  let x = ist_alloc #(TLList TNat) Nil in 
  let y = ist_alloc #(TLList TNat) (Cons 31 x) in
  let z = ist_alloc #(TLList TNat) (Cons 23 y) in
  Cons 23 z

let cycle_length3 () : ST (linkedList int) (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  let x = alloc Nil in 
  let y = alloc (Cons 7 x) in
  let z = alloc (Cons 5 y) in 
  write x (Cons 2 z);
  // let h1 = get() in
  // assume (inv_low_contains h1);
  Cons 2 z


let rec ll_eq (#a: Type0) (fuel: nat) (l1: linkedList a) (l2: linkedList a) (h: lheap) : Type0 =
  if fuel = 0 then False
  else
    match (l1, l2) with
    | (Nil, Nil) -> true
    | Nil, _ -> false
    | _, Nil -> false
    | Cons x xsref, Cons y ysref ->
      let xs = sel h xsref in
      let ys = sel h ysref in  
      x == y /\ ll_eq (fuel - 1) xs ys h

let head_tot (#a: Type0) (l: linkedList a{l =!= Nil}) (h: lheap) : a =
  let Cons x xsref = l in
  x

let head (#a: Type0) (l:linkedList a) : IST (option a)
  (requires fun h -> l =!= Nil)
  (ensures fun h0 head h1 -> h0 == h1 /\ head == Some (head_tot l h1)) =
      match l with
      | Nil -> None
      | Cons x xsref -> Some x

let tail_tot (#a: Type0) (l: linkedList a) (h: lheap) : 
  Pure (linkedList a)
    (requires (Cons? l ==> h `contains` (Cons?.next l)))
    (ensures (fun _ -> True)) = 
  match l with
  | Nil -> Nil
  | Cons x xsref -> sel_tot h xsref

let tail (a: Type0) (l: linkedList a) {| c:witnessable a |} : 
  IST (linkedList a)
    (requires fun h -> satisfy l h contains_pred)
    (ensures (fun h0 xs h1 -> h0 == h1 /\ xs == tail_tot l h0)) = 
  match l with
  | Nil -> Nil
  | Cons x xsref -> 
    let h = get () in
    lemma_sel_equals_sel_tot_for_contained_refs h xsref;
    !xsref

// let rec ll_has_length (#a: Type0) (h: lheap) (l: linkedList a) (len:nat) : Type0 =
//   l == Nil \/ (ll_has_length h (Cons?.next l) (len - 1))

let rec last_elem (t:typ) (l: elab_typ' (TLList t)) : 
  IST (option (elab_typ' t * ref (elab_typ' (TLList t))))
    (requires (fun h -> (elab_typ_tc' (TLList t)).satisfy l h contains_pred))
    (ensures fun h0 _ h1 -> h0 == h1) = 
  let h0 = get () in
  let l : linkedList (elab_typ' t) = l in
  match l with 
  | Nil -> None
  | Cons x xsref ->
    let xs = !xsref in
    match xs with
    | Nil -> Some (x, xsref)
    | Cons _ _ -> 
      eliminate_inv_contains' h0 (TLList t) xsref;
      last_elem t xs

// let insert_front (#a: Type0) (l: linkedList a) (v: a) : 
//   IST (linkedList a)
//     (requires (fun _ -> True))
//     (ensures fun h0 _ h1 -> True) = 
//   let r: ref (linkedList a) = ist_alloc #(TLList TNat) l in 
//   Cons v r

let rec append (#t: typ) (l: elab_typ' (TLList t)) (v: elab_typ' t) :
  ST (elab_typ' (TLList t))
    (requires (fun h -> 
      (elab_typ_tc' (TLList t)).satisfy l h contains_pred /\ 
      inv_points_to h contains_pred))
    (ensures fun _ _ _ -> True) =
  let h0 = get () in
  let l : linkedList (elab_typ' t) = l in
  match l with
  | Nil -> 
    let r = alloc Nil in 
    Cons v r
  | Cons v r -> 
    let tl = !r in
    match tl with
    | Nil -> 
      let newr = alloc Nil in 
      write r (Cons v newr);
      l
    | Cons _ _ -> 
      eliminate_inv_contains' h0 (TLList t) r;
      append tl v

let rec length_IST (t: typ) (l: elab_typ' (TLList t)) : IST int 
    (requires (fun h -> 
      (elab_typ_tc' (TLList t)).satisfy l h contains_pred /\
      inv_points_to h contains_pred))
    (ensures fun _ _ _ -> True) =
  let h0 = get () in
  let l : linkedList (elab_typ' t) = l in
  match l with 
    | Nil -> 0
    | Cons x xsref -> 
      let xs = !xsref in
      eliminate_inv_contains' h0 (TLList t) xsref;
      1 + length_IST t xs

let rec no_cycles_ll (#a: Type0) (fuel: nat) (l: linkedList a) (h: lheap): Type0 =
  if fuel = 0 then False
  else
    match l with
    | Nil -> True
    | Cons x xsref -> no_cycles_ll (fuel - 1) (sel h xsref) h

let rec deep_contains_ll (#a: Type0) (fuel: nat) (l: linkedList a) (h: lheap): Type0 =
  if fuel = 0 then False
  else
    match l with
    | Nil -> True
    | Cons x xsref -> 
      h `contains` xsref /\ deep_contains_ll (fuel - 1) (sel h xsref) h

let rec deep_high_ll (#a: Type0) (fuel: nat) (l: linkedList a) (h: lheap): Type0 =
  if fuel = 0 then False
  else
    match l with
    | Nil -> True
    | Cons x xsref -> 
      label_of xsref h == High /\ deep_high_ll (fuel - 1) (sel h xsref) h

noeq type deep_high_ll_ind (#a: Type0) (h: lheap) : linkedList a -> Type0 =
| DH_Nil: deep_high_ll_ind #a h Nil
| DH_Cons: x:a -> xsref: ref(linkedList a){label_of xsref h == High} ->
    deep_high_ll_ind h (sel h xsref) ->
    deep_high_ll_ind h (Cons x xsref)

noeq type ll_constant_ind (#a: Type0) (h1 h2: lheap) : linkedList a -> Type0 =
| LLC_Nil : ll_constant_ind h1 h2 (Nil #a)
| LLC_Cons_Cons_Cons : v:a ->
    xsref:ref (linkedList a){sel h1 xsref == sel h2 xsref} ->
    ll_constant_ind h1 h2 (sel h1 xsref) ->
    ll_constant_ind h1 h2 (Cons v xsref)

let rec ll_constant (#a: Type0) (fuel: nat) (l: linkedList a) (h1 h2: lheap) : Type0 =
  if fuel = 0 then False
  else
    match l with
    | Nil -> True
    | Cons _ xsref -> begin
      let xs1 = sel h1 xsref in
      let xs2 = sel h2 xsref in
      match (xs1, xs2) with
      | (Nil, Nil) -> True
      | Nil, _ -> False
      | _, Nil -> False
      | (Cons x xsref, Cons y ysref) ->
        x == y /\ xsref == ysref /\ ll_constant (fuel - 1) xs1 h1 h2
    end

let rec ll_same_labels (#a: Type0) (fuel: nat) (l: linkedList a) (h1 h2: lheap) : Type0 =
  if fuel = 0 then False
  else
    match l with
    | Nil -> True
    | Cons _ xsref ->
      let xs = sel h1 xsref in
      label_of xsref h1 == label_of xsref h2 /\ ll_same_labels (fuel - 1) xs h1 h2

let rec lemma_list_unchanged_modif_none0 (#a: Type0) (fuel:nat) (ll: linkedList a) (h0 h1: lheap): Lemma
  (requires modifies_none h0 h1 /\ deep_contains_ll fuel ll h0)
  (ensures ll_constant fuel ll h0 h1)
  (decreases fuel) = 
  match ll with
  | Nil -> ()
  | Cons x xsref -> 
    let xs1 = sel h0 xsref in
    let xs2 = sel h1 xsref in
    assert (modifies Set.empty h0 h1);
    assert (h0 `contains` xsref);
    assert (xs1 == xs2);
    lemma_list_unchanged_modif_none0 (fuel-1) xs1 h0 h1;
    ()

let ll_constant_trans (#a: Type0) (ll: linkedList a) (h0 h1 h2: lheap) : Lemma
  (requires (exists fuel. ll_constant fuel ll h0 h1) /\ (exists fuel. ll_constant fuel ll h1 h2))
  (ensures (exists fuel. ll_constant fuel ll h0 h2)) = admit ()

let lemma_list_unchanged_modif_none (#a: Type0) (ll: linkedList a) (h0 h1: lheap): Lemma
  (requires modifies_none h0 h1 /\ (exists fuel. deep_contains_ll fuel ll h0))
  (ensures exists fuel. ll_constant fuel ll h0 h1)
  = 
  eliminate exists (fuel: nat). 
        deep_contains_ll fuel ll h0
    returns (exists fuel. ll_constant fuel ll h0 h1) with _. begin
    lemma_list_unchanged_modif_none0 fuel ll h0 h1 
  end

let rec lemma_list_unchanged_when_high0 (#a: Type0) (ll: linkedList a) (h0 h1: lheap) (fuel:nat) : Lemma
  (requires (deep_contains_ll fuel ll h0 /\ deep_high_ll fuel ll h0) /\ modifies_only_label Low h0 h1)
  (ensures ll_constant fuel ll h0 h1)
  (decreases fuel) = 
  match ll with
  | Nil -> ()
  | Cons x xsref -> 
    let xs1 = sel h0 xsref in
    let xs2 = sel h1 xsref in
    lemma_list_unchanged_when_high0 xs1 h0 h1 (fuel-1);
    ()

let lemma_list_unchanged_when_high (#a: Type0) (ll: linkedList a) (h0 h1: lheap) : Lemma
  (requires (
    modifies_only_label Low h0 h1 /\
    (exists fuel. deep_contains_ll fuel ll h0 /\ deep_high_ll fuel ll h0)))
  (ensures (exists fuel. ll_constant fuel ll h0 h1)) = 
  eliminate exists (fuel: nat). 
        deep_contains_ll fuel ll h0 /\ 
        deep_high_ll fuel ll h0
    returns (exists fuel. ll_constant fuel ll h0 h1) with _. begin
    lemma_list_unchanged_when_high0 ll h0 h1 fuel
  end

#push-options "--split_queries always"
let rec footprint_acc
  (#a: Type)
  (l: linkedList a) 
  (h:lheap) 
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
#pop-options

let footprint (#a: Type) (l: linkedList a) (h:lheap) : GTot (Set.set nat) =
  let hdom = get_hdom h in
  FSet.all_finite_set_facts_lemma ();
  assert (FSet.emptyset `FSet.subset` hdom);
  let fp : FSet.set nat = footprint_acc l h hdom FSet.emptyset in
  Set.as_set (FSet.set_as_list fp)

let footprint_modifies_none (l:linkedList int) (h0 h1: lheap) : 
  Lemma
    (requires modifies_none h0 h1 /\ satisfy l h0 contains_pred /\ inv_points_to h0 contains_pred)
    (ensures footprint l h0 `Set.equal` footprint l h1) =
  match l with
    | Nil -> ()
    | Cons x xsref -> 
      admit();
      ()

let footprint_acc_cons 
  (l: linkedList int) 
  (h: lheap)
  (hdom:(FSet.set nat){forall (a:Type) (rel:_) (r:mref a rel). h `contains` r ==> addr_of r `FSet.mem` hdom})
  (acc:(FSet.set nat){acc `FSet.subset` hdom}):
Lemma
  (requires Cons? l /\ satisfy l h contains_pred)
  (ensures (
    let next = Cons?.next l in
    FSet.all_finite_set_facts_lemma ();
    let acc' = acc `FSet.union` FSet.singleton (addr_of next) in
    footprint_acc l h hdom acc `FSet.equal`
    (FSet.singleton (addr_of next) `FSet.union` 
    footprint_acc (sel h next) h hdom acc')
  )) =
  admit (); 
  ()

let footprint_cons'
  (l: linkedList int) 
  (h: lheap): Lemma
  (requires Cons? l /\ satisfy l h contains_pred)
  (ensures (
    let next = Cons?.next l in
    let hdom = get_hdom h in
    FSet.all_finite_set_facts_lemma ();
    let acc = FSet.singleton (addr_of next) in
    footprint_acc l h hdom FSet.emptyset `FSet.equal`
    (FSet.singleton (addr_of next) `FSet.union` 
    footprint_acc (sel h next) h hdom acc)
  )) =
  FSet.all_finite_set_facts_lemma ();
  let acc = FSet.singleton (addr_of (Cons?.next l)) in
  let hdom = get_hdom h in
  assert ((FSet.emptyset `FSet.union` acc) `FSet.equal` acc);
  footprint_acc_cons l h hdom FSet.emptyset;
  admit();
  ()

// TODO: this might not be true (footprint starts with the empty set as the acc, but we need 
// to know that the first reference has been visited (and thus that it's in the acc) when 
// writing footprint (sel h0 (Cons?.next l)) h0)) 

let footprint_cons (l:linkedList int) (h0 h1: lheap) :
  Lemma
    (requires (Cons? l /\ satisfy l h0 contains_pred))
    (ensures (
        footprint l h0 `Set.equal` 
        (Set.singleton (addr_of (Cons?.next l)) `Set.union` footprint (sel h0 (Cons?.next l)) h0))) =
  let next  = Cons?.next l in
  let hdom = get_hdom h0 in
  FSet.all_finite_set_facts_lemma (); // gives us that FSet.emptyset `FSet.subset` hdom 
  let fp_l = footprint_acc l h0 hdom FSet.emptyset in
  let acc = FSet.singleton (addr_of next) in
  let fp_next = footprint_acc (sel h0 next) h0 hdom acc in
  footprint_acc_cons l h0 hdom FSet.emptyset;
  assert ((FSet.emptyset `FSet.union` acc) `FSet.equal` acc);
  assert (fp_l `FSet.equal` (acc `FSet.union` fp_next));

  assert (footprint l h0 `Set.equal` Set.as_set (FSet.set_as_list fp_l));
  // assert (footprint (sel h0 (Cons?.next l)) h0 `Set.equal` Set.as_set (FSet.set_as_list fp_next));
  admit ();
  ()
  

let separated (#a: Type) (l1 l2: linkedList a) (h: lheap): Type0 = 
  (footprint l1 h `Set.disjoint` footprint l2 h)

// TODO: this version loops on cycles.
//  should we add a pre-condition or make it work for cycles?
let rec deep_declassify (l: linkedList int) : IST unit 
  (requires fun h -> 
    satisfy l h contains_pred)
  (ensures fun h0 x h1 ->
    modifies Set.empty h0 h1 /\
    modifies_classification (footprint l h0) h0 h1 /\
    satisfy l h1 is_low_pred) =
  let h0 = get() in
  match l with 
  | Nil -> ()
  | Cons h tlref ->
    let tl = !tlref in 
    eliminate_inv_contains' h0 (TLList TNat) tlref;
    deep_declassify tl;
    let h1 = get () in
    declassify_low' #(TLList TNat) tlref;
    let h2 = get () in
    lemma_declassify_preserves_is_low (TLList TNat) tlref h1 h2;
    footprint_modifies_none l h0 h2;
    footprint_cons l h0 h2;
    ()

let test_declassify (l: linkedList int) : IST unit 
  (ensures fun h -> satisfy l h contains_pred) 
  (requires fun _ _ _ -> True) =
  deep_declassify l;
  ()

val progr_llist_declassify: 
  ll: (linkedList int) -> 
  ctx:(elab_typ' (TArr (TLList TNat) TUnit)) ->
  IST unit 
    (requires (fun h0 -> satisfy ll h0 contains_pred))
    (ensures (fun h0 _ h1 -> True))
  
[@expect_failure]
let progr_llist_declassify ll ctx =
  ctx ll (* call should fail because it does not know that ll is low *)

let progr_llist_declassify ll ctx =
  deep_declassify ll;
  ctx ll

val progr_high_ll_unchanged :
  ll: linkedList int -> 
  ctx:(elab_typ' (TArr TUnit TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      satisfy ll h0 contains_pred /\
      (exists (fuel: nat).
        deep_contains_ll fuel ll h0 /\ 
        deep_high_ll fuel ll h0)
    ))
    (ensures (fun h0 _ h1 -> exists (fuel: nat). ll_constant fuel ll h0 h1))
let progr_high_ll_unchanged ll ctx =
  let h0 = get () in
  ctx ();
  let h1 = get() in
  lemma_list_unchanged_when_high ll h0 h1;
  ()

val progr_high_ll_unchanged_separation : 
  ll: linkedList int -> 
  sll: linkedList int ->
  ctx:(elab_typ' (TArr (TLList TNat) TUnit)) ->
  IST unit 
    (requires (fun h0 -> 
      satisfy ll h0 contains_pred /\
      (exists (fuel: nat).
        deep_contains_ll fuel ll h0 /\ 
        deep_high_ll fuel ll h0) /\
      satisfy sll h0 contains_pred /\
      separated ll sll h0))
    (ensures (fun h0 _ h1 ->
      exists (fuel: nat). 
        // deep_high_ll fuel ll h1 /\
        ll_constant fuel ll h0 h1))
let progr_high_ll_unchanged_separation ll sll ctx =
  let h0 = get () in
  deep_declassify sll;
  let h1 = get () in
  assert (exists (fuel: nat).
        deep_contains_ll fuel ll h0 /\ 
        deep_high_ll fuel ll h0);
  assert (separated ll sll h0);
  assume (exists (fuel: nat). ll_same_labels fuel ll h0 h1);
  lemma_list_unchanged_modif_none ll h0 h1;
  assume (exists fuel. deep_contains_ll fuel ll h1 /\ 
                           deep_high_ll fuel ll h1);
  ctx sll;
  let h2 = get() in
  assert (modifies_only_label Low h1 h2);
  lemma_list_unchanged_when_high ll h1 h2;
  ll_constant_trans ll h0 h1 h2;
  ()