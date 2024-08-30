module LinkedListIFC

open FStar.Tactics
open FStar.Tactics.Typeclasses
open Monotonic.IFC.Heap
open IFC.Heap.ST
open FStar.Ghost

open STLC
open TargetLangIFC

module FSet = FStar.FiniteSet.Base

let head_tot (#a: Type0) (l: linkedList a{l =!= Nil}) (h: lheap) {| c: witnessable a |} : a =
  let Cons(x, xsref) = l in
 x

let tail_tot (#a: Type0) (l: linkedList a) (h: lheap) {| c: witnessable a |} : linkedList a = 
    match l with
      | Nil -> Nil
      | Cons (x, xsref) -> 
        assume (satisfy l h contains_pred);
        sel_tot h xsref

let rec ll_eq (#a: Type0) (fuel: nat) (l1: linkedList a) (l2: linkedList a) (h: lheap) : Type0 =
  if fuel = 0 then True
  else
    match (l1, l2) with
    | (Nil, Nil) -> true
    | Nil, _ -> false
    | _, Nil -> false
    | (Cons (x, xsref), Cons (y, ysref)) ->
      let xs = sel h xsref in
      let ys = sel h ysref in  
      x == y /\ ll_eq (fuel - 1) xs ys h

let head (#a: Type0) (l:linkedList a) {| c:witnessable a |} : IST (option a)
  (requires fun h -> l =!= Nil)
  (ensures fun h0 head h1 -> modifies_none h0 h1 /\ head == Some (head_tot l h1)) =
      match l with
      | Nil -> None
      | Cons (x, xsref) -> Some x

let tail (a: Type0) (l: linkedList a) {| c:witnessable a |} : IST (linkedList a)
    (requires fun h -> satisfy l h contains_pred)
    // try to use tail_tot in the postcondition
    (ensures fun h0 xs h1 -> True) = 
      match l with
      | Nil -> Nil
      | Cons (x, xsref) -> !xsref

(* TODO: can we do this for l: linkedlist a? *)
  // let rec last_elem (l: linkedList nat) {| c:witnessable nat |} : IST (option nat)
  // (requires (fun h -> satisfy l h contains_pred))
  // (ensures fun _ _ _ -> True) = 
  //   let h0 = get() in
  //   match l with 
  //   | Nil -> None
  //   | Cons (x, xsref) ->
  //     let xs = !xsref in
  //     match xs with
  //     | Nil -> Some x
  //     | Cons _ -> 
  //       eliminate_inv_contains h0 (TLList TNat) xsref;
  //       last_elem xs #c

// let rec last_ref (#a: Type0) (l:linkedList a{l =!= Nil}) (h: lheap) : GTot (ref (linkedList a)) =
//   let Cons (x, xsref) = l in
//   assume (h `contains` xsref);
//    let xs = sel h xsref in
//    match xs with
//     | Nil -> xsref
//     | Cons _ -> last_ref #a xs h


let insert_front (a: Type0) (l: linkedList a) (v: a) {| c:witnessable a |}: ST (linkedList a)
    (requires (fun _ -> True))
    (ensures fun _ _ _ -> True) = 
    let r: ref (linkedList a) = alloc l in 
    Cons (v, r)

// TODO: fix this
// let rec append (a: Type0) (l: linkedList a) (v: a) {| c:target_lang a |}: IST (linkedList a)
//     (requires (fun h -> shallowly_contained l h /\ shallowly_low l h))
//     (ensures fun _ _ _ -> True) =
//     let h0 = get() in
//     match l with
//     | Nil -> 
//       let r = alloc Nil in 
//       Cons (v, r)
//     | Cons (v, r) -> 
//       let tl = !r in
//         eliminate forall (a:Type) (c:target_lang a) (r':ref a). shallowly_low r' h0 ==>
//         c.shallowly_low (sel h0 r') h0 with (linkedList a) (solve) r;
//         append a tl v #c

// let rec length_IST (a: Type0) (l: linkedList a) {| c:witnessable a |} : IST nat 
//        (requires (fun h -> shallowly_contained_low l h))
//        (ensures fun _ _ _ -> True) =
//        let h0 = get() in
//         match l with 
//          | Nil -> 0
//          | Cons (x, xsref) -> 
//            let xs = !xsref in
//             eliminate forall (a:Type) (c:witnessable a) (r:ref a). satisfy r h0 is_low_pred ==>
//               c.satisfy (sel h0 r) h0 is_low_pred with (linkedList a) (solve) xsref;
//             eliminate forall (a:Type) (c:witnessable a) (r:ref a). satisfy r h0 contains_pred ==>
//               c.satisfy (sel h0 r) h0 contains_pred with (linkedList a) (solve) xsref;
//             1 + length_IST a xs #c

//  let rec length (a: Type0) (l: linkedList a) (h: lheap) {| c:target_lang a |} : nat 
//        // (requires (fun h -> shallowly_contained l h /\ shallowly_low l h))
//        =
//        // let h0 = get() in
//         match l with 
//          | Nil -> 0
//          | Cons (x, xsref) -> 
//            let xs = sel h xsref in
//             // eliminate forall (a:Type) (c:target_lang a) (r:ref a). shallowly_low r h0 ==>
//             //   c.shallowly_low (sel h0 r) h0 with (linkedList a) (solve) xsref;
//             // eliminate forall (a:Type) (c:target_lang a) (r:ref a). shallowly_contained r h0 ==>
//             //   c.shallowly_contained (sel h0 r) h0 with (linkedList a) (solve) xsref;
//             1 + length a xs h #c 

let rec deep_high_ll (#a: Type0) (fuel: nat) (l: linkedList a) (h: lheap): Type0 =
  if fuel = 0 then False
  else
    match l with
    | Nil -> True
    | Cons (x, xsref) -> 
      label_of xsref h == High /\ deep_high_ll (fuel - 1) (sel h xsref) h

noeq type deep_high_ll_ind (#a: Type0) (h: lheap) : linkedList a -> Type0 =
| DH_Nil: deep_high_ll_ind #a h Nil
| DH_Cons: x:a -> xsref: ref(linkedList a){label_of xsref h == High} ->
    deep_high_ll_ind h (sel h xsref) ->
    deep_high_ll_ind h (Cons (x, xsref))

noeq type ll_constant_ind (#a: Type0) (h1 h2: lheap) : linkedList a -> Type0 =
| LLC_Nil : ll_constant_ind h1 h2 (Nil #a)
| LLC_Cons_Cons_Cons : v:a ->
    xsref:ref (linkedList a){sel h1 xsref == sel h2 xsref} ->
    ll_constant_ind h1 h2 (sel h1 xsref) ->
    ll_constant_ind h1 h2 (Cons (v,xsref))

let rec ll_constant (#a: Type0) (fuel: nat) (l: linkedList a) (h1 h2: lheap) : Type0 =
  if fuel = 0 then False
  else
    match l with
    | Nil -> True
    | Cons (_, xsref) -> begin
      let xs1 = sel h1 xsref in
      let xs2 = sel h2 xsref in
      match (xs1, xs2) with
      | (Nil, Nil) -> True
      | Nil, _ -> False
      | _, Nil -> False
      | (Cons (x, xsref), Cons (y, ysref)) ->
        x == y /\ xsref == ysref /\ ll_constant (fuel - 1) xs1 h1 h2
    end


let rec footprint_acc
  (#a: Type)
  (l: linkedList a) 
  (h:lheap) 
  (hdom:(erased (FSet.set pos)){forall (a:Type) (rel:_) (r:mref a rel). h `contains` r ==> addr_of r `FSet.mem` hdom})
  (acc:(erased (FSet.set pos)){acc `FSet.subset` hdom}) : 
  Tot (erased (FSet.set pos)) (decreases (FSet.cardinality (hdom `FSet.difference` acc))) =
  match l with 
  | Nil -> acc
  | Cons (x, xsref) -> 
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

let footprint (#a: Type) (l: linkedList a) (h:lheap) =
  let hdom = get_hdom h in
  assume (FSet.emptyset `FSet.subset` hdom);
  footprint_acc l h hdom FSet.emptyset

let separated (#a: Type) (l1 l2: linkedList a) (h: lheap): Type0 = 
  (footprint l1 h `FSet.intersection` footprint l2 h) == FSet.emptyset

(* Examples of linked lists *)

let empty_ll: linkedList nat = Nil

let ll1 () : ST (linkedList nat) (requires fun _ -> True) (ensures fun _ _ _ -> True) =
     let r: ref(linkedList nat) = alloc Nil in 
     Cons (13, r)

let ll2 () : ST (linkedList nat) (requires fun _ -> True) (ensures fun _ _ _ -> True) =
     let x = alloc Nil in 
     let y = alloc (Cons (31, x)) in
     let z = alloc (Cons (23, y)) in
     Cons(23, z)

let cycle_length3 () : ST (linkedList nat) (requires fun _ -> True) (ensures fun _ _ _ -> True) =
    let x = alloc Nil in 
    let y = alloc (Cons (7, x)) in
    let z = alloc (Cons (5, y)) in 
    // gst_witness (contains_pred x);
    write x (Cons(2, z));
    Cons (2, z)


// TODO: clean up
// let rec deep_declassify (l: linkedList int) : ST unit 
//   (requires fun h -> satisfy l h contains_pred /\ inv_contains_points_to_contains h)
//   (ensures fun h0 x h1 ->
//     inv_contains_points_to_contains h1 /\
//     modifies Set.empty h0 h1 /\
//     (* TODO: modifies_classification (footprint l) h0 h1 *)
//     satisfy l h1 is_low_pred /\
//     (forall (a:Type) (c:witnessable a) (r:ref a). 
//     (~(satisfy r h0 is_low_pred) /\ satisfy r h1 is_low_pred) ==> c.satisfy (sel h1 r) h1 is_low_pred)
//     ) =
//   let h0 = get() in
//   match l with 
//   | Nil -> ()
//   | Cons (h, tlref) ->
//       let tl = !tlref in 
//       declassify_low' tlref;
//       eliminate forall (a:Type) (c:witnessable a) (r:ref a). satisfy r h0 contains_pred ==>
//         c.satisfy (sel h0 r) h0 contains_pred with (linkedList int) (solve) tlref;
//       let h1 = get () in
//       deep_declassify tl;
//       let h2 = get () in
//       introduce forall (a:Type) (c:witnessable a) (r:ref a). 
//                (~(satisfy r h0 is_low_pred) /\ satisfy r h2 is_low_pred) ==> 
//                 c.satisfy (sel h2 r) h2 is_low_pred
//       with begin
//         introduce (~(satisfy r h0 is_low_pred) /\ satisfy r h2 is_low_pred) ==> 
//                 c.satisfy (sel h2 r) h2 is_low_pred
//         with _. begin
//           introduce ~(satisfy r h1 is_low_pred) ==> c.satisfy (sel h2 r) h2 is_low_pred with _. ();
//           introduce satisfy r h1 is_low_pred ==> c.satisfy (sel h2 r) h2 is_low_pred with _. begin
//             assert (addr_of r = addr_of tlref);
//             assume (is_mm r = is_mm tlref);
//             lemma_sel_same_addr' h2 r tlref;
//             // assert (shallowly_low (sel h2 tlref) h2);
//             // assert (sel h2 tlref == sel h2 r);
//             let c : witnessable (linkedList int) = c in
//             assert ((target_lang_linkedList int).satisfy (sel h2 tlref) h2 is_low_pred);
//             assume ((forall (a:Type) (c:witnessable a) (c':witnessable a) (v:a) . 
//               c.satisfy v h2 is_low_pred ==> c'.satisfy v h2 is_low_pred));
//             assert (c.satisfy (sel h2 tlref) h2 is_low_pred);
//             ()
//           end
//         end 
//       end;
//       ()

// (* Tests *)

// // TODO: Review this
// let test_declassify (l: linkedList int) : IST unit 
//   (ensures fun h -> shallowly_contained l h) 
//   (requires fun _ _ _ -> True) =
//   let h0 = get() in
//   deep_declassify l;
//   let h1 = get() in
//   // assume ((forall (a:Type) (c:target_lang a) (c':target_lang a) (v:a) . 
//   //   (target_lang_ref a #c).shallowly_low v h1 ==> c'.shallowly_low v h1));

//   assert (modifies Set.empty h0 h1);
//   assert (shallowly_contained l h0);
//   assert (shallowly_contained l h1);
//   assert (inv_contains_points_to_contains h1);

//   assert (shallowly_low l h1);
//   assert (inv_low_points_to_low h0); // by IST

//   introduce forall (a:Type) (c:target_lang a) (r:ref a).
//     shallowly_low r h1 ==> c.shallowly_low (sel h1 r) h1
//   with begin
//     introduce shallowly_low r h1 ==> c.shallowly_low (sel h1 r) h1 with _. begin
//       introduce shallowly_low r h0 ==> c.shallowly_low (sel h1 r) h1 with _. begin
//         assert (h0 `contains` r);
//         assert (modifies_none h0 h1);
//         assert (sel h1 r == sel h0 r);
//         assert (shallowly_low r h0 ==> c.shallowly_low (sel h0 r) h0);
//         lemma (sel h1 r) h0 h1;
//         // assume (shallowly_low (sel h1 r) h0 ==> shallowly_low (sel h1 r) h1);
//         ()
//       end;
//       introduce ~(shallowly_low r h0) ==> c.shallowly_low (sel h1 r) h1 with _. begin
//         assert
//           ((~(shallowly_low r h0) /\ shallowly_low r h1) ==> c.shallowly_low (sel h1 r) h1);
//         assert (~(shallowly_low r h0));
//         assert (shallowly_low r h1);
//         ()
//       end
//     end
//   end;

//   assert (inv_low_points_to_low h1);
//   ()

// let test2_declassify (l1 l2: linkedList int) : IST unit 
//   (ensures fun h -> shallowly_contained l1 h /\ shallowly_contained l2 h /\ deep_high_ll l2 h) 
//   (requires fun _ _ h1 -> deep_high_ll l2 h1) =
//   deep_declassify l1;


// // val progr_linked_list_unchanged: 
// //   rp: ref (linkedList int) -> 
// //   rs: ref int ->
// //   ctx:(elab_typ (TArr TUnit TUnit)) ->
// //   IST unit 
// //     (requires (fun h0 -> 
// //       shallowly_contained rp h0 /\
// //       label_of rp h0 == High /\
// //       shallowly_low rs h0))
// //     (ensures (fun h0 _ h1 ->
// //       sel h0 rp == sel h1 rp))
         
// // let progr_secret_unchanged_test rp rs ctx = 
// //   let x = alloc Nil in 
// //   let y = alloc (Cons (31, x)) in
// //   let secret_ll = Cons(23, y) in
// //   ctx ();
// //   let h = get() in
// //   assert (head int secret_ll h == 31);
// //   // assert (head int (tail int secret_ll) == 23);
// //   ()

// // val ctx_HO :
// //   elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
// // let ctx_HO f =
// //   let h0 = get () in
// //   let x:ref int = f () in
// //   let y = alloc Nil in
// //   let z = Cons(!x, y) in
// //   let t = insert_front int z 13 in
// //   let h2 = get () in
// //   assert (modifies_only_label Low h0 h2);
// //   ()

// // test with program getting callback?

// // val progr_sep:
// //   rp: linkedList int -> 
// //   ctx:(elab_typ (TArr (TRef TNat) TUnit)) ->
// //   IST unit
// //     (requires (fun h0 -> 
// //       shallowly_contained rp h0 /\
// //       label_of (last rp) h0 == High)
// //     )
// //     (ensures (fun h0 _ h1 -> True))
// // let progr_sep rp f =
// //   deep_declassify rp;
// //   let h1 = get () in
// //   assume (inv_low_points_to_low h1);
// //   let r = f rp in  
// //   r

// // add precond of not cycles
// let rec lemma_list_unchanged_modif_none (#a: Type0) (rp: linkedList a) (h0 h1: lheap): Lemma
//   (requires modifies_none h0 h1)
//   (ensures exists (gas:nat) . ll_constant gas rp h0 h1)
//   (decreases rp) = 
//   match rp with
//   | Nil ->
//     assert (ll_constant 1 rp h0 h1);
//     ()
//   | Cons (x, xsref) -> 
//     let xs1 = sel h0 xsref in
//     let xs2 = sel h1 xsref in
//     assert (modifies Set.empty h0 h1);
//     assume (h0 `contains` xsref);
//     assert (xs1 == xs2);
//     admit();
//     lemma_list_unchanged_modif_none xs1 h0 h1;
//     ()

// let lemma_list_unchanged_when_high (#a: Type0) (rp: linkedList a) (h0 h1: lheap): Lemma
//   (requires (exists (gas: nat). deep_high_ll gas rp h0 /\ modifies_only_label Low h0 h1))
//   (ensures exists (gas: nat). ll_constant gas rp h0 h1)
//   (decreases rp) = 
//   match rp with
//   | Nil ->
//     assert (ll_constant 1 rp h0 h1);
//     ()
//   | Cons (x, xsref) -> 
//     let xs1 = sel h0 xsref in
//     let xs2 = sel h1 xsref in
//     // assert (modifies Set.empty h0 h1);
//     // assume (h0 `contains` xsref);
//     // assert (xs1 == xs2);
//     admit();
//     // lemma_list_unchanged_modif_none xs1 h0 h1;
//     ()

// val progr_ll_unchanged':
//   rp: linkedList int -> 
//   ctx:(elab_typ (TArr TUnit TUnit)) ->
//   IST unit
//     (requires (fun h0 -> 
//       exists (gas: nat) . deep_high_ll gas rp h0 /\
//       shallowly_contained rp h0
//     ))
//     (ensures (fun h0 _ h1 -> exists (gas: nat). ll_constant gas rp h0 h1))
// let progr_ll_unchanged' rp f =
//   let h0 = get () in
//   f ();
//   let h1 = get() in
//   lemma_list_unchanged_when_high rp h0 h1;
//   ()

// // val ctx_alloc_ll: int -> St linked // take pre/post from elab_typ
// // elab_typ (TArr TNat (TPair TNat (TRef TNat)))
// // let ctx_alloc_ll v =
// //   let r = alloc Nil in 
// //   let rs = Cons(v, r) in
// //   rs

// // val progr_passes_cb:
// //   rp: linkedList int ->
// //   ctx: (elab_typ (TArr (TArr TUnit TUnit) TUnit)) ->
// //   IST unit 
// //     (requires fun h0 -> 
// //       shallowly_contained rp h0 /\ 
// //       (exists (gas: nat) . deep_high_ll gas rp h0))
// //     (ensures fun _ _  h1 -> inv_low_points_to_low h1)
// // let progr_getting_callback_test rp ctx = 
// //   declassify_low' (last_ref rp); // this shouldn't be necessary (the cb of the program should be able to modify High things)
// //   let cb: elab_typ (TArr TUnit TUnit) = 
// //     (fun () -> 
// //       let last_of_ll = last rp in
// //       write' last_of_ll (!last_of_ll + 1)) in
// //   ctx cb;
// //   ()
    