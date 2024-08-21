module LinkedListIFC

open FStar.Tactics
open FStar.Tactics.Typeclasses
open Monotonic.IFC.Heap
open IFC.Heap.ST

open STLC
open TargetLangIFC

noeq type linkedList (a: Type0) : Type0 =
    | Nil
    | Cons of a * ref (linkedList a)

instance target_lang_linkedList (t1:Type) {| c1:target_lang t1 |} : target_lang (linkedList t1) = {
  shallowly_contained = (fun l h ->
    match l with
    | Nil -> True
    | Cons (x, xs) -> c1.shallowly_contained x h /\ is_mm xs = false /\ contains_pred xs h); 
  shallowly_low = (fun l h ->
    match l with
    | Nil -> True
    | Cons (x, xs) -> c1.shallowly_low x h /\ is_low_pred xs h);
  shallowly_witness = (fun l ->
    match l with 
    | Nil -> (fun () -> ())
    | Cons (x, xs) ->
      let w = c1.shallowly_witness x in
      gst_witness (contains_pred xs);
      gst_witness (is_low_pred xs);
      (fun () -> w ();
       gst_recall (contains_pred xs);
       gst_recall (is_low_pred xs))
      )
}

// maybe change this to not use IST
let head (a: Type0) (l:linkedList a) {| c1:target_lang a |} : IST (option a)
  (requires (fun h -> shallowly_contained l h))
    (ensures fun _ _ _ -> True) = 
      match l with
      | Nil -> None
      | Cons (x, xsref) -> Some x

let tail (a: Type0) (l: linkedList a) {| c1:target_lang a |} : IST (linkedList a)
    (requires (fun h -> shallowly_contained l h))
    (ensures fun _ _ _ -> True) = 
      match l with
      | Nil -> Nil
      | Cons (x, xsref) -> !xsref

let rec last (#a: Type0) (l:linkedList a) {| c1:target_lang a |} : IST (option a)
  (requires (fun h -> shallowly_contained l h))
  (ensures fun _ _ _ -> True) = 
    let h0 = get() in
    match l with 
    | Nil -> None
    | Cons (x, xsref) ->
      let xs = !xsref in
      match xs with
      | Nil -> Some x
      | Cons _ -> 
        eliminate forall (a:Type) (c:target_lang a) (r':ref a). shallowly_contained r' h0 ==>
          c.shallowly_contained (sel h0 r') h0 with (linkedList a) (solve) xsref;
        last xs #c1

let insert_front (a: Type0) (l: linkedList a) (v: a) {| c:target_lang a |}: ST (linkedList a)
    (requires (fun _ -> True))
    (ensures fun _ _ _ -> True) = 
    let r: ref (linkedList a) = alloc l in 
    Cons (v, r)

// TODO: fix this
// let rec append (a: Type0) (l: linkedList a) (v: a) {| c:target_lang a |}: IST (linkedList a)
//     (requires (fun h -> shallowly_witnessed_contains l /\ shallowly_witnessed_is_low l))
//     (ensures fun _ _ _ -> True) =
//     let h0 = get() in
//     match l with 
//     | Nil -> 
//       let r = alloc Nil in 
//       Cons (v, r)
//     | Cons (v, r) -> 
//       let tl = !r in
//         eliminate forall (a:Type) (c:target_lang a) (r':ref a). witnessed (is_low_pred r') ==>
//         c.shallowly_witnessed_is_low (sel h0 r') with (linkedList a) (solve) r;
//         append a tl v #c

let rec length (a: Type0) (l: linkedList a) {| c:target_lang a |} : IST nat 
       (requires (fun h -> shallowly_contained l h /\ shallowly_low l h))
       (ensures fun _ _ _ -> True) =
       let h0 = get() in
        match l with 
         | Nil -> 0
         | Cons (x, xsref) -> 
           let xs = !xsref in
            eliminate forall (a:Type) (c:target_lang a) (r:ref a). shallowly_low r h0 ==>
              c.shallowly_low (sel h0 r) h0 with (linkedList a) (solve) xsref;
            eliminate forall (a:Type) (c:target_lang a) (r:ref a). shallowly_contained r h0 ==>
              c.shallowly_contained (sel h0 r) h0 with (linkedList a) (solve) xsref;
            1 + length a xs #c

// cycles??
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

let rec ll_constant (#a: Type0) (fuel: nat) (l: linkedList a) (h1 h2: lheap) : Type0 =
  if fuel = 0 then True
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

// examples

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
let rec deep_declassify (l: linkedList int) : ST unit 
  (requires fun h -> shallowly_contained l h /\ inv_contains_points_to_contains h)
  (ensures fun h0 x h1 ->
    inv_contains_points_to_contains h1 /\
    modifies Set.empty h0 h1 /\
    shallowly_low l h1 /\
    (forall (a:Type) (c:target_lang a) (r:ref a). 
    (shallowly_contained r h0 /\ ~(shallowly_low r h0) /\ shallowly_low r h1) ==> c.shallowly_low (sel h1 r) h1)
    ) =
  let h0 = get() in
  match l with 
  | Nil -> ()
  | Cons (h, tlref) ->
      let tl = !tlref in 
      declassify_low' tlref;
      // gst_witness (is_low_pred tlref);
      eliminate forall (a:Type) (c:target_lang a) (r:ref a). shallowly_contained r h0 ==>
        c.shallowly_contained (sel h0 r) h0 with (linkedList int) (solve) tlref;
      let h1 = get () in
      // admit();
      deep_declassify tl;
      // admit();
      let h2 = get () in
      // assert ((forall (a:Type) (c:target_lang a) (r:ref a). h0 `contains` r <==> h1 `contains` r));
      // assert ((forall (a:Type) (c:target_lang a) (r:ref a). 
      //           (h1 `contains` r /\ label_of r h1 <> Low /\ label_of r h2 == Low) ==> 
      //             c.shallowly_low (sel h2 r) h2));


      // assert (modifies_classification (only tlref) h0 h1);
      // assert (modifies Set.empty h0 h2);
      // assert (sel h0 tlref == sel h2 tlref);
      // assert (shallowly_low (sel h2 tlref) h2);
      // assert ((label_of tlref h0 <> Low /\ label_of tlref h2 == Low) ==> 
      //           shallowly_low (sel h2 tlref) h2);   
    
      introduce forall (a:Type) (c:target_lang a) (r:ref a). 
               (shallowly_contained r h0 /\ ~(shallowly_low r h0) /\ shallowly_low r h2) ==> 
                c.shallowly_low (sel h2 r) h2
      with begin
        introduce (shallowly_contained r h0 /\ ~(shallowly_low r h0) /\ shallowly_low r h2) ==> 
                c.shallowly_low (sel h2 r) h2
        with _. begin
          introduce ~(shallowly_low r h1) ==> c.shallowly_low (sel h2 r) h2 with _. ();
          introduce shallowly_low r h1 ==> c.shallowly_low (sel h2 r) h2 with _. begin
            assert (addr_of r = addr_of tlref);
            lemma_sel_same_addr' h2 r tlref;
            assert (shallowly_low (sel h2 tlref) h2);
            assert (sel h2 tlref == sel h2 r);
            // let r : ref (linkedList int) = r in
            let c : target_lang (linkedList int) = c in
            assert ((target_lang_linkedList int).shallowly_low (sel h2 tlref) h2);
            assume ((forall (a:Type) (c:target_lang a) (c':target_lang a) (v:a) . 
              c.shallowly_low v h2 ==> c'.shallowly_low v h2));
            assert (c.shallowly_low (sel h2 tlref) h2);
            assert (c.shallowly_low (sel h2 r) h2);
            ()
          end
        end 
      end;
      ()

  // Tests


// review this later
let test_declassify (l: linkedList int) : IST unit (ensures fun h -> shallowly_contained l h) (requires fun _ _ _ -> True) =
  // deep_declassify l;
  // let h2 = get() in
  // assume ((forall (a:Type) (c:target_lang a) (c':target_lang a) (v:a) . 
  //            c.shallowly_low v h2 ==> c'.shallowly_low v h2));
  ()

val progr_linked_list_unchanged: 
  rp: ref (linkedList int) -> 
  rs: ref int ->
  ctx:(elab_typ (TArr TUnit TUnit)) ->
  IST unit 
    (requires (fun h0 -> 
      shallowly_contained rp h0 /\
      label_of rp h0 == High /\
      shallowly_low rs h0))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp))
         
let progr_secret_unchanged_test rp rs ctx = 
  let x = alloc Nil in 
  let y = alloc (Cons (31, x)) in
  let secret_ll = Cons(23, y) in
  ctx ();
  // assert (head int secret_ll == 31); // how to cast type?
  // assert (head int (tail int secret_ll) == 23);
  ()

// val ctx_HO :
//   elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
// let ctx_HO f =
//   let h0 = get () in
//   let x:ref int = f () in
//   let y = alloc Nil in
//   let z = Cons(!x, y) in
//   let t = insert_front int z 13 in
//   let h2 = get () in
//   assert (modifies_only_label Low h0 h2);
//   ()

// test with program getting callback?


// how to check all labels of a list are High (esp. for cycles?)?
// val progr_sep:
//   rp: linkedList int -> 
//   ctx:(elab_typ (TArr (TRef TNat) TUnit)) ->
//   IST unit
//     (requires (fun h0 -> 
//       shallowly_contained rp h0 /\
//       // label_of (last rp) h0 == High)
//     ))
//     (ensures (fun h0 _ h1 -> True))
// let progr_sep rp f =
//   deep_declassify rp;
//   let h1 = get () in
//   assume (inv_low_points_to_low h1);
//   let r = f rp in  
//   r

// val lemma_list_unchanged_when_high (#a: Type0) (rp: linkedList a) (h0 h1: lheap): Lemma {

// }


let rec deep_high_ll (#a: Type0) (fuel: nat) (l: linkedList a) (h: lheap): Type0 =
  if fuel = 0 then True
  else
    match l with
    | Nil -> True
    | Cons (x, xsref) -> 
      label_of xsref h == High /\ deep_high_ll (fuel - 1) (sel h xsref) h

val progr_ll_unchanged':
  rp: linkedList int -> 
  ctx:(elab_typ (TArr TUnit TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      (forall gas . deep_high_ll gas rp h0) /\
      shallowly_contained rp h0
    ))
    (ensures (fun h0 _ h1 ->  forall gas . ll_constant gas rp h0 h1))
let progr_ll_unchanged' rp f =
  let h1 = get () in
  f ();
  ()