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
  shallowly_witnessed_contains = (fun x ->
    match x with
    | Nil -> True
    | Cons (h, tl) -> c1.shallowly_witnessed_contains h /\ is_mm tl = false /\ witnessed (contains_pred tl)); 
  shallowly_witnessed_is_low = (fun x ->
    match x with
    | Nil -> True
    | Cons (h, tl) -> c1.shallowly_witnessed_is_low h /\ witnessed (is_low_pred tl));
}

let head (a: Type0) (l:linkedList a) {| c1:target_lang a |} : IST (option a)
  (requires (fun h -> shallowly_witnessed_contains l))
    (ensures fun _ _ _ -> True) = 
      match l with
      | Nil -> None
      | Cons (h, tl) -> Some h

let tail (a: Type0) (l: linkedList a) {| c1:target_lang a |} : IST (linkedList a)
    (requires (fun h -> shallowly_witnessed_contains l))
    (ensures fun _ _ _ -> True) = 
      match l with
      | Nil -> Nil
      | Cons (h, tl) -> !tl

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
       (requires (fun h -> shallowly_witnessed_contains l /\ shallowly_witnessed_is_low l))
       (ensures fun _ _ _ -> True) =
       let h0 = get() in
        match l with 
         | Nil -> 0
         | Cons (h, tlref) -> 
           let tl = !tlref in
            eliminate forall (a:Type) (c:target_lang a) (r:ref a). witnessed (is_low_pred r) ==>
              c.shallowly_witnessed_is_low (sel h0 r) with (linkedList a) (solve) tlref;
            eliminate forall (a:Type) (c:target_lang a) (r:ref a). witnessed (contains_pred r) ==>
              c.shallowly_witnessed_contains (sel h0 r) with (linkedList a) (solve) tlref;
            1 + length a tl #c

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
    gst_witness (contains_pred x);
    write x (Cons(2, z));
    Cons (2, z)


// TODO: clean up
let rec deep_declassify (l: linkedList int) : ST unit 
  (requires fun h -> shallowly_witnessed_contains l /\ inv_contains_points_to_contains h)
  (ensures fun h0 x h1 -> (inv_contains_points_to_contains h1) /\
                           modifies Set.empty h0 h1 /\
                           shallowly_witnessed_is_low l /\
                           (forall (a:Type) (c:target_lang a) (r:ref a). 
                           (h0 `contains` r /\ label_of r h0 <> Low /\ label_of r h1 == Low) ==> c.shallowly_witnessed_is_low (sel h1 r) )
                           ) =
  let h0 = get() in
  match l with 
  | Nil -> ()
  | Cons (h, tlref) ->
    let tl = !tlref in 
      declassify tlref Low;
      gst_witness (is_low_pred tlref);
      eliminate forall (a:Type) (c:target_lang a) (r:ref a). witnessed (contains_pred r) ==>
        c.shallowly_witnessed_contains (sel h0 r) with (linkedList int) (solve) tlref;
      let h1 = get () in
      deep_declassify tl;
      let h2 = get () in
      assert ((forall (a:Type) (c:target_lang a) (r:ref a). h0 `contains` r <==> h1 `contains` r));
      assert ((forall (a:Type) (c:target_lang a) (r:ref a). 
                (h1 `contains` r /\ label_of r h1 <> Low /\ label_of r h2 == Low) ==> 
                  c.shallowly_witnessed_is_low (sel h2 r) ));


      assert (modifies_classification (only tlref) h0 h1);
      assert (modifies Set.empty h0 h2);
      assert (sel h0 tlref == sel h2 tlref);
      assert (shallowly_witnessed_is_low (sel h2 tlref));
      assert ((label_of tlref h0 <> Low /\ label_of tlref h2 == Low) ==> 
                shallowly_witnessed_is_low (sel h2 tlref) );   
    
      introduce forall (a:Type) (c:target_lang a) (r:ref a). 
               (h0 `contains` r /\ label_of r h0 <> Low /\ label_of r h2 == Low) ==> 
                c.shallowly_witnessed_is_low (sel h2 r)
      with begin
        introduce (h0 `contains` r /\ label_of r h0 <> Low /\ label_of r h2 == Low) ==> 
                c.shallowly_witnessed_is_low (sel h2 r)
        with _. begin
          introduce label_of r h1 <> Low ==> c.shallowly_witnessed_is_low (sel h2 r) with _. ();
          introduce label_of r h1 == Low ==> c.shallowly_witnessed_is_low (sel h2 r) with _. begin
            assert (addr_of r = addr_of tlref);
            assume (is_mm r == is_mm tlref);
            lemma_sel_same_addr' h2 r tlref;
            assert (shallowly_witnessed_is_low (sel h2 tlref));
            assert (sel h2 tlref == sel h2 r);
            // let r : ref (linkedList int) = r in
            let c : target_lang (linkedList int) = c in
            assert ((target_lang_linkedList int).shallowly_witnessed_is_low (sel h2 tlref));
            assume ((forall (a:Type) (c:target_lang a) (c':target_lang a) (v:a) . 
              c.shallowly_witnessed_is_low v ==> c'.shallowly_witnessed_is_low v));
            assert (c.shallowly_witnessed_is_low (sel h2 tlref));
            assert (c.shallowly_witnessed_is_low (sel h2 r));
            ()
          end
        end 
      end;
      assert ((forall (a:Type) (c:target_lang a) (r:ref a). 
          (h0 `contains` r /\ label_of r h0 <> Low /\ label_of r h2 == Low) ==> 
          c.shallowly_witnessed_is_low (sel h2 r) ));
      ()

  // let test (l: linkedList int) : IST unit (ensures fun _ -> True) (requires fun _ _ _ -> True) =
  //   deep_declassify l;
  //   ()