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

//TODO: adapt declassify for cycles
