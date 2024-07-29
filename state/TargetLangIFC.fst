module TargetLangIFC

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses

open Monotonic.IFC.Heap
open IFC.Heap.ST

(** target_lang is a shallow embedding of STLC **)
class target_lang (t:Type) = {
  deep_contains : lheap -> t -> Type0;
  deeply_labeled : t -> lheap -> label -> Type0; (** deep check of the lebel of a value **)
  deep_recall : (r:t) -> ST unit 
              (requires (fun h -> True))
              (ensures  (fun h0 _ h1 -> h0 == h1 /\ h1 `deep_contains` r));
  deep_declassify : (r:t) -> l:label -> ST unit 
              (requires (fun h0 -> exists l0. deeply_labeled r h0 l0 /\ l0 `lattice_gte` l)) (* TODO: this does not work at all with loops *)
              (ensures  (fun h0 _ h1 -> 
                modifies_none h0 h1 /\
                equal_dom h0 h1 /\
                deeply_labeled r h1 l));
}

instance target_lang_unit : target_lang unit = {
  deep_contains = (fun _ _ -> True);
  deeply_labeled = (fun _ _ _ -> True);
  deep_recall = (fun _ -> ());
  deep_declassify = (fun _ _ -> ())
}

instance target_lang_int : target_lang int = {
  deep_contains = (fun _ _ -> True);
  deeply_labeled = (fun _ _ _ -> True);
  deep_recall = (fun _ -> ());
  deep_declassify = (fun _ _ -> ())
}

instance target_lang_pair (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (t1 * t2) = {
  deep_contains = (fun h (x1, x2) -> h `deep_contains` x1 /\ h `deep_contains` x2);
  deeply_labeled = (fun (x1, x2) h l -> c1.deeply_labeled x1 h l /\ c2.deeply_labeled x2 h l);
  deep_recall = (fun (x1, x2) -> c1.deep_recall x1; c2.deep_recall x2);
  deep_declassify = (fun (x1, x2) l -> 
    c1.deep_declassify x1 l; 
    admit ();
    c2.deep_declassify x2 l)
}

instance target_lang_sum (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (either t1 t2) = {
  deep_contains = (fun h x ->
    match x with
    | Inl x1 -> h `deep_contains` x1
    | Inr x2 -> h `deep_contains` x2);
  deeply_labeled = (fun x h l ->
    match x with
    | Inl x1 -> c1.deeply_labeled x1 h l
    | Inr x2 -> c2.deeply_labeled x2 h l);
  deep_recall = (fun x ->
    match x with
    | Inl x1 -> c1.deep_recall x1
    | Inr x2 -> c2.deep_recall x2);
  deep_declassify = (fun x l ->
    match x with
    | Inl x1 -> c1.deep_declassify x1 l
    | Inr x2 -> c2.deep_declassify x2 l)
}

instance target_lang_ref (t:Type) {| c:target_lang t |} : target_lang (ref t) = {
  deep_contains = (fun h (x:ref t) -> h `contains` x /\ h `deep_contains` (sel h x));
  deeply_labeled = (fun (x:ref t) h l -> label_of x h == l /\ c.deeply_labeled (sel h x) h l);  
  deep_recall = (fun (x:ref t) -> recall x; c.deep_recall !x);
  deep_declassify = (fun (x:ref t) l -> 
    declassify x l; 
    admit ();
    c.deep_declassify !x l
  )
}

let modifies_only_label (l:label) (h0:lheap) (h1:lheap) : Type0 =
  (forall (a:Type) (r:ref a). h0 `contains` r /\ label_of r h0 =!= l ==>
          sel h0 r == sel h1 r)

let objects_deeply_labeled (h:lheap) : Type0 =
  forall a (c:target_lang (ref a)) (r:ref a). h `contains` r ==> 
    h `c.deep_contains` r /\ c.deeply_labeled r h (label_of r h)

unfold let pre_tgt_arrow
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (h0:lheap) =
  objects_deeply_labeled h0 /\                                            (* all objects are deeply labeled *)
  h0 `deep_contains` x /\                                                 (* required to instantiate the properties of modifies *)
  deeply_labeled x h0 Tourist                                             (* x is a Tourist *)

let post_tgt_arrow
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (#t2:t1 -> Type) {| tgtr : (x:t1 -> target_lang (t2 x)) |}
  (h0:lheap) (r:t2 x) (h1:lheap) =
  modifies_only_label Tourist h0 h1 /\                                  (* allow region rs to be modified *)

  objects_deeply_labeled h1 /\

  (h1 `(tgtr x).deep_contains` r) /\
  ((tgtr x).deeply_labeled r h1 Tourist)                                  (* x is deeply labeled with Tourist *)
(* TODO: what prevents the computation to allocate things in rp?
    If necessary, we can dissable it by adding the following postcondition:
      forall rrp. disjoint rrp rrs ==> equal_heap_dom rrp h0 h1 -- disables allocation in other regions
 *)

let mk_tgt_arrow 
  (t1:Type)
  {| tgt_t1: target_lang t1 |}
  (t2:t1 -> Type) (* TODO: this dependency is not needed anymore *)
  {| c2 : (x:t1 -> target_lang (t2 x)) |}
= x:t1 -> ST (t2 x) 
    (requires (pre_tgt_arrow x #tgt_t1))
    (ensures (post_tgt_arrow x #tgt_t1 #t2 #c2))

instance target_lang_arrow 
  (t1:Type)
  {| target_lang t1 |}
  (t2:t1 -> Type)
  {| (x:t1 -> target_lang (t2 x)) |}
  : target_lang (mk_tgt_arrow t1 t2) = {
    deep_contains = (fun _ _ -> True);
    deeply_labeled = (fun _ _ _ -> True);
    deep_recall = (fun _ -> ());
    deep_declassify = (fun _ _ -> ())
  }

let prog () =
  let r : ref int = alloc 0 in
  let h0 = get () in
  assert (label_of r h0 == NoVisa);
  declassify r Tourist;
  assert (label_of r h0 == NoVisa);
  let h1 = get () in
  assert (label_of r h1 == Tourist);
  let r1 : ref int = alloc 0 in
  declassify r1 Diplomatic;
  ()

(* TODO: during back-tarnslation, one needs to know that everything in env is deeply labeled with Tourist.
    previously, similar information (e.g., region) was on the reference *)