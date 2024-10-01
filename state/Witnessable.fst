module Witnessable

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Labeled.Monotonic.Heap
open Labeled.MST


type ref_lheap_pred =
  pred:(#a:Type -> #rel:_ -> mref a rel -> lheap -> Type0){forall (a:Type) (x:ref a) h0 h1. pred x h0 /\ h0 `lheap_rel` h1 ==> pred x h1}

noeq type linkedList (a: Type0) : Type0 =
| Nil : linkedList a
| Cons : v:a -> next:ref (linkedList a) -> linkedList a

class witnessable (t:Type) = {
  satisfy : t -> lheap -> ref_lheap_pred -> Type0;

  satisfy_monotonic : x:t -> pred:ref_lheap_pred -> h0:lheap -> h1:lheap -> Lemma (
    h0 `lheap_rel` h1 /\ satisfy x h0 pred ==> satisfy x h1 pred);

  witness : x:t -> pred:ref_lheap_pred -> ST (recall:(unit -> ST unit (fun _ -> True) (fun h0 _ h1 -> h0 == h1 /\ satisfy x h1 pred)))
    (requires (fun h0 -> satisfy x h0 pred))
    (ensures (fun h0 _ h1 -> h0 == h1));
}

instance witnessable_ref (t:Type) {| c:witnessable t |} : witnessable (ref t) = {
  satisfy = (fun x h pred -> pred x h);
  satisfy_monotonic = (fun x pred h0 h1 -> ());
  witness = (fun x pred ->
    mst_witness (pred x);
    (fun () -> mst_recall (pred x)))
}

instance witnessable_unit : witnessable unit = {
  satisfy = (fun _ _ _ -> True);
  satisfy_monotonic = (fun _ _ _ _ -> ());
  witness = (fun _ _ -> (fun () -> ()));
}

instance witnessable_int : witnessable int = {
  satisfy = (fun _ _ _ -> True);
  satisfy_monotonic = (fun _ _ _ _ -> ());
  witness = (fun _ _ -> (fun () -> ()));
}

instance witnessable_arrow 
  (t1:Type) (t2:Type)
  (pre:t1 -> lheap -> Type0)
  (post:t1 -> lheap -> t2 -> lheap -> Type0) // TODO: one cannot have pre-post depending on outside things.
: witnessable (x:t1 -> ST t2 (pre x) (post x)) = {
  satisfy = (fun _ _ _ -> True);
  satisfy_monotonic = (fun _ _ _ _ -> ());
  witness = (fun _ _ -> (fun () -> ()));
}

instance witnessable_pair (t1:Type) (t2:Type) {| c1:witnessable t1 |} {| c2:witnessable t2 |} : witnessable (t1 * t2) = {
  satisfy = (fun (x1, x2) h pred -> c1.satisfy x1 h pred /\ c2.satisfy x2 h pred);
  satisfy_monotonic = (fun (x1, x2) pred h0 h1 -> 
    c1.satisfy_monotonic x1 pred h0 h1;
    c2.satisfy_monotonic x2 pred h0 h1);
  witness = (fun (x1, x2) pred -> 
    let w1 = c1.witness x1 pred in
    let w2 = c2.witness x2 pred in
    (fun () -> w1 (); w2 ()))
}

instance witnessable_sum (t1:Type) (t2:Type) {| c1:witnessable t1 |} {| c2:witnessable t2 |} : witnessable (either t1 t2) = {
  satisfy = (fun x h pred ->
    match x with
    | Inl x1 -> c1.satisfy x1 h pred
    | Inr x2 -> c2.satisfy x2 h pred);
  satisfy_monotonic = (fun x pred h0 h1 ->
    match x with
    | Inl x1 -> c1.satisfy_monotonic x1 pred h0 h1
    | Inr x2 -> c2.satisfy_monotonic x2 pred h0 h1);
  witness = (fun x pred -> 
    match x with 
    | Inl x1 -> (let w = c1.witness x1 pred in (fun () -> w ()))
    | Inr x2 -> (let w = c2.witness x2 pred in (fun () -> w ())))
}

instance witnessable_llist (t:Type) {| c:witnessable t |} : witnessable (linkedList t) = {
  satisfy = (fun l h pred -> 
    match l with
    | Nil -> True
    | Cons x xsref -> c.satisfy x h pred /\ pred xsref h
  );

  satisfy_monotonic = (fun l pred h0 h1 ->
    match l with 
    | Nil -> ()
    | Cons x xsref -> c.satisfy_monotonic x pred h0 h1
  );

  witness = (fun l pred ->
    match l with
    | Nil -> (fun () -> ())
    | Cons x xsref ->
      let w = c.witness x pred in
      mst_witness (pred xsref);
      (fun () -> w (); mst_recall (pred xsref))
  );
}