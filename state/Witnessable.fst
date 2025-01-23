module Witnessable

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Universe

open FStar.Monotonic.Heap
open MST.Tot


type ref_lheap_pred =
  pred:(#a:Type -> #rel:_ -> mref a rel -> heap -> Type0){forall (a:Type) (x:ref a) h0 h1. pred x h0 /\ h0 `heap_rel` h1 ==> pred x h1}

class witnessable (t:Type) = {
  satisfy : t -> (#a:_ -> #rel:_ -> mref a rel -> Type0) -> Type0;
  satisfy_on_heap : t -> heap -> ref_lheap_pred -> Type0;

  satisfy_on_heap_monotonic : x:t -> pred:ref_lheap_pred -> h0:heap -> h1:heap -> Lemma (
    h0 `heap_rel` h1 /\ satisfy_on_heap x h0 pred ==> satisfy_on_heap x h1 pred);

  pwitness : x:t -> pred:ref_lheap_pred -> ST (precall:(unit -> ST unit (fun _ -> True) (fun h0 _ h1 -> h0 == h1 /\ satisfy_on_heap x h1 pred)))
    (requires (fun h0 -> satisfy_on_heap x h0 pred))
    (ensures (fun h0 _ h1 -> h0 == h1));
}

instance witnessable_ref (t:Type) {| c:witnessable t |} : witnessable (ref t) = {
  satisfy = (fun x pred -> pred x);
  satisfy_on_heap = (fun x h pred -> pred x h);
  satisfy_on_heap_monotonic = (fun x pred h0 h1 -> ());
  pwitness = (fun x pred ->
    MST.Tot.witness (pred x);
    (fun () -> MST.Tot.recall (pred x)))
}

instance witnessable_unit : witnessable unit = {
  satisfy = (fun _ _ -> True);
  satisfy_on_heap = (fun _ _ _ -> True);
  satisfy_on_heap_monotonic = (fun _ _ _ _ -> ());
  pwitness = (fun _ _ -> (fun () -> ()));
}

instance witnessable_int : witnessable int = {
  satisfy = (fun _ _ -> True);
  satisfy_on_heap = (fun _ _ _ -> True);
  satisfy_on_heap_monotonic = (fun _ _ _ _ -> ());
  pwitness = (fun _ _ -> (fun () -> ()));
}

instance witnessable_arrow 
  (t1:Type) (t2:Type)
  (pre:t1 -> st_pre)
  (post:(x:t1 -> h0:heap -> st_post' t2 (pre x h0))) // TODO: one cannot have pre-post depending on outside things.
: witnessable (x:t1 -> ST t2 (pre x) (post x)) = {
  satisfy = (fun _ _ -> True);
  satisfy_on_heap = (fun _ _ _ -> True);
  satisfy_on_heap_monotonic = (fun _ _ _ _ -> ());
  pwitness = (fun _ _ -> (fun () -> ()));
}

instance witnessable_pair (t1:Type) (t2:Type) {| c1:witnessable t1 |} {| c2:witnessable t2 |} : witnessable (t1 * t2) = {
  satisfy = (fun (x1, x2) pred -> c1.satisfy x1 pred /\ c2.satisfy x2 pred);
  satisfy_on_heap = (fun (x1, x2) h pred -> c1.satisfy_on_heap x1 h pred /\ c2.satisfy_on_heap x2 h pred);
  satisfy_on_heap_monotonic = (fun (x1, x2) pred h0 h1 -> 
    c1.satisfy_on_heap_monotonic x1 pred h0 h1;
    c2.satisfy_on_heap_monotonic x2 pred h0 h1);
  pwitness = (fun (x1, x2) pred -> 
    let w1 = c1.pwitness x1 pred in
    let w2 = c2.pwitness x2 pred in
    (fun () -> w1 (); w2 ()))
}

instance witnessable_sum (t1:Type) (t2:Type) {| c1:witnessable t1 |} {| c2:witnessable t2 |} : witnessable (either t1 t2) = {
  satisfy = (fun x pred ->
    match x with
    | Inl x1 -> c1.satisfy x1 pred
    | Inr x2 -> c2.satisfy x2 pred);
  satisfy_on_heap = (fun x h pred ->
    match x with
    | Inl x1 -> c1.satisfy_on_heap x1 h pred
    | Inr x2 -> c2.satisfy_on_heap x2 h pred);
  satisfy_on_heap_monotonic = (fun x pred h0 h1 ->
    match x with
    | Inl x1 -> c1.satisfy_on_heap_monotonic x1 pred h0 h1
    | Inr x2 -> c2.satisfy_on_heap_monotonic x2 pred h0 h1);
  pwitness = (fun x pred -> 
    match x with 
    | Inl x1 -> (let w = c1.pwitness x1 pred in (fun () -> w ()))
    | Inr x2 -> (let w = c2.pwitness x2 pred in (fun () -> w ())))
}

instance witnessable_llist (t:Type) {| c:witnessable t |} : witnessable (linkedList t) = {
  satisfy = (fun l pred ->
    match l with
    | LLNil -> True
    | LLCons x xsref -> c.satisfy x pred /\ pred xsref);
  satisfy_on_heap = (fun l h pred -> 
    match l with
    | LLNil -> True
    | LLCons x xsref -> c.satisfy_on_heap x h pred /\ pred xsref h
  );

  satisfy_on_heap_monotonic = (fun l pred h0 h1 ->
    match l with 
    | LLNil -> ()
    | LLCons x xsref -> c.satisfy_on_heap_monotonic x pred h0 h1
  );

  pwitness = (fun l pred ->
    match l with
    | LLNil -> (fun () -> ())
    | LLCons x xsref ->
      let w = c.pwitness x pred in
      MST.Tot.witness (pred xsref);
      (fun () -> w (); MST.Tot.recall (pred xsref))
  );
}

instance witnessable_univ_raise (t:Type u#a) {| c:witnessable t |} : witnessable (raise_t u#a u#b t) = {
  satisfy = (fun x -> c.satisfy (downgrade_val x));
  satisfy_on_heap = (fun x -> c.satisfy_on_heap (downgrade_val x));
  satisfy_on_heap_monotonic = (fun x -> c.satisfy_on_heap_monotonic (downgrade_val x));
  pwitness = (fun x -> c.pwitness (downgrade_val x));
}
