module ShareableType

open FStar.Tactics

open FStar.Preorder
open FStar.Monotonic.Heap
open MST.Repr
open MST.Tot

type shareable_typ =
  | SUnit
  | SNat
  | SSum : shareable_typ -> shareable_typ -> shareable_typ
  | SPair : shareable_typ -> shareable_typ -> shareable_typ
  | SRef : shareable_typ -> shareable_typ
  | SLList : shareable_typ -> shareable_typ

let rec to_Type (t:shareable_typ) : Type u#0 =
  match t with
  | SUnit -> unit
  | SNat -> int
  | SSum t1 t2 -> either (to_Type t1) (to_Type t2)
  | SPair t1 t2 -> (to_Type t1) * (to_Type t2)
  | SRef t -> ref (to_Type t)
  | SLList t -> linkedList (to_Type t)

let rec forall_refs (pred:mref_pred) (#t:shareable_typ) (x:to_Type t) : Type0 =
  let rcall #t x = forall_refs pred #t x in
  match t with
  | SUnit -> True
  | SNat -> True
  | SSum t1 t2 -> begin
    let x : either (to_Type t1) (to_Type t2) = x in
    match x with
    | Inl x' -> rcall x'
    | Inr x' -> rcall x'
  end
  | SPair t1 t2 ->
    let x : (to_Type t1) * (to_Type t2) = x in
    rcall (fst x) /\ rcall (snd x)
  | SRef t' ->
    let x : ref (to_Type t') = x in
    pred #(to_Type t') #(fun _ _ -> True) x
  | SLList t' -> begin
    let x : linkedList (to_Type t') = x in
    match x with
    | LLNil -> True
    | LLCons v xsref ->
      rcall v /\ pred xsref
   end

let forall_refs_heap (pred:mref_heap_stable_pred) (h:heap) (#t:shareable_typ) (x:to_Type t) : Type0 =
  forall_refs (fun r -> pred r h) x

let lemma_forall_refs (t:shareable_typ) (x:to_Type (SRef t)) (pred:mref_pred) :
  Lemma (forall_refs pred x == pred #_ #(FStar.Heap.trivial_rel _) x) [SMTPat (forall_refs pred x)] by (compute ()) = ()

let lemma_forall_refs_heap (t:shareable_typ) (x:to_Type (SRef t)) (pred:mref_heap_stable_pred) (h:heap) :
  Lemma (forall_refs_heap pred h x == pred #_ #(FStar.Heap.trivial_rel _) x h) [SMTPat (forall_refs_heap pred h x)] by (compute ()) = ()

let rec forall_refs_heap_monotonic (pred:mref_heap_stable_pred) (h0 h1:heap) (#t:shareable_typ) (x:to_Type t) :
  Lemma (requires (h0 `heap_rel` h1 /\ forall_refs_heap pred h0 x)) (ensures (forall_refs_heap pred h1 x)) =
  match t with
  | SUnit -> ()
  | SNat -> ()
  | SSum t1 t2 -> begin
    let x : either (to_Type t1) (to_Type t2) = x in
    match x  with
    | Inl x' -> forall_refs_heap_monotonic pred h0 h1 x'
    | Inr x' -> forall_refs_heap_monotonic pred h0 h1 x'
  end
  | SPair t1 t2 ->
    let x : (to_Type t1) * (to_Type t2) = x in
    forall_refs_heap_monotonic pred h0 h1 (fst x);
    forall_refs_heap_monotonic pred h0 h1 (snd x)
  | SRef t' -> ()
  | SLList t' -> begin
    let x : linkedList (to_Type t') = x in
    match x with
    | LLNil -> ()
    | LLCons v xsref ->
      forall_refs_heap_monotonic pred h0 h1 v
   end

let rec lemma_forall_refs_heap_forall_refs_witnessed #t (v:to_Type t) (pred:mref_heap_stable_pred) :
  ST unit All
    (requires (fun h0 -> forall_refs_heap pred h0 v))
    (ensures (fun h0 _ h1 -> h0 == h1 /\ forall_refs (fun r -> witnessed (pred r)) v)) =
  match t with
  | SUnit -> ()
  | SNat -> ()
  | SSum t1 t2 -> begin
    let v : either (to_Type t1) (to_Type t2) = v in
    match v with
    | Inl v' -> lemma_forall_refs_heap_forall_refs_witnessed v' pred
    | Inr v' -> lemma_forall_refs_heap_forall_refs_witnessed v' pred
  end
  | SPair t1 t2 ->
    let v : (to_Type t1) * (to_Type t2) = v in
    lemma_forall_refs_heap_forall_refs_witnessed (fst v) pred;
    lemma_forall_refs_heap_forall_refs_witnessed (snd v) pred
  | SRef t' ->
    let v : ref (to_Type t') = v in
    witness (pred v);
    ()
  | SLList t' -> begin
    let v : linkedList (to_Type t') = v in
    match v with
    | LLNil -> ()
    | LLCons v xsref ->
      lemma_forall_refs_heap_forall_refs_witnessed v pred;
      witness (pred xsref)
  end

let rec lemma_forall_refs_witnessed_forall_refs_heap #t (v:to_Type t) (pred:mref_heap_stable_pred) :
  ST unit All
    (requires (fun _ -> forall_refs (fun r -> witnessed (pred r)) v))
    (ensures (fun h0 _ h1 -> h0 == h1 /\ forall_refs_heap pred h1 v)) =
  match t with
  | SUnit -> ()
  | SNat -> ()
  | SSum t1 t2 -> begin
    let v : either (to_Type t1) (to_Type t2) = v in
    match v with
    | Inl v' -> lemma_forall_refs_witnessed_forall_refs_heap v' pred
    | Inr v' -> lemma_forall_refs_witnessed_forall_refs_heap v' pred
  end
  | SPair t1 t2 ->
    let v : (to_Type t1) * (to_Type t2) = v in
    lemma_forall_refs_witnessed_forall_refs_heap (fst v) pred;
    lemma_forall_refs_witnessed_forall_refs_heap (snd v) pred
  | SRef t' ->
    let v : ref (to_Type t') = v in
    recall (pred v);
    ()
  | SLList t' -> begin
    let v : linkedList (to_Type t') = v in
    match v with
    | LLNil -> ()
    | LLCons v xsref ->
      lemma_forall_refs_witnessed_forall_refs_heap v pred;
      recall (pred xsref)
  end

let rec lemma_forall_refs_join #t (v:to_Type t) (pred1 pred2:mref_pred) :
  Lemma (requires (forall_refs pred1 v /\ forall_refs pred2 v))
        (ensures (forall_refs (fun r -> pred1 r /\ pred2 r) v)) =
  match t with
  | SUnit -> ()
  | SNat -> ()
  | SSum t1 t2 -> begin
    let v : either (to_Type t1) (to_Type t2) = v in
    match v with
    | Inl v' -> lemma_forall_refs_join v' pred1 pred2
    | Inr v' -> lemma_forall_refs_join v' pred1 pred2
  end
  | SPair t1 t2 ->
    let v : (to_Type t1) * (to_Type t2) = v in
    lemma_forall_refs_join (fst v) pred1 pred2;
    lemma_forall_refs_join (snd v) pred1 pred2
  | SRef t' -> ()
  | SLList t' -> begin
    let v : linkedList (to_Type t') = v in
    match v with
    | LLNil -> ()
    | LLCons v xsref ->
      lemma_forall_refs_join v pred1 pred2
  end

let rec lemma_forall_refs_split #t (v:to_Type t) (pred1 pred2:mref_pred) :
  Lemma (requires (forall_refs (fun r -> pred1 r /\ pred2 r) v))
        (ensures (forall_refs pred1 v /\ forall_refs pred2 v)) =
  match t with
  | SUnit -> ()
  | SNat -> ()
  | SSum t1 t2 -> begin
    let v : either (to_Type t1) (to_Type t2) = v in
    match v with
    | Inl v' -> lemma_forall_refs_split v' pred1 pred2
    | Inr v' -> lemma_forall_refs_split v' pred1 pred2
  end
  | SPair t1 t2 ->
    let v : (to_Type t1) * (to_Type t2) = v in
    lemma_forall_refs_split (fst v) pred1 pred2;
    lemma_forall_refs_split (snd v) pred1 pred2
  | SRef t' -> ()
  | SLList t' -> begin
    let v : linkedList (to_Type t') = v in
    match v with
    | LLNil -> ()
    | LLCons v xsref ->
      lemma_forall_refs_split v pred1 pred2
  end

