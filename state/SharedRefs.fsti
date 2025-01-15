module SharedRefs

open FStar.Tactics

open FStar.Preorder
include FStar.Monotonic.Heap
open FStar.Ghost
include MST.Tot

type ref_pred =
  #a:Type0 -> #rel:preorder a -> mref a rel -> Type0

type ref_heap_stable_pred =
  pred:(#a:Type -> #rel:_ -> mref a rel -> heap -> Type0){forall (a:Type) (x:ref a) h0 h1. pred x h0 /\ h0 `heap_rel` h1 ==> pred x h1}

type map_sharedT = 
  mref (pos -> GTot bool) (fun (m0 m1:pos -> GTot bool) -> forall p. m0 p ==> m1 p) (** pre-order necessary to show that the predicate `is_shared` is stable **)

noeq
type sigT = {
  map_shared : erased map_sharedT;
  is_shared : pred:ref_heap_stable_pred;
 // is_shared_implies_contained : #a:_ -> #rel:_ -> r:mref a rel -> h:heap -> Lemma (is_shared r h ==> h `contains` r);
  fresh_ref_not_shared : #a:_ -> #rel:_ -> (r:mref a rel) -> h:heap -> Lemma (
    (forall p. p >= next_addr h ==> ~((sel h map_shared) p)) /\ (addr_of r >= next_addr h) ==> ~(is_shared r h));
  unmodified_map_implies_same_shared_status : s:Set.set nat -> h0:heap -> h1:heap -> 
    Lemma (h0 `contains` map_shared /\ h0 `heap_rel` h1 /\ ~(addr_of map_shared `Set.mem` s) /\ modifies s h0 h1 ==> 
      (forall #a #rel (r:mref a rel). is_shared r h0 <==> is_shared r h1));
  same_addr_same_sharing_status : #aa:_ -> #rela:_ -> #b:_ -> #relb:_ -> ra:mref aa rela -> rb:mref b relb -> h:heap ->
    Lemma (addr_of ra == addr_of rb ==> (is_shared ra h <==> is_shared rb h));
  share : #a:Type0 -> #p:preorder a -> sr:(mref a p) ->
    ST unit 
      (requires (fun h0 -> 
        h0 `contains` sr /\
        h0 `contains` map_shared /\
        ~(compare_addrs sr map_shared) /\ (** prevent sharing the map *)
        ~(is_shared map_shared h0) /\
        (forall p. p >= next_addr h0 ==> ~(sel h0 map_shared p)))) (** necessary to prove that freshly allocated references are not shared **)
      (ensures (fun h0 _ h1 ->
        modifies !{map_shared} h0 h1 /\
        ~(is_shared (map_shared) h1) /\
        (forall b (r:ref b). is_shared r h0 ==> is_shared r h1) /\
        (forall b (r:ref b). ~(is_shared r h0) /\ ~(compare_addrs r sr) ==> ~(is_shared r h1)) /\
        (forall p. p >= next_addr h1 ==> ~(sel h1 map_shared p)) /\
        is_shared sr h1))
}

val shareS : sigT

unfold let unmodified_common (h0:heap) (h1:heap) : Type0 =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (contains h1 r)}
                               h0 `contains` r ==> h1 `contains` r) /\
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (r `unused_in` h0)}
                               r `unused_in` h1 ==> r `unused_in` h0) /\
  (forall (n: nat) . {:pattern (n `addr_unused_in` h0) }
    n `addr_unused_in` h1 ==> n `addr_unused_in` h0)

let modifies_only_shared (h0:heap) (h1:heap) : Type0 =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (sel h1 r)} 
    (h0 `contains` r /\ ~(shareS.is_shared r h0)) ==> sel h0 r == sel h1 r) /\
  unmodified_common h0 h1

type inv_typ =
  | IUnit
  | INat
  | ISum : inv_typ -> inv_typ -> inv_typ
  | IPair : inv_typ -> inv_typ -> inv_typ
  | IRef : inv_typ -> inv_typ
  | ILList : inv_typ -> inv_typ

let rec to_Type (t:inv_typ) : Type u#0 = 
  match t with
  | IUnit -> unit
  | INat -> int
  | ISum t1 t2 -> either (to_Type t1) (to_Type t2)
  | IPair t1 t2 -> (to_Type t1) * (to_Type t2)
  | IRef t -> ref (to_Type t)
  | ILList t -> linkedList (to_Type t)

let rec forallRefs (pred:ref_pred) (#t:inv_typ) (x:to_Type t) : Type0 =
  let rcall #t x = forallRefs pred #t x in
  match t with
  | IUnit -> True
  | INat -> True
  | ISum t1 t2 -> begin
    let x : either (to_Type t1) (to_Type t2) = x in
    match x  with
    | Inl x' -> rcall x' 
    | Inr x' -> rcall x' 
  end
  | IPair t1 t2 ->
    let x : (to_Type t1) * (to_Type t2) = x in
    rcall (fst x) /\ rcall (snd x)
  | IRef t' -> 
    let x : ref (to_Type t') = x in
    pred #(to_Type t') #(fun _ _ -> True) x
  | ILList t' -> begin
    let x : linkedList (to_Type t') = x in
    match x with
    | LLNil -> True
    | LLCons v xsref -> 
      rcall v /\ pred xsref
   end 

let forallRefsHeap (pred:ref_heap_stable_pred) (h:heap) (#t:inv_typ) (x:to_Type t) : Type0 =
  forallRefs (fun r -> pred r h) x

let lemma_forallRefs (t:inv_typ) (x:to_Type (IRef t)) (pred:ref_pred) :
  Lemma (forallRefs pred x == pred x) [SMTPat (forallRefs pred x)] by (compute ()) = ()
  
let lemma_forallRefsHeap (t:inv_typ) (x:to_Type (IRef t)) (pred:ref_heap_stable_pred) (h:heap) :
  Lemma (forallRefsHeap pred h x == pred x h) [SMTPat (forallRefsHeap pred h x)] by (compute ()) = ()

let rec forallRefsHeap_monotonic (pred:ref_heap_stable_pred) (h0 h1:heap) (#t:inv_typ) (x:to_Type t) :
  Lemma (h0 `heap_rel` h1 /\ forallRefsHeap pred h0 x ==> forallRefsHeap pred h1 x) =
  match t with
  | IUnit -> ()
  | INat -> ()
  | ISum t1 t2 -> begin
    let x : either (to_Type t1) (to_Type t2) = x in
    match x  with
    | Inl x' -> forallRefsHeap_monotonic pred h0 h1 x' 
    | Inr x' -> forallRefsHeap_monotonic pred h0 h1 x' 
  end
  | IPair t1 t2 ->
    let x : (to_Type t1) * (to_Type t2) = x in
    forallRefsHeap_monotonic pred h0 h1 (fst x);
    forallRefsHeap_monotonic pred h0 h1 (snd x) 
  | IRef t' -> ()
  | ILList t' -> begin
    let x : linkedList (to_Type t') = x in
    match x with
    | LLNil -> ()
    | LLCons v xsref -> 
      forallRefsHeap_monotonic pred h0 h1 v 
   end 

let ctrans_ref_pred (h:heap) (pred:ref_heap_stable_pred) =
  (** forall references, if r satisfies pred in h, then the references r points to also satisfy pred **)
  (forall (t:inv_typ) (r:ref (to_Type t)).
    pred r h ==> forallRefsHeap pred h (sel h r))
  // CA: previous version tried to implement this with typeclasses, but it was not working because one had to prove 
  // that two instances of the same type are equal.
  // invariant:
  //   forall (a:Type) (c:witnessable a) (r:ref a). 
  //     (witnessable_ref _ #c).satisfy r h pred ==> c.satisfy (sel h r) h pred
  // lemma needed:
  //   forall (a:Type) (c:witnessable a) (c':witnessable a) (r:ref a).
  //     c.satisfy r h pred ==> c'.satisfy r h pred

let trans_shared_contains (h:heap) = 
  ctrans_ref_pred h contains_pred /\ ctrans_ref_pred h shareS.is_shared

effect IST (a:Type) (pre:st_pre) (post: (h:heap -> Tot (st_post' a (pre h)))) =
  ST a 
    (requires (fun h0 -> 
      trans_shared_contains h0 /\
      h0 `contains` shareS.map_shared /\ 
      ~(shareS.is_shared (shareS.map_shared) h0) /\ (* the map stays unshared *)
      (forall p. p >= next_addr h0 ==> ~(sel h0 shareS.map_shared p)) /\
      pre h0))
    (ensures  (fun h0 r h1 -> 
      trans_shared_contains h1 /\
      ~(shareS.is_shared (shareS.map_shared) h1) /\
      (forall p. p >= next_addr h1 ==> ~(sel h1 shareS.map_shared p)) /\
      post h0 r h1))

let eliminate_ctrans_ref_pred (h:heap) a (r:ref (to_Type a)) (pred:ref_heap_stable_pred) :
  Lemma
    (requires (ctrans_ref_pred h pred))
    (ensures (pred r h ==> forallRefsHeap pred h (sel h r)
    )) = ()

let eliminate_ctrans_ref_shared h a (r:ref (to_Type a)) :
  Lemma
    (requires (ctrans_ref_pred h shareS.is_shared))
    (ensures (shareS.is_shared r h ==> forallRefsHeap shareS.is_shared h (sel h r))) = ()

let eliminate_ctrans_ref_contains h a (r:ref (to_Type a)) :
  Lemma
    (requires (ctrans_ref_pred h contains_pred))
    (ensures (contains_pred r h ==> forallRefsHeap contains_pred h (sel h r))) = ()

let rec inversion (a:inv_typ) (xa:inv_typ) :
  Lemma
    (requires (to_Type a == to_Type xa))
    (ensures (a == xa)) =
  match a with
  | IUnit -> ()
  | INat -> ()
  | _ -> admit ()

let read (#t:inv_typ) (r:ref (to_Type t)) 
  : IST (to_Type t) 
        (requires (fun h0 -> h0 `contains` r))
        (ensures (fun h0 v h1 -> h0 == h1 /\ v == sel h1 r)) =
  MST.Tot.read r
  
let lemma_ist_alloc_preserves_contains t (x:ref (to_Type t)) (v:to_Type t) (h0 h1:heap) : Lemma
  (requires (
    h0 `heap_rel` h1 /\
    h1 == upd h0 x v /\ 
    fresh x h0 h1 /\ 
    modifies Set.empty h0 h1 /\
    sel h1 x == v /\ 
    ~(shareS.is_shared x h1) /\
    is_mm x == false /\
    forallRefsHeap contains_pred h0 v /\
    ctrans_ref_pred h0 contains_pred))
  (ensures (
    ctrans_ref_pred h1 contains_pred)) = 
  introduce forall a (r:ref (to_Type a)).
      contains_pred r h1 ==> forallRefsHeap contains_pred h1 (sel h1 r)
  with begin
    introduce contains_pred r h1 ==> forallRefsHeap contains_pred h1 (sel h1 r)
    with _. begin
      introduce addr_of r =!= addr_of x ==> forallRefsHeap contains_pred h1 (sel h1 r) with _. begin
        eliminate_ctrans_ref_pred h0 a r contains_pred;
        assert (h0 `contains` r);
        forallRefsHeap_monotonic contains_pred h0 h1 (sel h0 r)
      end;
      introduce addr_of r == addr_of x ==> forallRefsHeap contains_pred h1 (sel h1 r) with _. begin
        assert (sel h1 x == v);
        inversion a t;
        forallRefsHeap_monotonic contains_pred h0 h1 v
      end
    end
  end

let lemma_ist_alloc_preserves_shared t (x:ref (to_Type t)) (v:to_Type t) (h0 h1:heap) : Lemma
  (requires (
    h0 `contains` shareS.map_shared /\
    h0 `heap_rel` h1 /\
    h1 == upd h0 x v /\ 
    fresh x h0 h1 /\ 
    modifies Set.empty h0 h1 /\
    sel h1 x == v /\ 
    ~(shareS.is_shared x h1) /\
    is_mm x == false /\
    forallRefsHeap contains_pred h0 v /\
    ctrans_ref_pred h0 shareS.is_shared))
  (ensures (
    ctrans_ref_pred h1 shareS.is_shared)) =
  introduce forall a (r:ref (to_Type a)). shareS.is_shared r h1 ==> forallRefsHeap shareS.is_shared h1 (sel h1 r)
  with begin
    introduce shareS.is_shared r h1 ==> forallRefsHeap shareS.is_shared h1 (sel h1 r) with _. begin
      shareS.unmodified_map_implies_same_shared_status Set.empty h0 h1;
      assert (shareS.is_shared r h0);
      eliminate_ctrans_ref_pred h0 a r shareS.is_shared;
      forallRefsHeap_monotonic shareS.is_shared h0 h1 (sel h0 r);
      assert (forallRefsHeap shareS.is_shared h1 (sel h0 r));
      introduce addr_of x =!= addr_of r ==> forallRefsHeap shareS.is_shared h1 (sel h1 r) with _. ();
      introduce addr_of x == addr_of r ==> forallRefsHeap shareS.is_shared h1 (sel h1 r) with _. begin
        assert ~(shareS.is_shared x h1);
        assert (shareS.is_shared r h1);
        shareS.same_addr_same_sharing_status r x h1;
        assert False
      end
    end
  end


let ist_alloc (#t:inv_typ) (init:to_Type t)
: IST (ref (to_Type t))
    (fun h0 -> forallRefsHeap contains_pred h0 init)
    (fun h0 r h1 -> alloc_post #(to_Type t) init h0 r h1)
=
  let h0 = get () in
  let r = alloc init in
  let h1 = get () in
  shareS.fresh_ref_not_shared r h0;
  shareS.unmodified_map_implies_same_shared_status Set.empty h0 h1;
  lemma_ist_alloc_preserves_contains t r init h0 h1;
  lemma_ist_alloc_preserves_shared t r init h0 h1;
  r

let _ = () 

(**  
let elab_write (#t:typ0) (r:ref (elab_typ0 t)) (v:elab_typ0 t) 
: IST unit
  (requires (fun h0 -> 
    shallowly_contained_low r #(elab_typ0_tc (TRef t)) h0 /\
    shallowly_contained_low v #(elab_typ0_tc t) h0))
  (ensures (fun h0 () h1 ->
    write_post r v h0 () h1 /\
    modifies_only_label Low h0 h1 /\
    shallowly_contained_low r #(elab_typ0_tc (TRef t)) h1))
= let h0 = get () in
  write r v;
  let h1 = get () in
  lemma_write_preserves_is_low (to_inv_typ t) r v h0 h1;
  lemma_write_preserves_contains (to_inv_typ t) r v h0 h1;
  ()

let declassify_low' (#t:typ0) (r:ref (elab_typ0 t)) : ST unit
  (fun h -> (elab_typ0_tc (TRef t)).satisfy r h contains_pred /\ inv_points_to h contains_pred)
  (fun h0 () h1 -> 
    inv_points_to h1 contains_pred /\
    shallowly_contained_low r #(elab_typ0_tc (TRef t)) h1 /\
    declassify_post r Low h0 () h1)
=
  let h0 = get () in
  declassify r Low;
  let h1 = get () in
  lemma_declassify_preserves_contains (to_inv_typ t) r h0 h1

val elab_alloc (#t:typ0) (init:elab_typ0 t)
: IST (ref (elab_typ0 t))
  (requires (fun h0 ->
    shallowly_contained_low init #(elab_typ0_tc t) h0))
  (ensures (fun h0 r h1 -> 
    fresh r h0 h1 /\ 
    modifies Set.empty h0 h1 /\
    modifies_classification Set.empty h0 h1 /\
    sel h1 r == init /\
    shallowly_contained_low r #(elab_typ0_tc (TRef t)) h1))
let elab_alloc #t init = 
  let h0 = get () in
  let r : ref (elab_typ0 t) = ist_alloc init in
  let h1 = get () in
  declassify_low' r;
  let h2 = get () in
  (elab_typ0_tc t).satisfy_monotonic init is_low_pred h0 h1;
  lemma_declassify_preserves_is_low (to_inv_typ t) r h1 h2;
  assert (inv_points_to h2 is_low_pred);
  r
**)
