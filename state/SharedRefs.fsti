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

let share_post (map_shared:map_sharedT) (is_shared:ref_heap_stable_pred) #a #rel (sr:mref a rel) h0 () h1 : Type0 =
    equal_dom h0 h1 /\
    modifies !{map_shared} h0 h1 /\
    ~(is_shared (map_shared) h1) /\
    (forall b (r:ref b). is_shared r h0 ==> is_shared r h1) /\
    (forall b (r:ref b). ~(is_shared r h0) /\ ~(compare_addrs r sr) ==> ~(is_shared r h1)) /\
    (forall p. p >= next_addr h1 ==> ~(sel h1 map_shared p)) /\
    is_shared sr h1

noeq
type sigT = {
  map_shared : erased map_sharedT;
  is_shared : pred:ref_heap_stable_pred;
 // is_shared_implies_contained : #a:_ -> #rel:_ -> r:mref a rel -> h:heap -> Lemma (is_shared r h ==> h `contains` r);
  fresh_ref_not_shared : #a:_ -> #rel:_ -> (r:mref a rel) -> h:heap -> Lemma (
    (forall p. p >= next_addr h ==> ~((sel h map_shared) p)) /\ (addr_of r >= next_addr h) ==> ~(is_shared r h));
  unmodified_map_implies_same_shared_status : s:Set.set nat -> h0:heap -> h1:heap -> 
    Lemma (requires (h0 `contains` map_shared /\ h0 `heap_rel` h1 /\ ~(addr_of map_shared `Set.mem` s) /\ modifies s h0 h1))
          (ensures (forall #a #rel (r:mref a rel). is_shared r h0 <==> is_shared r h1));
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
      (ensures (share_post map_shared is_shared #a #p sr))
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

type sharable_typ =
  | SUnit
  | SNat
  | SSum : sharable_typ -> sharable_typ -> sharable_typ
  | SPair : sharable_typ -> sharable_typ -> sharable_typ
  | SRef : sharable_typ -> sharable_typ
  | SLList : sharable_typ -> sharable_typ

let rec to_Type (t:sharable_typ) : Type u#0 = 
  match t with
  | SUnit -> unit
  | SNat -> int
  | SSum t1 t2 -> either (to_Type t1) (to_Type t2)
  | SPair t1 t2 -> (to_Type t1) * (to_Type t2)
  | SRef t -> ref (to_Type t)
  | SLList t -> linkedList (to_Type t)

let rec forallRefs (pred:ref_pred) (#t:sharable_typ) (x:to_Type t) : Type0 =
  let rcall #t x = forallRefs pred #t x in
  match t with
  | SUnit -> True
  | SNat -> True
  | SSum t1 t2 -> begin
    let x : either (to_Type t1) (to_Type t2) = x in
    match x  with
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

let forallRefsHeap (pred:ref_heap_stable_pred) (h:heap) (#t:sharable_typ) (x:to_Type t) : Type0 =
  forallRefs (fun r -> pred r h) x

let lemma_forallRefs (t:sharable_typ) (x:to_Type (SRef t)) (pred:ref_pred) :
  Lemma (forallRefs pred x == pred x) [SMTPat (forallRefs pred x)] by (compute ()) = ()
  
let lemma_forallRefsHeap (t:sharable_typ) (x:to_Type (SRef t)) (pred:ref_heap_stable_pred) (h:heap) :
  Lemma (forallRefsHeap pred h x == pred x h) [SMTPat (forallRefsHeap pred h x)] by (compute ()) = ()

let rec forallRefsHeap_monotonic (pred:ref_heap_stable_pred) (h0 h1:heap) (#t:sharable_typ) (x:to_Type t) :
  Lemma (requires (h0 `heap_rel` h1 /\ forallRefsHeap pred h0 x)) (ensures (forallRefsHeap pred h1 x)) =
  match t with
  | SUnit -> ()
  | SNat -> ()
  | SSum t1 t2 -> begin
    let x : either (to_Type t1) (to_Type t2) = x in
    match x  with
    | Inl x' -> forallRefsHeap_monotonic pred h0 h1 x' 
    | Inr x' -> forallRefsHeap_monotonic pred h0 h1 x' 
  end
  | SPair t1 t2 ->
    let x : (to_Type t1) * (to_Type t2) = x in
    forallRefsHeap_monotonic pred h0 h1 (fst x);
    forallRefsHeap_monotonic pred h0 h1 (snd x) 
  | SRef t' -> ()
  | SLList t' -> begin
    let x : linkedList (to_Type t') = x in
    match x with
    | LLNil -> ()
    | LLCons v xsref -> 
      forallRefsHeap_monotonic pred h0 h1 v 
   end 

let ctrans_ref_pred (h:heap) (pred:ref_heap_stable_pred) =
  (** forall references, if r satisfies pred in h, then the references r points to also satisfy pred **)
  (forall (t:sharable_typ) (r:ref (to_Type t)).
    h `contains` r /\ pred r h ==> forallRefsHeap pred h (sel h r)) (** cannot select without being contained **)
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

effect SST (a:Type) (pre:st_pre) (post: (h:heap -> Tot (st_post' a (pre h)))) =
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

let eliminate_ctrans_ref_pred (h:heap) #a (r:ref (to_Type a)) (pred:ref_heap_stable_pred) :
  Lemma
    (requires (ctrans_ref_pred h pred /\ h `contains` r /\ pred r h))
    (ensures (forallRefsHeap pred h (sel h r))) = ()

let rec inversion (a:sharable_typ) (xa:sharable_typ) :
  Lemma
    (requires (to_Type a == to_Type xa))
    (ensures (a == xa)) =
  match a with
  | SUnit -> ()
  | SNat -> ()
  | _ -> admit ()

let lemma_sst_alloc_preserves_contains #t (x:ref (to_Type t)) (v:to_Type t) (h0 h1:heap) : Lemma
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
        eliminate_ctrans_ref_pred h0 r contains_pred;
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

#push-options "--split_queries always"
let lemma_sst_alloc_preserves_shared #t (x:ref (to_Type t)) (v:to_Type t) (h0 h1:heap) : Lemma
  (requires (
    h0 `contains` shareS.map_shared /\
    h0 `heap_rel` h1 /\
    x `unused_in` h0 /\
    h1 `contains` x /\
    h1 == upd h0 x v /\ 
    modifies Set.empty h0 h1 /\
    ~(shareS.is_shared x h1) /\
    ctrans_ref_pred h0 shareS.is_shared))
  (ensures (
    ctrans_ref_pred h1 shareS.is_shared)) =
  introduce forall a (r:ref (to_Type a)). h1 `contains` r /\ shareS.is_shared r h1 ==> forallRefsHeap shareS.is_shared h1 (sel h1 r)
  with begin
    introduce h1 `contains` r /\ shareS.is_shared r h1 ==> forallRefsHeap shareS.is_shared h1 (sel h1 r) with _. begin
      introduce addr_of x =!= addr_of r ==> forallRefsHeap shareS.is_shared h1 (sel h1 r) with _. begin
        shareS.unmodified_map_implies_same_shared_status Set.empty h0 h1;
        eliminate forall a rel (r:mref a rel). shareS.is_shared r h0 <==> shareS.is_shared r h1 with _ _ r;
        lemma_unused_upd_contains h0 x v r;
        eliminate_ctrans_ref_pred h0 r shareS.is_shared;
        forallRefsHeap_monotonic shareS.is_shared h0 h1 (sel h0 r)
      end;
      introduce addr_of x == addr_of r ==> False with _. begin
        assert ~(shareS.is_shared x h1);
        assert (shareS.is_shared r h1);
        shareS.same_addr_same_sharing_status r x h1
      end
    end
  end
#pop-options
  
let lemma_sst_share_preserves_contains (h0 h1:heap) : Lemma
  (requires (
    equal_dom h0 h1 /\
    modifies !{shareS.map_shared} h0 h1 /\
    h0 `contains` shareS.map_shared /\
    h0 `heap_rel` h1 /\
    ctrans_ref_pred h0 contains_pred))
  (ensures (
    ctrans_ref_pred h1 contains_pred)) = 
  introduce forall a (r:ref (to_Type a)).
      contains_pred r h1 ==> forallRefsHeap contains_pred h1 (sel h1 r)
  with begin
    introduce contains_pred r h1 ==> forallRefsHeap contains_pred h1 (sel h1 r)
    with _. begin
      introduce addr_of r =!= addr_of shareS.map_shared ==> forallRefsHeap contains_pred h1 (sel h1 r) with _. begin
        eliminate_ctrans_ref_pred h0 r contains_pred;
        assert (h0 `contains` r);
        forallRefsHeap_monotonic contains_pred h0 h1 (sel h0 r)
      end;
      introduce addr_of r == addr_of shareS.map_shared ==> False with _. begin
        () 
      end
    end
  end

#push-options "--split_queries always"
let lemma_sst_share_preserves_shared #t (x:ref (to_Type t)) (h0 h1:heap) : Lemma
  (requires (
    h0 `heap_rel` h1 /\
    equal_dom h0 h1 /\
    modifies !{shareS.map_shared} h0 h1 /\
    h0 `contains` x /\
    h0 `contains` shareS.map_shared /\
    shareS.is_shared x h1 /\
    forallRefsHeap shareS.is_shared h0 (sel h0 x) /\
    (forall b (r:ref b). shareS.is_shared r h0 ==> shareS.is_shared r h1) /\
    (forall b (r:ref b). ~(shareS.is_shared r h0) /\ ~(compare_addrs r x) ==> ~(shareS.is_shared r h1)) /\
    (forall p. p >= next_addr h1 ==> ~(sel h1 shareS.map_shared p)) /\
    ctrans_ref_pred h0 shareS.is_shared))
  (ensures (
    ctrans_ref_pred h1 shareS.is_shared)) =
  introduce forall a (r:ref (to_Type a)). h1 `contains` r /\ shareS.is_shared r h1 ==> forallRefsHeap shareS.is_shared h1 (sel h1 r)
  with begin
    introduce h1 `contains` r /\ shareS.is_shared r h1 ==> forallRefsHeap shareS.is_shared h1 (sel h1 r) with _. begin
      introduce shareS.is_shared r h0 ==> forallRefsHeap shareS.is_shared h1 (sel h1 r) with _. begin
        eliminate_ctrans_ref_pred h0 r (shareS.is_shared);
        forallRefsHeap_monotonic shareS.is_shared h0 h1 (sel h0 r);
        assert (forallRefsHeap shareS.is_shared h1 (sel h0 r));
        assert (addr_of r =!= addr_of shareS.map_shared);
        assert (sel h0 r == sel h1 r)
      end;
      introduce ~(shareS.is_shared r h0) ==> forallRefsHeap shareS.is_shared h1 (sel h1 r) with _. begin
        assert (addr_of x =!= addr_of shareS.map_shared);
        forallRefsHeap_monotonic shareS.is_shared h0 h1 (sel h0 x);
        assert (sel h0 x == sel h1 x);
        assert (forallRefsHeap shareS.is_shared h1 (sel h1 x));
        assert (addr_of r == addr_of x);
        lemma_sel_same_addr h1 r x;
        inversion a t;
        assert (sel h1 r == sel h1 x);
        assert (forallRefsHeap shareS.is_shared h1 (sel h1 r))
      end
    end
  end
#pop-options

let sst_read (#t:sharable_typ) (r:ref (to_Type t)) 
  : SST (to_Type t) 
        (requires (fun h0 -> h0 `contains` r))
        (ensures (fun h0 v h1 -> h0 == h1 /\ v == sel h1 r)) =
  MST.Tot.read r

let sst_alloc (#t:sharable_typ) (init:to_Type t)
: SST (ref (to_Type t))
    (fun h0 -> forallRefsHeap contains_pred h0 init)
    (fun h0 r h1 -> alloc_post #(to_Type t) init h0 r h1 /\  ~(shareS.is_shared r h1))
=
  let h0 = get () in
  let r = alloc init in
  let h1 = get () in
  shareS.fresh_ref_not_shared r h0;
  shareS.unmodified_map_implies_same_shared_status Set.empty h0 h1;
  lemma_sst_alloc_preserves_contains r init h0 h1;
  lemma_sst_alloc_preserves_shared r init h0 h1;
  r

let sst_share (#t:sharable_typ) (r:ref (to_Type t)) 
: SST unit
  (fun h0 -> h0 `contains` r /\ 
         forallRefsHeap shareS.is_shared h0 (sel h0 r))
  (share_post shareS.map_shared shareS.is_shared r) 
=
  let h0 = get () in
  shareS.share r;
  let h1 = get () in
  lemma_sst_share_preserves_contains h0 h1;
  assert (ctrans_ref_pred h1 contains_pred);
  lemma_sst_share_preserves_shared r h0 h1;
  assert (ctrans_ref_pred h1 shareS.is_shared)

#push-options "--split_queries always"
let sst_alloc_shared (#t:sharable_typ) (init:to_Type t)
: SST (ref (to_Type t))
    (fun h0 -> forallRefsHeap contains_pred h0 init /\ forallRefsHeap shareS.is_shared h0 init)
    (fun h0 r h1 -> 
      fresh r h0 h1 /\ 
      sel h1 r == init /\
      is_mm r == false /\
 //     addr_of r == next_addr h0 /\
 //     next_addr h1 > next_addr h0 /\
      modifies !{shareS.map_shared} h0 h1 /\

      (forall b (r':ref b). shareS.is_shared r' h0 ==> shareS.is_shared r' h1) /\
      (forall b (r':ref b). ~(shareS.is_shared r' h0) /\ ~(compare_addrs r' r) ==> ~(shareS.is_shared r' h1)) /\
      shareS.is_shared r h1
      )
=
  let h0 = get () in
  let r = sst_alloc init in
  let h1 = get () in
  forallRefsHeap_monotonic shareS.is_shared h0 h1 init;
  shareS.unmodified_map_implies_same_shared_status Set.empty h0 h1;
  sst_share r;
  let h2 = get () in
  assert (fresh r h0 h2);
  assert (addr_of r =!= addr_of shareS.map_shared);
  assert (sel h2 r == init);
  assert (is_mm r == false);
  assert (modifies !{shareS.map_shared} h0 h2);
  assert (shareS.is_shared r h2);
  assert (forall b (r':ref b). shareS.is_shared r' h0 ==> shareS.is_shared r' h1);
  assert (forall b (r':ref b). ~(shareS.is_shared r' h0) /\ ~(compare_addrs r' r) ==> ~(shareS.is_shared r' h1));
  r
#pop-options

let lemma_sst_write_preserves_contains #t (x:ref (to_Type t)) (v:to_Type t) (h0 h1:heap) : Lemma
  (requires (
    h0 `heap_rel` h1 /\
    write_post x v h0 () h1 /\
    h0 `contains` x /\
    forallRefsHeap contains_pred h0 v /\
    ctrans_ref_pred h0 contains_pred))
  (ensures (
    ctrans_ref_pred h1 contains_pred)) =
  introduce forall a (r:ref (to_Type a)). h1 `contains` r ==> forallRefsHeap contains_pred h1 (sel h1 r)
  with begin
    introduce h1 `contains` r ==> forallRefsHeap contains_pred h1 (sel h1 r) with _. begin
      assert (equal_dom h0 h1);
      introduce addr_of r =!= addr_of x ==> forallRefsHeap contains_pred h1 (sel h1 r) with _. begin
        eliminate_ctrans_ref_pred h0 r contains_pred; 
        forallRefsHeap_monotonic contains_pred h0 h1 (sel h0 r)
      end;
      introduce addr_of r == addr_of x ==> forallRefsHeap contains_pred h1 (sel h1 r) with _. begin
        lemma_sel_same_addr h1 r x;
        inversion t a;
        assert (sel h1 r == sel h1 x);
        forallRefsHeap_monotonic contains_pred h0 h1 v
      end
    end
  end

#push-options "--split_queries always"
let lemma_sst_write_preserves_shared #t (x:ref (to_Type t)) (v:to_Type t) (h0 h1:heap) : Lemma
  (requires (
    h0 `contains` shareS.map_shared /\
    addr_of x =!= addr_of shareS.map_shared /\
    h0 `heap_rel` h1 /\
    write_post x v h0 () h1 /\
    h0 `contains` x /\
    shareS.is_shared x h0 /\
    shareS.is_shared x h1 /\
    forallRefsHeap shareS.is_shared h0 v /\
    ctrans_ref_pred h0 shareS.is_shared))
  (ensures (
    ctrans_ref_pred h1 shareS.is_shared)) =
  introduce forall a (r:ref (to_Type a)). h1 `contains` r /\ shareS.is_shared r h1 ==> forallRefsHeap shareS.is_shared h1 (sel h1 r)
  with begin
    introduce h1 `contains` r /\ shareS.is_shared r h1 ==> forallRefsHeap shareS.is_shared h1 (sel h1 r) with _. begin
      assert (equal_dom h0 h1);
      introduce addr_of r =!= addr_of x ==> forallRefsHeap shareS.is_shared h1 (sel h1 r) with _. begin
        shareS.unmodified_map_implies_same_shared_status !{x} h0 h1;
        eliminate forall a rel (r:mref a rel). shareS.is_shared r h0 <==> shareS.is_shared r h1 with _ _ r;
        assert (shareS.is_shared r h0);
        eliminate_ctrans_ref_pred h0 r shareS.is_shared; 
        forallRefsHeap_monotonic shareS.is_shared h0 h1 (sel h0 r)
      end;
      introduce addr_of r == addr_of x ==> forallRefsHeap shareS.is_shared h1 (sel h1 r) with _. begin
        lemma_sel_same_addr h1 r x;
        inversion t a;
        assert (sel h1 r == sel h1 x);
        forallRefsHeap_monotonic shareS.is_shared h0 h1 v
      end
    end
  end
#pop-options


#push-options "--split_queries always"
let sst_write (#t:sharable_typ) (r:ref (to_Type t)) (v:to_Type t)
: SST unit
  (requires (fun h0 -> 
    h0 `contains` r /\ shareS.is_shared r h0 /\ 
    forallRefsHeap contains_pred h0 v /\ forallRefsHeap shareS.is_shared h0 v))
  (ensures (fun h0 () h1 ->
    write_post r v h0 () h1 /\
    shareS.is_shared r h1)) =
  let h0 = get () in
  write r v;
  let h1 = get () in
  assert (shareS.is_shared r h1);
  assert (write_post r v h0 () h1);
  lemma_sst_write_preserves_contains r v h0 h1;
  lemma_sst_write_preserves_shared r v h0 h1;
  shareS.unmodified_map_implies_same_shared_status !{r} h0 h1;
  assert (addr_of r =!= addr_of shareS.map_shared);
  assert (~(shareS.is_shared (shareS.map_shared) h1));
  lemma_next_addr_upd_tot h0 r v;
  assert (next_addr h0 == next_addr h1);
  assert (forall p. p >= next_addr h1 ==> ~(sel h1 shareS.map_shared p));
  ()
#pop-options
