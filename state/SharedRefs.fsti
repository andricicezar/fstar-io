module SharedRefs

open FStar.Tactics

open FStar.Preorder
include FStar.Monotonic.Heap
open FStar.Ghost
open MST.Repr
include MST.Tot
include ShareableType

(** CA&DA: This can be proved trivially in FStar.Monotonic.Heap.fst **)
val lemma_eq_addrs_eq_all #a #rela #b #relb (r1:mref a rela) (r2:mref b relb) (h:heap) : Lemma
  (requires (h `contains` r1 /\ h `contains` r2 /\ addr_of r1 == addr_of r2))
  (ensures (a == b /\ rela == relb /\ is_mm r1 == is_mm r2 /\ sel h r1 == sel h r2))
(** DA: In my FStar.Monotonic.Heap.fst **)
(*
let lemma_eq_addrs_eq_all _ _ _ = ()
*)

(** DA: This can be proved trivially in FStar.Monotonic.Heap.fst **)
val lemma_eq_ref_types_eq_value_types #a #b (#rela:preorder a) (#relb : preorder b) (r:mref a rela)
  : Lemma (requires (mref a rela == mref b relb))
          (ensures  (a == b))
(** DA: In my FStar.Monotonic.Heap.fst **)
(*
let lemma_eq_ref_types_eq_value_types _ = ()
*)

type ref_kind =
  | Private
  | Shared
  | Encapsulated

let ref_kind_rel : preorder ref_kind = fun k k' ->
  match k , k' with
  | Private , _ | Shared , Shared | Encapsulated , Encapsulated -> True
  | _ , _ -> False

type map_sharedT =
  mref
    (pos -> GTot ref_kind)
    (fun (m0 m1:(pos -> GTot ref_kind)) ->
      forall p. (m0 p) `ref_kind_rel`  (m1 p))

val map_shared : erased map_sharedT

let is_private : mref_heap_pred = (fun #a #p (r:mref a p) h ->
    Private? ((sel h map_shared) (addr_of r)))

let is_private_addr : pos -> heap -> Type0 = (fun p h ->
    Private? ((sel h map_shared) p))

let is_shared : mref_heap_stable_pred = (fun #a #p (r:mref a p) h ->
    h `contains` map_shared /\ (** this contains is necessary to show that is_shared is a stable predicate **)
    Shared? ((sel h map_shared) (addr_of r)))

let is_encapsulated : mref_heap_stable_pred = (fun #a #p (r:mref a p) h ->
    h `contains` map_shared /\ (** this contains is necessary to show that is_encapsulated is a stable predicate **)
    Encapsulated? ((sel h map_shared) (addr_of r)))

let kind_not_modified #a #rel (r:mref a rel) (h0:heap) (h1:heap) =
  (sel h0 map_shared) (addr_of r) = (sel h1 map_shared) (addr_of r) /\
  h0 `contains` map_shared <==> h1 `contains` map_shared

let gets_shared (s:set nat) (h0:heap) (h1:heap) =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern ((sel h1 map_shared) (addr_of r))}
    ((~ (Set.mem (addr_of r) s)) /\ h0 `contains` r) ==> kind_not_modified r h0 h1) /\
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (is_shared r h1)}
    ((Set.mem (addr_of r) s) /\ h0 `contains` r) ==> is_shared r h1)

let share_post (map_shared:map_sharedT) (is_shared:mref_heap_stable_pred) #a #rel (sr:mref a rel) h0 () h1 : Type0 =
    equal_dom h0 h1 /\
    modifies !{map_shared} h0 h1 /\
    is_private (map_shared) h1 /\
    (forall p. p >= next_addr h1 ==> is_private_addr p h1) /\
    gets_shared !{sr} h0 h1

inline_for_extraction
val share : #a:Type0 -> #p:preorder a -> sr:(mref a p) ->
    ST unit
      (requires (fun h0 ->
        h0 `contains` sr /\
        h0 `contains` map_shared /\
        ~(compare_addrs sr map_shared) /\ (** prevent sharing the map *)
        is_private map_shared h0 /\
        is_private sr h0 /\ (** necessary to change the reference kind to shared *)
        (forall p. p >= next_addr h0 ==> is_private_addr p h0))) (** necessary to prove that freshly allocated references are not shared **)
      (ensures (share_post map_shared is_shared #a #p sr))

val lemma_fresh_ref_not_shared : #a:_ -> #rel:_ -> (r:mref a rel) -> h:heap ->
    Lemma (requires (h `contains` map_shared /\ (forall p. p >= next_addr h ==> is_private_addr p h) /\ (addr_of r >= next_addr h)))
          (ensures  (is_private r h))

val lemma_unmodified_map_implies_same_shared_status : s:Set.set nat -> h0:heap -> h1:heap ->
    Lemma (requires (h0 `contains` map_shared /\ h0 `heap_rel` h1 /\ ~(addr_of map_shared `Set.mem` s) /\ modifies s h0 h1))
          (ensures  (gets_shared Set.empty h0 h1))

val lemma_same_addr_same_sharing_status : #aa:_ -> #rela:_ -> #b:_ -> #relb:_ -> ra:mref aa rela -> rb:mref b relb -> h:heap ->
    Lemma (requires (addr_of ra == addr_of rb))
          (ensures (is_shared ra h <==> is_shared rb h))

let lemma_fresh_gets_shared #a #rel (r:mref a rel) (h0:heap) (h1:heap) (h2:heap)
: Lemma (requires (h0 `contains` map_shared /\ fresh r h0 h1 /\ modifies Set.empty h0 h1 /\ gets_shared !{r} h1 h2))
        (ensures  (gets_shared Set.empty h0 h2))
=
  ()

unfold let unmodified_common (h0:heap) (h1:heap) : Type0 =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (contains h1 r)}  (** CA: why is this here? this is from heap_rel **)
                               h0 `contains` r ==> h1 `contains` r) /\
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (r `unused_in` h0)} (** CA: probably this can be proven from heap_rel too *)
                               r `unused_in` h1 ==> r `unused_in` h0) /\
  (forall (n: nat) . {:pattern (n `addr_unused_in` h0) } (** CA: ditto **)
    n `addr_unused_in` h1 ==> n `addr_unused_in` h0)

let modifies_only_shared (h0:heap) (h1:heap) : Type0 =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (sel h1 r)}
    (h0 `contains` r /\ ~(compare_addrs r map_shared) /\ ~(is_shared r h0)) ==> sel h0 r == sel h1 r) /\
  unmodified_common h0 h1

let modifies_only_shared_and_encapsulated (h0:heap) (h1:heap) : Type0 =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (sel h1 r)}
    (h0 `contains` r /\ ~(compare_addrs r map_shared) /\ ~(is_shared r h0 \/ is_encapsulated r h0)) ==> sel h0 r == sel h1 r) /\
  unmodified_common h0 h1

let modifies_shared_and (h0:heap) (h1:heap) (s:Set.set nat) : Type0 =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (sel h1 r)}
    (h0 `contains` r /\ ~(compare_addrs r map_shared) /\ ~(is_shared r h0 \/ Set.mem (addr_of r) s)) ==> sel h0 r == sel h1 r) /\
  unmodified_common h0 h1

let modifies_shared_and_encapsulated_and (h0:heap) (h1:heap) (s:Set.set nat) : Type0 =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (sel h1 r)}
    (h0 `contains` r /\ ~(compare_addrs r map_shared) /\ ~(is_shared r h0 \/ is_encapsulated r h0 \/ Set.mem (addr_of r) s)) ==> sel h0 r == sel h1 r) /\
  unmodified_common h0 h1

let ctrans_ref_pred (h:heap) (pred:mref_heap_stable_pred) =
  (** forall references, if r satisfies pred in h, then the references r points to refs that also satisfy pred **)
  (forall (t:shareable_typ) (r:ref (to_Type t)).
    h `contains` r /\ pred r h ==> forall_refs_heap pred h (sel h r)) (** cannot select without being contained **)
  // CA: previous version tried to implement this with typeclasses, but it was not working because one had to prove
  // that two instances of the same type are equal.
  // invariant:
  //   forall (a:Type) (c:witnessable a) (r:ref a).
  //     (witnessable_ref _ #c).satisfy r h pred ==> c.satisfy (sel h r) h pred
  // lemma needed:
  //   forall (a:Type) (c:witnessable a) (c':witnessable a) (r:ref a).
  //     c.satisfy r h pred ==> c'.satisfy r h pred

let trans_shared_contains (h:heap) =
  ctrans_ref_pred h contains_pred /\ ctrans_ref_pred h is_shared

unfold
let sst_inv h =
  trans_shared_contains h /\
  h `contains` map_shared /\
  is_private (map_shared) h /\ (* the map stays unshared *)
  (forall p. p >= next_addr h ==> is_private_addr p h)

unfold
let sst_pre (pre:st_pre) : st_pre =
  fun h0 -> sst_inv h0 /\ pre h0

unfold
let sst_post
  (a:Type)
  (pre:st_pre)
  (post: (h:heap -> Tot (st_post' a ((sst_pre pre) h))))
  : (h:heap -> Tot (st_post' a ((sst_pre pre) h))) =
  fun h0 r h1 -> sst_inv h1 /\ post h0 r h1

effect SST (a:Type) (pre:st_pre) (post: (h:heap -> Tot (st_post' a ((sst_pre pre) h)))) =
  ST a
    (requires (sst_pre pre))
    (ensures  (sst_post a pre post))

let eliminate_ctrans_ref_pred (h:heap) #a (r:ref (to_Type a)) (pred:mref_heap_stable_pred) :
  Lemma
    (requires (ctrans_ref_pred h pred /\ h `contains` r /\ pred r h))
    (ensures (forall_refs_heap pred h (sel h r))) = ()

unfold
let force_retype (#a #b:Type0) (x:a) : Pure b (requires (a == b)) (ensures (fun _ -> True)) = x

let lemma_forall_refs_heap_force_retype_refs (pred:mref_heap_stable_pred) (h:heap) #a (x:ref (to_Type a)) :
  Lemma
    (requires (pred #(to_Type a) x h))
    (ensures (forall b. to_Type b == to_Type a ==>  pred #(to_Type b) #(FStar.Heap.trivial_preorder _) (force_retype x) h)) = ()

#set-options "--print_implicits"
let rec lemma_forall_refs_heap_force_retype (pred:mref_heap_stable_pred) (h:heap) #a (x:to_Type a) :
  Lemma
    (requires (forall_refs_heap pred h #a x))
    (ensures (forall b. to_Type b == to_Type a ==> forall_refs_heap pred h #b (force_retype x))) =
  match a with
  | SUnit -> ()
  | SNat -> ()
  | SSum t1 t2 -> begin
    let x : either (to_Type t1) (to_Type t2) = x in
    match x  with
    | Inl x' -> begin
      lemma_forall_refs_heap_force_retype pred h x';
      assert (forall b1. to_Type b1 == to_Type t1 ==> forall_refs_heap pred h #b1 (force_retype x'));
      introduce forall b. to_Type b == to_Type a ==> forall_refs_heap pred h #b (force_retype x) with begin
        introduce _ ==> _ with _. begin
          assert (forall_refs_heap pred h #a x);
          assert (forall_refs_heap pred h #b (force_retype x))
        end
      end
    end
    | Inr x' -> begin
      lemma_forall_refs_heap_force_retype pred h x';
      assert (forall b1. to_Type b1 == to_Type t2 ==> forall_refs_heap pred h #b1 (force_retype x'));
      introduce forall b. to_Type b == to_Type a ==> forall_refs_heap pred h #b (force_retype x) with begin
        introduce _ ==> _ with _. begin
          assert (forall_refs_heap pred h #a x);
          assert (forall_refs_heap pred h #b (force_retype x)) by (norm [delta_only [`%force_retype];iota])
        end
      end
    end
  end
  | SRef t' -> begin
    let x : ref (to_Type t') = x in
    (** no recursive call, because we don't have any type contructor **)
    introduce forall b. to_Type b == to_Type a ==> forall_refs_heap pred h #b (force_retype x) with begin
      introduce _ ==> _ with _. begin
        let SRef t'' = b in
        assert (forall_refs_heap pred h #a x);
        assert (pred #(to_Type t') #(FStar.Heap.trivial_preorder _) x h);
        lemma_forall_refs_heap_force_retype_refs pred h #t' x;
        assert (to_Type (SRef t'') == to_Type (SRef t'));
        assert (ref (to_Type t'') == ref (to_Type t'));
        lemma_eq_ref_types_eq_value_types #(to_Type t') #(to_Type t'') #(FStar.Heap.trivial_preorder _) #(FStar.Heap.trivial_preorder _) x;
        assert (to_Type t'' == to_Type t'); (** would work if ref is injective **)
        assert (pred #(to_Type t'') #(FStar.Heap.trivial_preorder _) x h);
        assert (forall_refs_heap pred h #b (force_retype x))
      end
    end
  end
  | SPair t1 t2 ->
    let x : (to_Type t1) * (to_Type t2) = x in
    lemma_forall_refs_heap_force_retype pred h (fst x);
    lemma_forall_refs_heap_force_retype pred h (snd x);
    introduce forall b. to_Type b == to_Type a ==> forall_refs_heap pred h #b (force_retype x) with begin
      introduce _ ==> _ with _. begin
        assert (forall_refs_heap pred h #a x);
        assert (forall_refs_heap pred h #b (force_retype x))
      end
    end
  | SLList t' -> begin
    let x : linkedList (to_Type t') = x in
    match x with
    | LLNil -> ()
    | LLCons v xsref ->
      lemma_forall_refs_heap_force_retype pred h v;
      introduce forall b. to_Type b == to_Type a ==> forall_refs_heap pred h #b (force_retype x) with begin
        introduce _ ==> _ with _. begin
          assert (forall_refs_heap pred h #a x);
          assert (forall_refs_heap pred h #b (force_retype x))
        end
      end
   end

let lemma_sst_write_or_alloc_preserves_contains #a (#rel:preorder a) (x:mref a rel) (v:a) (h0 h1:heap) : Lemma
  (requires (
    h0 `heap_rel` h1 /\
    (h0 `contains` x \/ fresh x h0 h1) /\
    h1 == upd h0 x v /\ (** SMTPat kicks in **)
    (forall t . to_Type t == a ==> forall_refs_heap contains_pred h0 #t v) /\
    ctrans_ref_pred h0 contains_pred))
  (ensures (
    ctrans_ref_pred h1 contains_pred)) =
  introduce forall t (r:ref (to_Type t)). h1 `contains` r ==> forall_refs_heap contains_pred h1 (sel h1 r)
  with begin
    introduce h1 `contains` r ==> forall_refs_heap contains_pred h1 (sel h1 r) with _. begin
      introduce addr_of r =!= addr_of x ==> forall_refs_heap contains_pred h1 (sel h1 r) with _. begin
        eliminate_ctrans_ref_pred h0 r contains_pred;
        forall_refs_heap_monotonic contains_pred h0 h1 (sel h0 r)
      end;
      introduce addr_of r == addr_of x ==> forall_refs_heap contains_pred h1 (sel h1 r) with _. begin
        lemma_eq_addrs_eq_all r x h1;
        assert (a == to_Type t);
        forall_refs_heap_monotonic contains_pred h0 h1 #t v;
        assert (forall_refs_heap contains_pred h1 #t v);
        assert (sel h1 r == force_retype v);
        lemma_forall_refs_heap_force_retype contains_pred h1 #t v;
        assert (forall_refs_heap contains_pred h1 #t (force_retype v));
        assert (forall_refs_heap contains_pred h1 #t (sel h1 r))
      end
    end
  end

let lemma_sst_write_or_alloc_preserves_contains_shareable #t (#rel:preorder (to_Type t)) (x:mref (to_Type t) rel) (v:to_Type t) (h0 h1:heap) : Lemma
  (requires (
    h0 `heap_rel` h1 /\
    (h0 `contains` x \/ fresh x h0 h1) /\
    h1 == upd h0 x v /\ (** SMTPat kicks in **)
    forall_refs_heap contains_pred h0 #t v /\
    ctrans_ref_pred h0 contains_pred))
  (ensures (
    ctrans_ref_pred h1 contains_pred)) =
  introduce forall t' . to_Type t' == to_Type t ==> forall_refs_heap contains_pred h0 #t' (force_retype #_ #(to_Type t') v) with
  begin
    introduce to_Type t' == to_Type t ==> forall_refs_heap contains_pred h0 #t' (force_retype #_ #(to_Type t') v) with _.
    begin
      lemma_forall_refs_heap_force_retype contains_pred h0 v
    end
  end;
  lemma_sst_write_or_alloc_preserves_contains x v h0 h1

let lemma_sst_share_preserves_contains (h0 h1:heap) : Lemma
  (requires (
    h0 `contains` map_shared /\
    h0 `heap_rel` h1 /\
    equal_dom h0 h1 /\
    modifies !{map_shared} h0 h1 /\
    ctrans_ref_pred h0 contains_pred))
  (ensures (
    ctrans_ref_pred h1 contains_pred)) =
  introduce forall a (r:ref (to_Type a)).
      contains_pred r h1 ==> forall_refs_heap contains_pred h1 (sel h1 r)
  with begin
    introduce contains_pred r h1 ==> forall_refs_heap contains_pred h1 (sel h1 r)
    with _. begin
      introduce addr_of r =!= addr_of map_shared ==> forall_refs_heap contains_pred h1 (sel h1 r) with _. begin
        eliminate_ctrans_ref_pred h0 r contains_pred;
        assert (h0 `contains` r);
        forall_refs_heap_monotonic contains_pred h0 h1 (sel h0 r)
      end;
      introduce addr_of r == addr_of map_shared ==> False with _. begin
        ()
      end
    end
  end

#push-options "--split_queries always"
let lemma_sst_alloc_preserves_shared #a (#rel:preorder a) (x:mref a rel) (v:a) (h0 h1:heap) : Lemma
  (requires (
    h0 `contains` map_shared /\
    h0 `heap_rel` h1 /\
    fresh x h0 h1 /\
    h1 == upd h0 x v /\ (** SMTPat kicks in **)
    ~(is_shared x h1) /\
    ctrans_ref_pred h0 is_shared))
  (ensures (
    ctrans_ref_pred h1 is_shared)) =
  introduce forall a (r:ref (to_Type a)). h1 `contains` r /\ is_shared r h1 ==> forall_refs_heap is_shared h1 (sel h1 r)
  with begin
    introduce h1 `contains` r /\ is_shared r h1 ==> forall_refs_heap is_shared h1 (sel h1 r) with _. begin
      introduce addr_of x =!= addr_of r ==> forall_refs_heap is_shared h1 (sel h1 r) with _. begin
        assert (~(addr_of map_shared `Set.mem` Set.empty));
        lemma_unmodified_map_implies_same_shared_status Set.empty h0 h1;
        eliminate forall (a:Type) (rel:preorder a) (r:mref a rel).
          ((~ (Set.mem (addr_of r) Set.empty)) /\ h0 `contains` r) ==> (is_shared r h0 <==> is_shared r h1) with _ _ r;
        lemma_unused_upd_contains h0 x v r;
        eliminate_ctrans_ref_pred h0 r is_shared;
        forall_refs_heap_monotonic is_shared h0 h1 (sel h0 r)
      end;
      introduce addr_of x == addr_of r ==> False with _. begin
        assert ~(is_shared x h1);
        assert (is_shared r h1);
        lemma_same_addr_same_sharing_status r x h1
      end
    end
  end
#pop-options

#push-options "--split_queries always"
let lemma_sst_write_preserves_shared #t (#rel:preorder (to_Type t)) (x:mref (to_Type t) rel) (v:to_Type t) (h0 h1:heap) : Lemma
  (requires (
    h0 `contains` map_shared /\
    h0 `heap_rel` h1 /\
    h0 `contains` x /\
    h1 == upd h0 x v /\ (** SMTPat kicks in **)
    (is_shared x h0 ==> forall_refs_heap is_shared h0 v) /\
    ctrans_ref_pred h0 is_shared))
  (ensures (
    ctrans_ref_pred h1 is_shared)) =
  introduce forall a (r:ref (to_Type a)). h1 `contains` r /\ is_shared r h1 ==> forall_refs_heap is_shared h1 (sel h1 r)
  with begin
    introduce h1 `contains` r /\ is_shared r h1 ==> forall_refs_heap is_shared h1 (sel h1 r) with _. begin
      assert (~(addr_of map_shared `Set.mem` !{x}));
      lemma_unmodified_map_implies_same_shared_status !{x} h0 h1;
      eliminate forall (a:Type) (rel:preorder a) (r:mref a rel).
        ((~ (Set.mem (addr_of r) !{x})) /\ h0 `contains` r) ==> (is_shared r h0 <==> is_shared r h1) with _ _ r;
      assert (is_shared r h0);
      introduce addr_of r =!= addr_of x ==> forall_refs_heap is_shared h1 (sel h1 r) with _. begin
        eliminate_ctrans_ref_pred h0 r is_shared;
        forall_refs_heap_monotonic is_shared h0 h1 (sel h0 r)
      end;
      introduce addr_of r == addr_of x ==> forall_refs_heap is_shared h1 (sel h1 r) with _. begin
        lemma_eq_addrs_eq_all r x h1;
        lemma_same_addr_same_sharing_status r x h0;
        eliminate is_shared x h0 ==> forall_refs_heap is_shared h0 v with _;
        forall_refs_heap_monotonic is_shared h0 h1 v;
        lemma_forall_refs_heap_force_retype is_shared h1 #t v
      end
    end
  end
#pop-options

#push-options "--split_queries always"
let lemma_sst_share_preserves_shared #t (x:ref (to_Type t)) (h0 h1:heap) : Lemma
  (requires (
    h0 `contains` map_shared /\
    h0 `heap_rel` h1 /\
    equal_dom h0 h1 /\
    modifies !{map_shared} h0 h1 /\
    h0 `contains` x /\
    forall_refs_heap is_shared h0 (sel h0 x) /\
    gets_shared !{x} h0 h1 /\
    (forall p. p >= next_addr h1 ==> is_private_addr p h1) /\
    ctrans_ref_pred h0 is_shared))
  (ensures (
    ctrans_ref_pred h1 is_shared)) =
  introduce forall a (r:ref (to_Type a)). h1 `contains` r /\ is_shared r h1 ==> forall_refs_heap is_shared h1 (sel h1 r)
  with begin
    introduce h1 `contains` r /\ is_shared r h1 ==> forall_refs_heap is_shared h1 (sel h1 r) with _. begin
      introduce is_shared r h0 ==> forall_refs_heap is_shared h1 (sel h1 r) with _. begin
        eliminate_ctrans_ref_pred h0 r (is_shared);
        forall_refs_heap_monotonic is_shared h0 h1 (sel h0 r);
        assert (forall_refs_heap is_shared h1 (sel h0 r));
        assert (addr_of r =!= addr_of map_shared);
        assert (sel h0 r == sel h1 r)
      end;
      introduce ~(is_shared r h0) ==> forall_refs_heap is_shared h1 (sel h1 r) with _. begin
        assert (addr_of x =!= addr_of map_shared);
        assert (addr_of r == addr_of x);
        lemma_eq_addrs_eq_all r x h1;
        forall_refs_heap_monotonic is_shared h0 h1 (sel h0 x);
        lemma_forall_refs_heap_force_retype is_shared h1 #t (sel h1 x)
      end
    end
  end
#pop-options

inline_for_extraction
let sst_read #a #rel (r:mref a rel)
  : SST a
        (requires (fun h0 -> h0 `contains` r))
        (ensures (fun h0 v h1 -> h0 == h1 /\ v == sel h1 r)) =
  MST.Tot.read r

inline_for_extraction
let sst_alloc #a (#rel:preorder a) (init:a)
: SST (mref a rel)
    (fun h0 ->
      (forall t . to_Type t == a ==>
        forall_refs_heap contains_pred h0 #t init))
    (fun h0 r h1 ->
      alloc_post #a init h0 r h1 /\
      is_private r h1 /\
      gets_shared Set.empty h0 h1)
=
  let h0 = get_heap () in
  let r = alloc #a #rel init in
  let h1 = get_heap () in
  lemma_fresh_ref_not_shared r h0;
  lemma_unmodified_map_implies_same_shared_status Set.empty h0 h1;
  assert (gets_shared Set.empty h0 h1);
  assert (is_private r h1);
  assert (alloc_post #a init h0 r h1);
  assert (ctrans_ref_pred h0 contains_pred);
  lemma_sst_write_or_alloc_preserves_contains r init h0 h1;
  lemma_sst_alloc_preserves_shared r init h0 h1;
  assert (ctrans_ref_pred h1 contains_pred);
  assert (ctrans_ref_pred h1 is_shared);
  r

inline_for_extraction
let sst_alloc_shareable (#t:shareable_typ) (init:to_Type t)
: SST (ref (to_Type t))
    (fun h0 -> forall_refs_heap contains_pred h0 init)
    (fun h0 r h1 ->
      alloc_post #(to_Type t) init h0 r h1 /\
      is_private r h1 /\
      gets_shared Set.empty h0 h1)
=
  let h0 = get_heap () in
  introduce forall t' . to_Type t' == to_Type t ==> forall_refs_heap contains_pred h0 #t' (force_retype #_ #(to_Type t') init) with
  begin
    lemma_forall_refs_heap_force_retype contains_pred h0 init
  end;
  sst_alloc #(to_Type t) #(FStar.Heap.trivial_preorder _) init

inline_for_extraction
let sst_share (#t:shareable_typ) (r:ref (to_Type t))
: SST unit
  (fun h0 -> h0 `contains` r /\
         is_private r h0 /\
         forall_refs_heap is_shared h0 (sel h0 r))
  (share_post map_shared is_shared r)
=
  assert (~(compare_addrs r map_shared));
  let h0 = get_heap () in
  share r;
  let h1 = get_heap () in
  lemma_sst_share_preserves_contains h0 h1;
  assert (ctrans_ref_pred h1 contains_pred);
  lemma_sst_share_preserves_shared r h0 h1;
  assert (ctrans_ref_pred h1 is_shared)

#push-options "--split_queries always"
inline_for_extraction
let sst_alloc_shared (#t:shareable_typ) (init:to_Type t)
: SST (ref (to_Type t))
    (fun h0 -> forall_refs_heap contains_pred h0 init /\ forall_refs_heap is_shared h0 init)
    (fun h0 r h1 ->
      fresh r h0 h1 /\
      sel h1 r == init /\
      is_mm r == false /\
      modifies !{map_shared} h0 h1 /\
      gets_shared Set.empty h0 h1 /\
      is_shared r h1 /\
      modifies_only_shared h0 h1 (** here to help **)) =
  let h0 = get_heap () in
  let r = sst_alloc_shareable init in
  let h1 = get_heap () in
  forall_refs_heap_monotonic is_shared h0 h1 init;
  assert (~(addr_of map_shared `Set.mem` Set.empty));
  lemma_unmodified_map_implies_same_shared_status Set.empty h0 h1;
  sst_share r;
  let h2 = get_heap () in
  assert (fresh r h0 h2);
  assert (addr_of r =!= addr_of map_shared);
  assert (sel h2 r == init);
  assert (is_mm r == false);
  assert (modifies !{map_shared} h0 h2);
  assert (is_shared r h2);
  assert (unmodified_common h0 h2);
  lemma_fresh_gets_shared r h0 h1 h2;
  assert (gets_shared Set.empty h0 h2);
  assert (is_shared r h2);
  assert (modifies_only_shared h0 h2);
  r
#pop-options

let lemma_sst_write_non_shareable_preserves_contains #a (#rel:preorder a) (x:mref a rel) (v:a) (h0 h1:heap) : Lemma
  (requires (
    h0 `heap_rel` h1 /\
    (h0 `contains` x \/ fresh x h0 h1) /\
    h1 == upd h0 x v /\ (** SMTPat kicks in **)
    sel h1 x == v /\
    (forall t. ~(to_Type t == a)) /\
    ctrans_ref_pred h0 contains_pred))
  (ensures (
    ctrans_ref_pred h1 contains_pred)) =
  introduce forall b (r:ref (to_Type b)). h1 `contains` r ==> forall_refs_heap contains_pred h1 (sel h1 r)
  with begin
    introduce h1 `contains` r ==> forall_refs_heap contains_pred h1 (sel h1 r) with _. begin
      introduce addr_of r =!= addr_of x ==> forall_refs_heap contains_pred h1 (sel h1 r) with _. begin
        eliminate_ctrans_ref_pred h0 r contains_pred;
        forall_refs_heap_monotonic contains_pred h0 h1 (sel h0 r)
      end;
      introduce addr_of r == addr_of x ==> False with _. ()
    end
  end

let lemma_sst_write_non_shareable_preserves_shared #a (#rel:preorder a) (x:mref a rel) (v:a) (h0 h1:heap) : Lemma
  (requires (
    h0 `contains` map_shared /\
    h0 `heap_rel` h1 /\
    h0 `contains` x /\
    ~(compare_addrs x map_shared) /\
    h1 == upd h0 x v /\ (** SMTPat kicks in **)
    (forall t. ~(to_Type t == a)) /\
    ctrans_ref_pred h0 is_shared))
  (ensures (
    ctrans_ref_pred h1 is_shared)) =
  introduce forall b (r:ref (to_Type b)). h1 `contains` r /\ is_shared r h1 ==> forall_refs_heap is_shared h1 (sel h1 r)
  with begin
    introduce h1 `contains` r /\ is_shared r h1 ==> forall_refs_heap is_shared h1 (sel h1 r) with _. begin
      assert (equal_dom h0 h1);
      introduce addr_of r =!= addr_of x ==> forall_refs_heap is_shared h1 (sel h1 r) with _. begin
        lemma_unmodified_map_implies_same_shared_status !{x} h0 h1;
        eliminate forall (a:Type) (rel:preorder a) (r:mref a rel).
            ((~ (Set.mem (addr_of r) !{x})) /\ h0 `contains` r) ==> (is_shared r h0 <==> is_shared r h1) with _ _ r;
        assert (is_shared r h0);
        eliminate_ctrans_ref_pred h0 r is_shared;
        forall_refs_heap_monotonic is_shared h0 h1 (sel h0 r)
      end;
      introduce addr_of r == addr_of x ==> False with _. ()
    end
  end

inline_for_extraction
let sst_write #a (#rel:preorder a) (r:mref a rel) (v:a)
: SST unit
  (requires (fun h0 ->
    h0 `contains` r /\
    rel (sel h0 r) v /\
    ~(compare_addrs r map_shared) /\
    (forall t. to_Type t == a ==>
      forall_refs_heap contains_pred h0 #t v /\
      (is_shared r h0 ==> forall_refs_heap is_shared h0 #t v))))
  (ensures (fun h0 () h1 ->
    write_post r v h0 () h1 /\
    gets_shared Set.empty h0 h1 /\
    (is_shared r h0 ==> modifies_only_shared h0 h1) (** here to help **))) =
  let h0 = get_heap () in
  write r v;
  let h1 = get_heap () in
  assert (~(is_shared (map_shared) h1));
  lemma_next_addr_upd h0 r v;
  assert (forall p. p >= next_addr h1 ==> is_private_addr p h1);
  lemma_upd_equals_upd_tot_for_contained_refs h0 r v;
  lemma_unmodified_map_implies_same_shared_status !{r} h0 h1;
  introduce (exists t. to_Type t == a) ==> trans_shared_contains h1 with _. begin
    eliminate exists t. to_Type t == a returns _ with _. begin
      lemma_sst_write_or_alloc_preserves_contains_shareable #t #rel r v h0 h1;
      lemma_sst_write_preserves_shared #t #rel r v h0 h1
    end
  end;
  introduce (forall t. ~(to_Type t == a)) ==> trans_shared_contains h1 with _. begin
    lemma_sst_write_non_shareable_preserves_contains r v h0 h1;
    lemma_sst_write_non_shareable_preserves_shared r v h0 h1
  end;
  ()

#push-options "--split_queries always"
inline_for_extraction
let sst_write_shareable (#t:shareable_typ) (r:ref (to_Type t)) (v:to_Type t)
: SST unit
  (requires (fun h0 ->
    h0 `contains` r /\ forall_refs_heap contains_pred h0 v /\
    (is_shared r h0 ==> forall_refs_heap is_shared h0 v)))
  (ensures (fun h0 () h1 ->
    write_post r v h0 () h1 /\
    gets_shared Set.empty h0 h1 /\
    (is_shared r h0 ==> modifies_only_shared h0 h1) (** here to help **))) =
  let h0 = get_heap () in
  introduce forall t'. to_Type t' == to_Type t ==>
      forall_refs_heap contains_pred h0 #t' (force_retype #_ #(to_Type t') v) /\
      (is_shared r h0 ==> forall_refs_heap is_shared h0 #t' (force_retype #_ #(to_Type t') v)) with
  begin
    introduce to_Type t' == to_Type t ==>
      forall_refs_heap contains_pred h0 #t' (force_retype #_ #(to_Type t') v) /\
      (is_shared r h0 ==> forall_refs_heap is_shared h0 #t' (force_retype #_ #(to_Type t') v)) with _.
    begin
      lemma_forall_refs_heap_force_retype contains_pred h0 v;
      introduce is_shared r h0 ==> forall_refs_heap is_shared h0 #t' (force_retype #_ #(to_Type t') v) with _.
      begin
        lemma_forall_refs_heap_force_retype is_shared h0 v
      end
    end
  end;
  assert (~(compare_addrs r map_shared));
  sst_write #(to_Type t) #(FStar.Heap.trivial_preorder _) r v
#pop-options

inline_for_extraction
let sst_write_ref #a (r:ref a) (v:a)
: SST unit
  (requires (fun h0 ->
    h0 `contains` r /\
    ~(compare_addrs r map_shared) /\
    (forall t. to_Type t == a ==>
      forall_refs_heap contains_pred h0 #t v /\
      (is_shared r h0 ==> forall_refs_heap is_shared h0 #t v))))
  (ensures (fun h0 () h1 ->
    write_post r v h0 () h1 /\
    gets_shared Set.empty h0 h1 /\
    (is_shared r h0 ==> modifies_only_shared h0 h1) (** here to help **))) =
  sst_write r v

let gets_encapsulated (s:set nat) (h0:heap) (h1:heap) =
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern ((sel h1 map_shared) (addr_of r))}
    ((~ (Set.mem (addr_of r) s)) /\ h0 `contains` r) ==> (sel h0 map_shared) (addr_of r) = (sel h1 map_shared) (addr_of r)) /\
  (forall (a:Type) (rel:preorder a) (r:mref a rel).{:pattern (is_encapsulated r h1)}
    ((Set.mem (addr_of r) s) /\ h0 `contains` r) ==> is_encapsulated r h1)

let encapsulate_post #a #rel (r:mref a rel) h0 () h1 : Type0 =
    equal_dom h0 h1 /\
    modifies !{map_shared} h0 h1 /\
    is_private (map_shared) h1 /\
    (forall p. p >= next_addr h1 ==> is_private_addr p h1) /\
    gets_encapsulated !{r} h0 h1

#push-options "--split_queries always"
let lemma_sst_encapsulate_preserves_shared #a (#rel:preorder a) (x:mref a rel) (h0 h1:heap) : Lemma
  (requires (
    h0 `contains` map_shared /\
    h0 `heap_rel` h1 /\
    equal_dom h0 h1 /\
    modifies !{map_shared} h0 h1 /\
    h0 `contains` x /\
    ~(compare_addrs x map_shared) /\  (** in contrast to sst_share, cannot be inferred because mref a rel is not guaranteed to be different from map_shared's type *)
    gets_encapsulated !{x} h0 h1 /\
    (forall p. p >= next_addr h1 ==> is_private_addr p h1) /\
    ctrans_ref_pred h0 is_shared))
  (ensures (
    ctrans_ref_pred h1 is_shared)) =
  introduce forall a (r:ref (to_Type a)). h1 `contains` r /\ is_shared r h1 ==> forall_refs_heap is_shared h1 (sel h1 r)
  with begin
    introduce h1 `contains` r /\ is_shared r h1 ==> forall_refs_heap is_shared h1 (sel h1 r) with _. begin
      introduce is_shared r h0 ==> forall_refs_heap is_shared h1 (sel h1 r) with _. begin
        eliminate_ctrans_ref_pred h0 r (is_shared);
        forall_refs_heap_monotonic is_shared h0 h1 (sel h0 r);
        assert (forall_refs_heap is_shared h1 (sel h0 r));
        assert (addr_of r =!= addr_of map_shared);
        assert (sel h0 r == sel h1 r)
      end;
      introduce ~(is_shared r h0) ==> forall_refs_heap is_shared h1 (sel h1 r) with _. begin
        assert (addr_of x =!= addr_of map_shared);
        assert (is_private r h0 \/ is_encapsulated r h0);
        introduce is_private r h0 ==> forall_refs_heap is_shared h1 (sel h1 r) with _. begin
          introduce addr_of x = addr_of r ==> False with _. begin
            assert (is_encapsulated r h1);
            assert (is_shared r h1)
          end
        end
      end
    end
  end
#pop-options

inline_for_extraction
val encapsulate : #a:Type0 -> #p:preorder a -> r:(mref a p) ->
    ST unit
      (requires (fun h0 ->
        h0 `contains` r /\
        h0 `contains` map_shared /\
        ~(compare_addrs r map_shared) /\ (** prevent encapsulating the map *)
        is_private map_shared h0 /\
        is_private r h0 /\ (** necessary to change the reference kind to encapsulated *)
        (forall p. p >= next_addr h0 ==> is_private_addr p h0))) (** necessary to prove that freshly allocated references are not encapsulated **)
      (ensures (encapsulate_post #a #p r))

inline_for_extraction
let sst_encapsulate  #a (#rel:preorder a) (r:mref a rel)
: SST unit
  (fun h0 -> h0 `contains` r /\
         ~(compare_addrs r map_shared) /\  (** in contrast to sst_share, cannot be inferred because mref a rel is not guaranteed to be different from map_shared's type *)
         is_private r h0)
  (encapsulate_post r)
=
  let h0 = get_heap () in
  encapsulate r;
  let h1 = get_heap () in
  lemma_sst_share_preserves_contains h0 h1;
  lemma_sst_encapsulate_preserves_shared r h0 h1;
  ()
