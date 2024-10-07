module TargetLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Labeled.Monotonic.Heap
open Labeled.MST
open Witnessable

(** _elab_typ should be in translation file, but it is here because 
    we need it to write our invariants **)
type inv_typ =
  | InvT_Unit
  | InvT_Nat
  | InvT_Sum : inv_typ -> inv_typ -> inv_typ
  | InvT_Pair : inv_typ -> inv_typ -> inv_typ
  | InvT_Ref : inv_typ -> inv_typ
  | InvT_LList : inv_typ -> inv_typ

let rec to_Type (t:inv_typ) : Type u#0 = 
  match t with
  | InvT_Unit -> unit
  | InvT_Nat -> int
  | InvT_Sum t1 t2 -> either (to_Type t1) (to_Type t2)
  | InvT_Pair t1 t2 -> (to_Type t1) * (to_Type t2)
  | InvT_Ref t -> ref (to_Type t)
  | InvT_LList t -> linkedList (to_Type t)

let rec to_Type_solve (t:inv_typ) : witnessable (to_Type t) =
  match t with
  | InvT_Unit -> witnessable_unit
  | InvT_Nat -> witnessable_int
  | InvT_Sum t1 t2 -> witnessable_sum (to_Type t1) (to_Type t2) #(to_Type_solve t1) #(to_Type_solve t2)
  | InvT_Pair t1 t2 -> witnessable_pair (to_Type t1) (to_Type t2) #(to_Type_solve t1) #(to_Type_solve t2)
  | InvT_Ref t -> witnessable_ref (to_Type t) #(to_Type_solve t)
  | InvT_LList t -> witnessable_llist (to_Type t) #(to_Type_solve t)

let inv_points_to (h:lheap) pred =
  // forall (a:Type) (c:witnessable a) (r:ref a). 
  //   (witnessable_ref _ #c).satisfy r h pred ==>
  //     c.satisfy (sel h r) h pred
  // CA: previous version does not work because in proofs, one needs to prove a property like:
  // forall (a:Type) (c:witnessable a) (c':witnessable a) (r:ref a).
  //   c.satisfy r h pred ==> c'.satisfy r h pred

  // however, the following version needs an inversion lemma that cannot be proven in F* yet
  // because one cannot reason about the types of effectful arrows. e.g., `int =!= int -> ST int` cannot be proven
  (forall (a:inv_typ) (r:ref (to_Type a)).
    (witnessable_ref _ #(to_Type_solve a)).satisfy r h pred ==> 
      (to_Type_solve a).satisfy (sel h r) h pred)

let inv_low_contains (h:lheap) = 
  inv_points_to h contains_pred /\ inv_points_to h is_low_pred

let eliminate_inv_points_to (h:lheap) a (r:ref (to_Type a)) pred :
  Lemma
    (requires (inv_points_to h pred))
    (ensures (
      (witnessable_ref (to_Type a) #(to_Type_solve a)).satisfy r h pred ==> 
        (to_Type_solve a).satisfy (sel h r) h pred
    )) = ()

let eliminate_inv_low h a (r:ref (to_Type a)) :
  Lemma
    (requires (inv_points_to h is_low_pred))
    (ensures (
      (witnessable_ref (to_Type a) #(to_Type_solve a)).satisfy r h is_low_pred ==> 
        (to_Type_solve a).satisfy (sel h r) h is_low_pred
    )) = ()

let eliminate_inv_contains h a (hinv:lheap -> Type0) (r:ref (to_Type a)) :
  Lemma
    (requires (inv_points_to h contains_pred))
    (ensures (
      (witnessable_ref (to_Type a) #(to_Type_solve a)).satisfy r h contains_pred ==> 
        (to_Type_solve a).satisfy (sel h r) h contains_pred
    )) = ()

effect IST (a:Type) (pre:st_pre) (post: (h:lheap -> Tot (st_post' a (pre h)))) =
  ST a 
    (requires (fun h0      -> inv_low_contains h0 /\ pre h0))
    (ensures  (fun h0 r h1 -> inv_low_contains h1 /\ post h0 r h1))

let rec inversion (a:inv_typ) (xa:inv_typ) :
  Lemma
    (requires (to_Type a == to_Type xa))
    (ensures (a == xa /\ to_Type_solve a == to_Type_solve xa)) =
  match a with
  | InvT_Unit -> ()
  | InvT_Nat -> ()
  | InvT_Sum t1 t2 -> begin
    let InvT_Sum t1' t2' = xa in
    assume (forall a b c d. either a b == either c d ==> a == c /\ b == d);
    inversion t1 t1';
    inversion t2 t2'
  end
  | InvT_Pair t1 t2 -> begin
    let InvT_Pair t1' t2' = xa in
    assume (forall a b c d. (a * b) == (c * d) ==> a == c /\ b == d);
    inversion t1 t1';
    inversion t2 t2'
  end
  | InvT_Ref t -> begin
    let InvT_Ref t' = xa in
    assume (forall a b. ref a == ref b ==> a == b);
    inversion t t'
  end
  | InvT_LList t -> begin
    let InvT_LList t' = xa in
    assume (forall a b. linkedList a == linkedList b ==> a == b);
    inversion t t'
  end
  
let lemma_write_preserves_is_low t (x:ref (to_Type t)) (v:to_Type t) (h0 h1:lheap) : Lemma
  (requires (
    h0 `lheap_rel` h1 /\
    equal_dom h0 h1 /\
    modifies (Set.singleton (addr_of x)) h0 h1 /\
    modifies_classification Set.empty h0 h1 /\
    sel h1 x == v /\
    (to_Type_solve (InvT_Ref t)).satisfy x h0 is_low_pred /\
    (to_Type_solve t).satisfy v h0 is_low_pred /\
    inv_points_to h0 is_low_pred))
  (ensures (
    inv_points_to h1 is_low_pred)) = 
  introduce forall a (r:ref (to_Type a)).
      (witnessable_ref _ #(to_Type_solve a)).satisfy r h1 is_low_pred ==> 
        (to_Type_solve a).satisfy (sel h1 r) h1 is_low_pred
  with begin
    introduce (witnessable_ref _ #(to_Type_solve a)).satisfy r h1 is_low_pred 
      ==> (to_Type_solve a).satisfy (sel h1 r) h1 is_low_pred
    with _. begin
      introduce addr_of r =!= addr_of x ==> (to_Type_solve a).satisfy (sel h1 r) h1 is_low_pred with _. begin
        eliminate_inv_points_to h0 a r is_low_pred;
        (to_Type_solve a).satisfy_monotonic (sel h0 r) is_low_pred h0 h1
      end;
      introduce addr_of r == addr_of x ==> (to_Type_solve a).satisfy (sel h1 r) h1 is_low_pred with _. begin
        assert (sel h1 x == v);
        lemma_sel_same_addr' h1 x r;
        inversion a t;
        assert ((to_Type_solve t).satisfy v h0 is_low_pred);
        (to_Type_solve t).satisfy_monotonic v is_low_pred h0 h1;
        assert ((to_Type_solve t).satisfy v h1 is_low_pred)
      end
    end
  end

let lemma_write_preserves_contains t (x:ref (to_Type t)) (v:to_Type t) (h0 h1:lheap) : Lemma
  (requires (
    h0 `lheap_rel` h1 /\
    equal_dom h0 h1 /\
    modifies (Set.singleton (addr_of x)) h0 h1 /\
    modifies_classification Set.empty h0 h1 /\
    sel h1 x == v /\
    (to_Type_solve (InvT_Ref t)).satisfy x h0 contains_pred /\
    (to_Type_solve t).satisfy v h0 contains_pred /\
    inv_points_to h0 contains_pred))
  (ensures (
    inv_points_to h1 contains_pred)) = 
  introduce forall a (r:ref (to_Type a)).
      (witnessable_ref _ #(to_Type_solve a)).satisfy r h1 contains_pred ==> 
        (to_Type_solve a).satisfy (sel h1 r) h1 contains_pred
  with begin
    introduce (witnessable_ref _ #(to_Type_solve a)).satisfy r h1 contains_pred 
      ==> (to_Type_solve a).satisfy (sel h1 r) h1 contains_pred
    with _. begin
      introduce addr_of r =!= addr_of x ==> (to_Type_solve a).satisfy (sel h1 r) h1 contains_pred with _. begin
        eliminate_inv_points_to h0 a r contains_pred;
        (to_Type_solve a).satisfy_monotonic (sel h0 r) contains_pred h0 h1
      end;
      introduce addr_of r == addr_of x ==> (to_Type_solve a).satisfy (sel h1 r) h1 contains_pred with _. begin
        assert (sel h1 x == v);
        lemma_sel_same_addr' h1 x r;
        inversion a t;
        assert ((to_Type_solve t).satisfy v h0 contains_pred);
        (to_Type_solve t).satisfy_monotonic v contains_pred h0 h1;
        assert ((to_Type_solve t).satisfy v h1 contains_pred)
      end
    end
  end


let lemma_declassify_preserves_contains t (x:ref (to_Type t)) (h0 h1:lheap) : Lemma
  (requires (
    modifies_none h0 h1 /\
    h0 `lheap_rel` h1 /\
    equal_dom h0 h1 /\
    modifies_classification (only x) h0 h1 /\
    (to_Type_solve (InvT_Ref t)).satisfy x h0 contains_pred /\ 
    (to_Type_solve t).satisfy (sel h0 x) h0 contains_pred /\
    inv_points_to h0 contains_pred))
  (ensures (inv_points_to h1 contains_pred)) =
  introduce forall a (r:ref (to_Type a)).
      (witnessable_ref _ #(to_Type_solve a)).satisfy r h1 contains_pred ==> 
        (to_Type_solve a).satisfy (sel h1 r) h1 contains_pred
  with begin
    let refw = witnessable_ref _ #(to_Type_solve a) in
    introduce refw.satisfy r h1 contains_pred ==> (to_Type_solve a).satisfy (sel h1 r) h1 contains_pred
    with _. begin
      introduce refw.satisfy r h0 contains_pred ==> (to_Type_solve a).satisfy (sel h1 r) h1 contains_pred
      with _. (to_Type_solve a).satisfy_monotonic (sel h0 r) contains_pred h0 h1;
      
      introduce ~(refw.satisfy r h0 contains_pred) ==> (to_Type_solve a).satisfy (sel h1 r) h1 contains_pred
      with _. begin
        assert (addr_of r == addr_of x);
        lemma_sel_same_addr' h1 x r;
        assert (to_Type_solve a == to_Type_solve t);
        inversion a t;
        assert (to_Type_solve a == to_Type_solve t);

        assert ((to_Type_solve t).satisfy (sel h0 x) h0 contains_pred);
        (to_Type_solve t).satisfy_monotonic (sel h0 x) contains_pred h0 h1;
        assert (sel h0 x == sel h1 x);
        assert ((to_Type_solve t).satisfy (sel h1 x) h1 contains_pred);
        assert ((to_Type_solve a).satisfy (sel h1 r) h1 contains_pred)
      end
    end
  end

let lemma_declassify_preserves_is_low t (x:ref (to_Type t)) (h0 h1:lheap) : Lemma
  (requires (
    modifies_none h0 h1 /\
    h0 `lheap_rel` h1 /\
    equal_dom h0 h1 /\
    modifies_classification (only x) h0 h1 /\
    (to_Type_solve (InvT_Ref t)).satisfy x h1 is_low_pred /\
    (to_Type_solve t).satisfy (sel h0 x) h0 is_low_pred /\
    inv_points_to h0 is_low_pred))
  (ensures (inv_points_to h1 is_low_pred)) =
  introduce forall a (inv:lheap -> Type0) (r:ref (to_Type a)).
      (witnessable_ref _ #(to_Type_solve a)).satisfy r h1 is_low_pred ==> 
        (to_Type_solve a).satisfy (sel h1 r) h1 is_low_pred
  with begin
    let refw = witnessable_ref _ #(to_Type_solve a) in
    introduce refw.satisfy r h1 is_low_pred ==> (to_Type_solve a).satisfy (sel h1 r) h1 is_low_pred
    with _. begin
      introduce refw.satisfy r h0 is_low_pred ==> (to_Type_solve a).satisfy (sel h1 r) h1 is_low_pred
      with _. (to_Type_solve a).satisfy_monotonic (sel h0 r) is_low_pred h0 h1;
      
      introduce ~(refw.satisfy r h0 is_low_pred) ==> (to_Type_solve a).satisfy (sel h1 r) h1 is_low_pred
      with _. begin
        assert (addr_of r == addr_of x);
        lemma_sel_same_addr' h1 x r;
        inversion a t;
        (to_Type_solve t).satisfy_monotonic (sel h0 x) is_low_pred h0 h1
      end
    end
  end

let lemma_ist_alloc_preserves_contains t (x:ref (to_Type t)) (v:to_Type t) (h0 h1:lheap) : Lemma
  (requires (
    h0 `lheap_rel` h1 /\
    h1 == upd h0 x v /\ 
    fresh x h0 h1 /\ 
    modifies Set.empty h0 h1 /\
    modifies_classification Set.empty h0 h1 /\
    sel h1 x == v /\ 
    label_of x h1 == High /\
    is_mm x == false /\
    (to_Type_solve t).satisfy v h0 contains_pred /\
    inv_points_to h0 contains_pred))
  (ensures (
    inv_points_to h1 contains_pred)) = 
  introduce forall a (r:ref (to_Type a)).
      (witnessable_ref _ #(to_Type_solve a)).satisfy r h1 contains_pred ==> 
        (to_Type_solve a).satisfy (sel h1 r) h1 contains_pred
  with begin
    introduce (witnessable_ref _ #(to_Type_solve a)).satisfy r h1 contains_pred 
      ==> (to_Type_solve a).satisfy (sel h1 r) h1 contains_pred
    with _. begin
      introduce addr_of r =!= addr_of x ==> (to_Type_solve a).satisfy (sel h1 r) h1 contains_pred with _. begin
        eliminate_inv_points_to h0 a r contains_pred;
        assert (h0 `contains` r);
        (to_Type_solve a).satisfy_monotonic (sel h0 r) contains_pred h0 h1
      end;
      introduce addr_of r == addr_of x ==> (to_Type_solve a).satisfy (sel h1 r) h1 contains_pred with _. begin
        assert (sel h1 x == v);
        lemma_sel_same_addr' h1 x r;
        inversion a t;
        (to_Type_solve t).satisfy_monotonic v contains_pred h0 h1
      end
    end
  end

let lemma_ist_alloc_preserves_is_low t (x:ref (to_Type t)) (v:to_Type t) (h0 h1:lheap) : Lemma
  (requires (
    h0 `lheap_rel` h1 /\
    h1 == upd h0 x v /\ 
    fresh x h0 h1 /\ 
    modifies Set.empty h0 h1 /\
    modifies_classification Set.empty h0 h1 /\
    sel h1 x == v /\ 
    label_of x h1 == High /\
    is_mm x == false /\
    (to_Type_solve t).satisfy v h0 contains_pred /\
    inv_points_to h0 is_low_pred))
  (ensures (
    inv_points_to h1 is_low_pred)) = 
  introduce forall a (r:ref (to_Type a)).
      (witnessable_ref _ #(to_Type_solve a)).satisfy r h1 is_low_pred ==> 
        (to_Type_solve a).satisfy (sel h1 r) h1 is_low_pred
  with begin
    introduce (witnessable_ref _ #(to_Type_solve a)).satisfy r h1 is_low_pred 
      ==> (to_Type_solve a).satisfy (sel h1 r) h1 is_low_pred
    with _. begin
      introduce addr_of r =!= addr_of x ==> (to_Type_solve a).satisfy (sel h1 r) h1 is_low_pred with _. begin
        eliminate_inv_points_to h0 a r is_low_pred;
        assert (h0 `contains` r);
        (to_Type_solve a).satisfy_monotonic (sel h0 r) is_low_pred h0 h1;
        assert ((to_Type_solve a).satisfy (sel h1 r) h1 is_low_pred)
      end;
      introduce addr_of r == addr_of x ==> (to_Type_solve a).satisfy (sel h1 r) h1 is_low_pred with _. begin
        assert (sel h1 x == v);
        lemma_sel_same_addr' h1 x r;
        assert (label_of r h1 == Low);
        assert (label_of x h1 == High);
        assert (r == x);
        assert False
      end
    end
  end


let ist_alloc (#t:inv_typ) (init:to_Type t)
: IST (ref (to_Type t))
    (fun h -> 
      (to_Type_solve t).satisfy init h contains_pred)
    (alloc_post #(to_Type t) init)
=
  let h0 = get () in
  let r = alloc init in
  let h1 = get () in
  lemma_ist_alloc_preserves_contains t r init h0 h1;
  lemma_ist_alloc_preserves_is_low t r init h0 h1;
  r