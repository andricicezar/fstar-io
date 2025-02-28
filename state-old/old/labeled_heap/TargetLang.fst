module TargetLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Labeled.Monotonic.Heap
open Labeled.MST
open Witnessable

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


effect IST (a:Type) (pre:st_pre) (post: (h:lheap -> Tot (st_post' a (pre h)))) =
  ST a 
    (requires (fun h0      -> inv_low_contains h0 /\ pre h0))
    (ensures  (fun h0 r h1 -> inv_low_contains h1 /\ post h0 r h1))


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


open STLC

let rec to_inv_typ (t:typ0) : inv_typ =
  match t with
  | TUnit -> InvT_Unit
  | TNat -> InvT_Nat
  | TSum t1 t2 -> InvT_Sum (to_inv_typ t1) (to_inv_typ t2)
  | TPair t1 t2 -> InvT_Pair (to_inv_typ t1) (to_inv_typ t2)
  | TRef t -> InvT_Ref (to_inv_typ t)
  | TLList t -> InvT_LList (to_inv_typ t)

(** elab_typ0 should be in translation file, but it is here because 
    we need it to write our invariants **)

unfold
let elab_typ0 (t:typ0) : Type u#0 = 
  to_Type (to_inv_typ t)

unfold
let elab_typ0_tc (t:typ0) : witnessable (elab_typ0 t) =
  to_Type_solve (to_inv_typ t)

unfold let shallowly_contained_low (#a:Type) (v:a) {| c:witnessable a |} (h:lheap) =
  c.satisfy v h contains_pred /\ c.satisfy v h is_low_pred

unfold let pre_tgt_arrow
  (#t1:Type) {| c1 : witnessable t1 |}
  (x:t1) (h0:lheap) =
  inv_low_contains h0 /\
  shallowly_contained_low x #c1 h0

unfold let post_tgt_arrow
  (#t1:Type) {| c1 : witnessable t1 |}
  (#t2:Type) {| c2 : witnessable t2 |}
  (x:t1) (h0:lheap) (r:t2) (h1:lheap) =
  inv_low_contains h1 /\
  modifies_only_label Low h0 h1 /\                       (* allows low references to be modified *)
  modifies_classification Set.empty h0 h1 /\             (* no modifications of the classification *)
  shallowly_contained_low r #c2 h1

let mk_tgt_arrow
  (t1:Type) {| c1 : witnessable t1 |}
  (t2:Type) {| c2 : witnessable t2 |}
= x:t1 -> ST t2 
    (requires (pre_tgt_arrow #t1 #c1 x ))
    (ensures (post_tgt_arrow #t1 #c1 #t2 #c2 x))

open FStar.Universe

let rec _elab_typ (t:typ) : tt:Type u#1 & witnessable tt =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = _elab_typ t1 in
    let tt2 = _elab_typ t2 in
    (| mk_tgt_arrow (dfst tt1) #(dsnd tt1) (dfst tt2) #(dsnd tt2),
       witnessable_arrow (dfst tt1) (dfst tt2) pre_tgt_arrow post_tgt_arrow
    |)
  end 
  | TUnit -> (| raise_t unit, solve |)
  | TNat -> (| raise_t int, solve |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 in
    let (| tt2, c_tt2 |) = _elab_typ t2 in
    (| either tt1 tt2, witnessable_sum tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 in
    let (| tt2, c_tt2 |) = _elab_typ t2 in
    (| tt1 * tt2, witnessable_pair tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef _ ->
    let tt = elab_typ0 t in
    let c_tt = elab_typ0_tc t in
    (| raise_t tt, witnessable_univ_raise _ #c_tt |)
  | TLList t ->
    let tt = elab_typ0 t in
    let c_tt = elab_typ0_tc t in
    (| raise_t (linkedList tt), witnessable_univ_raise _ #(witnessable_llist tt #c_tt) |)

let elab_typ (t:typ) : Type =
  dfst (_elab_typ t)

let elab_typ_tc (t:typ) : witnessable (elab_typ t) =
  dsnd (_elab_typ t)

let eliminate_inv_low' h (a:typ0) (r:ref (elab_typ0 a)) :
  Lemma
    (requires (inv_points_to h is_low_pred))
    (ensures (
      (witnessable_ref _ #(elab_typ0_tc a)).satisfy r h is_low_pred ==> 
        (elab_typ0_tc a).satisfy (sel h r) h is_low_pred
    )) = eliminate_inv_low h (to_inv_typ a) r

let eliminate_inv_contains' (h:lheap) (a:typ0) (r:ref (elab_typ0 a)) :
  Lemma
    (requires (inv_points_to h contains_pred))
    (ensures (
      (witnessable_ref _ #(elab_typ0_tc a)).satisfy r h contains_pred ==> 
        (elab_typ0_tc a).satisfy (sel h r) h contains_pred
    )) = eliminate_inv_contains h (to_inv_typ a) inv_low_contains r

(** ** Elaboration of the operations **) 

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

(** ** Examples **) 

val ctx_update_ref_test : 
  elab_typ (TArr (TRef TNat) TUnit)
let ctx_update_ref_test y =
  let y : ref int = downgrade_val y in
  elab_write #TNat y (!y + 1);
  raise_val ()

val ctx_update_multiple_refs_test : 
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit))
let ctx_update_multiple_refs_test x =
  let x : ref (ref int) = downgrade_val x in
  mst_witness (contains_pred x);
  mst_witness (is_low_pred x);
  let cb : elab_typ (TArr (TRef TNat) TUnit) = (fun y ->
    let y : ref int = downgrade_val y in
    let h0 = get () in
    mst_recall (contains_pred x);
    let ix : ref int = !x in
    mst_recall (is_low_pred x);   
    eliminate_inv_contains' h0 (TRef TNat) x;
    elab_write #TNat ix (!ix + 1);
    let h1 = get () in
    elab_write #(TRef TNat) x y;
    let h2 = get () in
    elab_write #TNat y (!y + 5);
    let h3 = get () in
    eliminate_inv_low' h0 (TRef TNat) x;
    lemma_modifies_only_label_trans Low h0 h1 h2;
    lemma_modifies_only_label_trans Low h0 h2 h3;
    assert (modifies_only_label Low h0 h3);
    let r = raise_val () in
    assert (shallowly_contained_low r h3);
    assert (inv_low_contains h3);
    assert (modifies_classification Set.empty h0 h3);
    r
  ) in
  cb

val ctx_HO_test1 : 
  elab_typ (TArr (TRef (TPair (TRef TNat) (TRef TNat))) (TArr TUnit TUnit))
let ctx_HO_test1 xs =
  let xs : ref ((ref int) * ref int) = downgrade_val xs in
  let (x', x'') = !xs in
  let h0 = get () in
  eliminate_inv_contains' h0 (TPair (TRef TNat) (TRef TNat)) xs;
  eliminate_inv_low' h0 (TPair (TRef TNat) (TRef TNat)) xs;
  elab_write #(TPair (TRef TNat) (TRef TNat)) xs (x', x');
  mst_witness (is_low_pred xs);
  mst_witness (is_low_pred x');
  mst_witness (is_low_pred x'');
  (fun _ -> 
    mst_recall (is_low_pred xs);
    mst_recall (is_low_pred x');
    mst_recall (is_low_pred x'');
    elab_write #(TPair (TRef TNat) (TRef TNat)) xs (x', x'');
    raise_val ())
  
val ctx_identity :
  elab_typ (TArr (TRef TNat) (TRef TNat))
let ctx_identity x = x

val ctx_HO_test2 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test2 f =
  let h0 = get () in
  let x:ref int = downgrade_val (f (raise_val ())) in
  let h1 = get () in
  elab_write #TNat x (!x + 1);
  let h2 = get () in
  assert (modifies_only_label Low h0 h2);
  raise_val ()

val ctx_swap_ref_test :
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef (TRef TNat)) TUnit))
let ctx_swap_ref_test x =
  let x : ref (ref int) = downgrade_val x in
  mst_witness (contains_pred x);
  mst_witness (is_low_pred x);
  let cb : elab_typ (TArr (TRef (TRef TNat)) TUnit) = (fun y ->
    let y : ref (ref int) = downgrade_val y in
    let h0 = get () in
    mst_recall (contains_pred x);
    mst_recall (is_low_pred x);
    eliminate_inv_contains' h0 (TRef TNat) x;
    eliminate_inv_low' h0 (TRef TNat) x;
    
    let z = !x in
    let t = !y in
    elab_write #(TRef TNat) x t;
  
    let h1 = get () in
    elab_write #(TRef TNat) y z;
    let h2 = get () in

    assert (modifies_classification Set.empty h0 h1);
    lemma_modifies_only_label_trans Low h0 h1 h2;
    assert (modifies_only_label Low h0 h2); // we have an SMT Pat for this, but it does not kick in
    assert (modifies_classification Set.empty h0 h2);
    assert (inv_low_contains h2);
    let r = raise_val () in
    assert (shallowly_contained_low r h2);
    r) in
  cb

val ctx_dynamic_alloc_test :
   elab_typ (TArr TUnit (TRef TNat))
let ctx_dynamic_alloc_test _ = 
  let v = elab_alloc #TNat 0 in 
  raise_val v

val ctx_HO_test3 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test3 f =
  let x:ref int = downgrade_val (f (raise_val ())) in
  let y:ref int = elab_alloc #TNat (!x + 1) in
  raise_val ()

val ctx_returns_callback_test :
  elab_typ (TArr TUnit (TArr TUnit TUnit))
let ctx_returns_callback_test _ =
  let x: ref int = elab_alloc #TNat 13 in
  mst_witness (contains_pred x);
  mst_witness (is_low_pred x);
  let cb : elab_typ (TArr TUnit TUnit) = (fun _ ->
    mst_recall (contains_pred x);
    mst_recall (is_low_pred x);
    elab_write #TNat x (!x % 5);
    raise_val ()
  ) in
  cb

val ctx_HO_test4 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test4 f =
  let x:ref int = downgrade_val (f (raise_val ())) in
  let y:ref (ref int) = elab_alloc #(TRef TNat) x in
  raise_val ()

val progr_sep_test: 
  #rp: ref int -> 
  ctx:(elab_typ (TArr TUnit TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
         
let progr_sep_test #rp f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  downgrade_val (f (raise_val ()))

val progr_declassify :
  rp: ref int -> 
  ctx:(elab_typ (TArr (TRef TNat) TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 -> True))
let progr_declassify rp f =
  let h0 = get () in
  declassify_low' #TNat rp;
  let h1 = get () in
  lemma_declassify_preserves_is_low InvT_Nat rp h0 h1;
  let r = downgrade_val (f (raise_val rp)) in  
  r

val progr_declassify_nested:
  rp: ref (ref int) -> 
  ctx:(elab_typ (TArr (TRef (TRef TNat)) TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 -> True))
let progr_declassify_nested rp f =
  let h0 = get () in
  eliminate_inv_contains' h0 (TRef TNat) rp;

  let p : ref int = !rp in
  declassify_low' #TNat p;
  let h1 = get () in
  lemma_declassify_preserves_is_low InvT_Nat p h0 h1;
  declassify_low' #(TRef TNat) rp;
  let h2 = get () in
  lemma_declassify_preserves_is_low (InvT_Ref InvT_Nat) rp h1 h2;
  // let r = elab_alloc (!rp) in (* <-- needed a copy here! *) 
  downgrade_val (f (raise_val rp))

val progr_secret_unchanged_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr TUnit TUnit)) ->
  IST unit 
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High /\
      satisfy rs h0 is_low_pred))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp))
         
let progr_secret_unchanged_test rp rs ctx = 
  let secret: ref int = ist_alloc #InvT_Nat 0 in
  downgrade_val (ctx (raise_val ()));
  let v = !secret in
  assert (v == 0);
  ()

val progr_passing_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr (TArr TUnit TUnit) TUnit)) ->
  IST unit 
    (requires (fun h0 ->
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High /\
      satisfy rs h0 is_low_pred))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context

// TODO: the callback of the program should be able to modify rp
let progr_passing_callback_test rp rs f =
  let secret: ref int = ist_alloc #InvT_Nat 0 in
  let h0 = get () in
  declassify_low' #TNat secret;
  let h1 = get () in
  lemma_declassify_preserves_is_low InvT_Nat secret h0 h1;
  mst_witness (contains_pred secret);
  mst_witness (is_low_pred secret);
  let cb: elab_typ (TArr TUnit TUnit) = (fun _ -> 
    mst_recall (contains_pred secret);
    mst_recall (is_low_pred secret);
    elab_write #TNat secret (!secret + 1);
    raise_val ()) in
  downgrade_val (f cb);
  ()

val progr_getting_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr TUnit (TArr TUnit TUnit))) ->
  IST unit 
    (requires (fun h0 ->
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High /\
      satisfy rs h0 is_low_pred))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp))
let progr_getting_callback_test rp rs f =
  let h0 = get () in
  let cb = f (raise_val ()) in
  let h1 = get () in
  downgrade_val (cb (raise_val ()));
  let h2 = get () in
  lemma_modifies_only_label_trans Low h0 h1 h2;
  assert (modifies_only_label Low h0 h2);
  ()