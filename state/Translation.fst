module Translation

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Labeled.Monotonic.Heap
open Labeled.MST
open Witnessable
open TargetLang
open STLC

let elab_typ' t = elab_typ t inv_low_contains
let elab_typ_tc' t = elab_typ_tc t inv_low_contains

let eliminate_inv_low' h a (r:ref (elab_typ' a)) :
  Lemma
    (requires (inv_points_to h is_low_pred))
    (ensures (
      (witnessable_ref (elab_typ' a) #(elab_typ_tc' a)).satisfy r h is_low_pred ==> 
        (elab_typ_tc' a).satisfy (sel h r) h is_low_pred
    )) = eliminate_inv_low h a inv_low_contains r

let eliminate_inv_contains' (h:lheap) (a:typ) (r:ref (elab_typ' a)) :
  Lemma
    (requires (inv_points_to h contains_pred))
    (ensures (
      (witnessable_ref (elab_typ' a) #(elab_typ_tc' a)).satisfy r h contains_pred ==> 
        (elab_typ_tc' a).satisfy (sel h r) h contains_pred
    )) = eliminate_inv_contains h a inv_low_contains r

(** ** Elaboration of the operations **) 

(** Nik's workaround:
Here's a possible workaround until we figure out if and how to support reasoning about disequalities on effectful function types
Is it possible for you to work with a type isomorphic to (int -> Dv int)? For example:
type wrap_div (a:Type) = | WrapDiv of a
let unwrap_div (x:wrap_div 'a) : 'a = match x with | WrapDiv y -> y

let _ = assert (int =!= wrap_div (int -> Dv int))
I.e., use a fresh inductive type to wrap each effecftul function type? So, you'd have wrap_div, wrap_st etc?

Catalin's question: can't we use tactics to prove this?
*)
let rec inversion (a:typ) (inv:lheap -> Type0) (xa:typ) :
  Lemma
    (requires (elab_typ a inv == elab_typ' xa))
    (ensures (a == xa /\ elab_typ_tc a inv == elab_typ_tc' xa)) =
    match a, xa with
    | TNat, TNat -> ()
    | TUnit, TUnit -> ()
    | TSum t1 t2, TSum t1' t2' -> begin
      assume (elab_typ t1 inv == elab_typ' t1');
      inversion t1 inv t1';
      assume (elab_typ t2 inv == elab_typ' t2');
      inversion t2 inv t2'
    end
    | TPair t1 t2, TPair t1' t2' -> begin
      assume (elab_typ t1 inv == elab_typ' t1');
      inversion t1 inv t1';
      assume (elab_typ t2 inv == elab_typ' t2');
      inversion t2 inv t2'
    end
    | TRef t, TRef t' -> begin
      assume (elab_typ t inv == elab_typ' t');
      inversion t inv t'
    end
    | TArr x y, TArr x' y' ->
      assume (elab_typ x inv == elab_typ' x');
      inversion x inv x';
      assume (elab_typ y inv == elab_typ' y');
      inversion y inv y';
      assume (inv == inv_low_contains)
    | TLList a, TLList b ->
      assume (elab_typ a inv == elab_typ' b);
      inversion a inv b
    | _, _ -> admit () (* TODO: other cases are impossible because of the pre-condition*)

let lemma_write_preserves_is_low (t:typ) (x:ref (elab_typ' t)) (v:elab_typ' t) (h0 h1:lheap) : Lemma
  (requires (
    h0 `lheap_rel` h1 /\
    equal_dom h0 h1 /\
    modifies (Set.singleton (addr_of x)) h0 h1 /\
    modifies_classification Set.empty h0 h1 /\
    sel h1 x == v /\
    (elab_typ_tc' (TRef t)).satisfy x h0 is_low_pred /\
    (elab_typ_tc' t).satisfy v h0 is_low_pred /\
    inv_points_to h0 is_low_pred))
  (ensures (
    inv_points_to h1 is_low_pred)) = 
  introduce forall (a:typ) (hinv:lheap -> Type0) (r:ref (elab_typ a hinv)).
      (witnessable_ref (elab_typ a hinv) #(elab_typ_tc a hinv)).satisfy r h1 is_low_pred ==> 
        (elab_typ_tc a hinv).satisfy (sel h1 r) h1 is_low_pred
  with begin
    introduce (witnessable_ref (elab_typ a hinv) #(elab_typ_tc a hinv)).satisfy r h1 is_low_pred 
      ==> (elab_typ_tc a hinv).satisfy (sel h1 r) h1 is_low_pred
    with _. begin
      introduce addr_of r =!= addr_of x ==> (elab_typ_tc a hinv).satisfy (sel h1 r) h1 is_low_pred with _. begin
        eliminate_inv_points_to h0 a hinv r is_low_pred;
        (elab_typ_tc a hinv).satisfy_monotonic (sel h0 r) is_low_pred h0 h1
      end;
      introduce addr_of r == addr_of x ==> (elab_typ_tc a hinv).satisfy (sel h1 r) h1 is_low_pred with _. begin
        assert (sel h1 x == v);
        lemma_sel_same_addr' h1 x r;
        inversion a hinv t;
        assert ((elab_typ_tc' t).satisfy v h0 is_low_pred);
        (elab_typ_tc' t).satisfy_monotonic v is_low_pred h0 h1;
        assert ((elab_typ_tc' t).satisfy v h1 is_low_pred)
      end
    end
  end

let lemma_write_preserves_contains (t:typ) (x:ref (elab_typ' t)) (v:elab_typ' t) (h0 h1:lheap) : Lemma
  (requires (
    h0 `lheap_rel` h1 /\
    equal_dom h0 h1 /\
    modifies (Set.singleton (addr_of x)) h0 h1 /\
    modifies_classification Set.empty h0 h1 /\
    sel h1 x == v /\
    (elab_typ_tc' (TRef t)).satisfy x h0 contains_pred /\
    (elab_typ_tc' t).satisfy v h0 contains_pred /\
    inv_points_to h0 contains_pred))
  (ensures (
    inv_points_to h1 contains_pred)) = 
  introduce forall (a:typ) (hinv:lheap -> Type0) (r:ref (elab_typ a hinv)).
      (witnessable_ref (elab_typ a hinv) #(elab_typ_tc a hinv)).satisfy r h1 contains_pred ==> 
        (elab_typ_tc a hinv).satisfy (sel h1 r) h1 contains_pred
  with begin
    introduce (witnessable_ref (elab_typ a hinv) #(elab_typ_tc a hinv)).satisfy r h1 contains_pred 
      ==> (elab_typ_tc a hinv).satisfy (sel h1 r) h1 contains_pred
    with _. begin
      introduce addr_of r =!= addr_of x ==> (elab_typ_tc a hinv).satisfy (sel h1 r) h1 contains_pred with _. begin
        eliminate_inv_points_to h0 a hinv r contains_pred;
        (elab_typ_tc a hinv).satisfy_monotonic (sel h0 r) contains_pred h0 h1
      end;
      introduce addr_of r == addr_of x ==> (elab_typ_tc a hinv).satisfy (sel h1 r) h1 contains_pred with _. begin
        assert (sel h1 x == v);
        lemma_sel_same_addr' h1 x r;
        inversion a hinv t;
        assert ((elab_typ_tc' t).satisfy v h0 contains_pred);
        (elab_typ_tc' t).satisfy_monotonic v contains_pred h0 h1;
        assert ((elab_typ_tc' t).satisfy v h1 contains_pred)
      end
    end
  end


let lemma_declassify_preserves_inv (xa:typ) (x:ref (elab_typ' xa)) (h0 h1:lheap) : Lemma
  (requires (modifies_none h0 h1 /\
            h0 `lheap_rel` h1 /\
            equal_dom h0 h1 /\
            modifies_classification (only x) h0 h1 /\
            (elab_typ_tc' (TRef xa)).satisfy x h0 contains_pred /\ 
            shallowly_contained_low #_ #(elab_typ_tc' xa) (sel h0 x) h0 /\
            shallowly_contained_low #_ #(elab_typ_tc' (TRef xa)) x h1 /\
            inv_points_to h0 is_low_pred))
  (ensures (inv_points_to h1 is_low_pred)) =
  introduce forall (a:typ) (inv:lheap -> Type0) (r:ref (elab_typ a inv)).
      (witnessable_ref _ #(elab_typ_tc a inv)).satisfy r h1 is_low_pred ==> 
        (elab_typ_tc a inv).satisfy (sel h1 r) h1 is_low_pred
  with begin
    let refw = witnessable_ref _ #(elab_typ_tc a inv) in
    introduce refw.satisfy r h1 is_low_pred ==> (elab_typ_tc a inv).satisfy (sel h1 r) h1 is_low_pred
    with _. begin
      introduce refw.satisfy r h0 is_low_pred ==> (elab_typ_tc a inv).satisfy (sel h1 r) h1 is_low_pred
      with _. (elab_typ_tc a inv).satisfy_monotonic (sel h0 r) is_low_pred h0 h1;
      
      introduce ~(refw.satisfy r h0 is_low_pred) ==> (elab_typ_tc a inv).satisfy (sel h1 r) h1 is_low_pred
      with _. begin
        assert (addr_of r == addr_of x);
        lemma_sel_same_addr' h1 x r;
        assert (elab_typ a inv == elab_typ' xa);
        inversion a inv xa;
        assert (elab_typ_tc a inv == elab_typ_tc' xa);

        assert ((elab_typ_tc' xa).satisfy (sel h0 x) h0 is_low_pred);
        (elab_typ_tc' xa).satisfy_monotonic (sel h0 x) is_low_pred h0 h1;
        assert (sel h0 x == sel h1 x);
        assert ((elab_typ_tc' xa).satisfy (sel h1 x) h1 is_low_pred);
        assert ((elab_typ_tc a inv).satisfy (sel h1 r) h1 is_low_pred)
      end
    end
  end

let lemma_ist_alloc_preserves_contains (t:typ) (x:ref (elab_typ' t)) (v:elab_typ' t) (h0 h1:lheap) : Lemma
  (requires (
    h0 `lheap_rel` h1 /\
    h1 == upd h0 x v /\ 
    fresh x h0 h1 /\ 
    modifies Set.empty h0 h1 /\
    modifies_classification Set.empty h0 h1 /\
    sel h1 x == v /\ 
    label_of x h1 == High /\
    is_mm x == false /\
    (elab_typ_tc' t).satisfy v h0 contains_pred /\
    inv_points_to h0 contains_pred))
  (ensures (
    inv_points_to h1 contains_pred)) = 
  introduce forall (a:typ) (hinv:lheap -> Type0) (r:ref (elab_typ a hinv)).
      (witnessable_ref (elab_typ a hinv) #(elab_typ_tc a hinv)).satisfy r h1 contains_pred ==> 
        (elab_typ_tc a hinv).satisfy (sel h1 r) h1 contains_pred
  with begin
    introduce (witnessable_ref (elab_typ a hinv) #(elab_typ_tc a hinv)).satisfy r h1 contains_pred 
      ==> (elab_typ_tc a hinv).satisfy (sel h1 r) h1 contains_pred
    with _. begin
      introduce addr_of r =!= addr_of x ==> (elab_typ_tc a hinv).satisfy (sel h1 r) h1 contains_pred with _. begin
        eliminate_inv_points_to h0 a hinv r contains_pred;
        assert (h0 `contains` r);
        (elab_typ_tc a hinv).satisfy_monotonic (sel h0 r) contains_pred h0 h1;
        assert ((elab_typ_tc a hinv).satisfy (sel h1 r) h1 contains_pred)
      end;
      introduce addr_of r == addr_of x ==> (elab_typ_tc a hinv).satisfy (sel h1 r) h1 contains_pred with _. begin
        assert (sel h1 x == v);
        lemma_sel_same_addr' h1 x r;
        inversion a hinv t;
        assert ((elab_typ_tc' t).satisfy v h0 contains_pred);
        (elab_typ_tc' t).satisfy_monotonic v contains_pred h0 h1;
        assert ((elab_typ_tc' t).satisfy v h1 contains_pred)
      end
    end
  end

let lemma_ist_alloc_preserves_is_low (t:typ) (x:ref (elab_typ' t)) (v:elab_typ' t) (h0 h1:lheap) : Lemma
  (requires (
    h0 `lheap_rel` h1 /\
    h1 == upd h0 x v /\ 
    fresh x h0 h1 /\ 
    modifies Set.empty h0 h1 /\
    modifies_classification Set.empty h0 h1 /\
    sel h1 x == v /\ 
    label_of x h1 == High /\
    is_mm x == false /\
    (elab_typ_tc' t).satisfy v h0 contains_pred /\
    inv_points_to h0 is_low_pred))
  (ensures (
    inv_points_to h1 is_low_pred)) = 
  introduce forall (a:typ) (hinv:lheap -> Type0) (r:ref (elab_typ a hinv)).
      (witnessable_ref (elab_typ a hinv) #(elab_typ_tc a hinv)).satisfy r h1 is_low_pred ==> 
        (elab_typ_tc a hinv).satisfy (sel h1 r) h1 is_low_pred
  with begin
    introduce (witnessable_ref (elab_typ a hinv) #(elab_typ_tc a hinv)).satisfy r h1 is_low_pred 
      ==> (elab_typ_tc a hinv).satisfy (sel h1 r) h1 is_low_pred
    with _. begin
      introduce addr_of r =!= addr_of x ==> (elab_typ_tc a hinv).satisfy (sel h1 r) h1 is_low_pred with _. begin
        eliminate_inv_points_to h0 a hinv r is_low_pred;
        assert (h0 `contains` r);
        (elab_typ_tc a hinv).satisfy_monotonic (sel h0 r) is_low_pred h0 h1;
        assert ((elab_typ_tc a hinv).satisfy (sel h1 r) h1 is_low_pred)
      end;
      introduce addr_of r == addr_of x ==> (elab_typ_tc a hinv).satisfy (sel h1 r) h1 is_low_pred with _. begin
        assert (sel h1 x == v);
        lemma_sel_same_addr' h1 x r;
        assert (label_of r h1 == Low);
        assert (label_of x h1 == High);
        assert False
      end
    end
  end

let elab_write (#t:typ) (r:ref (elab_typ' t)) (v:elab_typ' t) 
: IST unit
  (requires (fun h0 -> 
    shallowly_contained_low #_ #(elab_typ_tc' (TRef t)) r h0 /\
    shallowly_contained_low #_ #(elab_typ_tc' t) v h0))
  (ensures (fun h0 () h1 ->
    write_post r v h0 () h1 /\
    modifies_only_label Low h0 h1 /\
    shallowly_contained_low #_ #(elab_typ_tc' (TRef t)) r h1))
= let h0 = get () in
  write r v;
  let h1 = get () in
  lemma_write_preserves_is_low t r v h0 h1;
  lemma_write_preserves_contains t r v h0 h1;
  ()

let ist_alloc (#t:typ) (init:elab_typ' t)
: IST (ref (elab_typ' t))
    (fun h -> 
      (elab_typ_tc' t).satisfy init h contains_pred)
    (alloc_post #(elab_typ' t) init)
=
  let h0 = get () in
  let r = alloc init in
  let h1 = get () in
  lemma_ist_alloc_preserves_contains t r init h0 h1;
  lemma_ist_alloc_preserves_is_low t r init h0 h1;
  r

let declassify_low' (#t:typ) (r:ref (elab_typ' t)) : ST unit
  (fun h -> (elab_typ_tc' (TRef t)).satisfy r h contains_pred /\ inv_points_to h contains_pred)
  (fun h0 () h1 -> 
    inv_points_to h1 contains_pred /\
    shallowly_contained_low #_ #(elab_typ_tc' (TRef t)) r h1 /\
    declassify_post r Low h0 () h1)
=
  declassify r Low;
  let h1 = get () in
  assume (inv_points_to h1 contains_pred)

val elab_alloc (#t:typ) (init:elab_typ' t)
: IST (ref (elab_typ' t))
  (requires (fun h0 ->
    shallowly_contained_low #_ #(elab_typ_tc' t) init h0))
  (ensures (fun h0 r h1 -> 
    fresh r h0 h1 /\ 
    modifies Set.empty h0 h1 /\
    modifies_classification Set.empty h0 h1 /\
    sel h1 r == init /\
    shallowly_contained_low #_ #(elab_typ_tc' (TRef t)) r h1))
let elab_alloc #t init = 
  let h0 = get () in
  let r : ref (elab_typ' t) = ist_alloc init in
  let h1 = get () in
  declassify_low' r;
  let h2 = get () in
  (elab_typ_tc' t).satisfy_monotonic init is_low_pred h0 h1;
  lemma_declassify_preserves_inv t r h1 h2;
  assert (inv_points_to h2 is_low_pred);
  r

(** ** Examples **) 

val ctx_update_ref_test : 
  elab_typ' (TArr (TRef TNat) TUnit)
let ctx_update_ref_test (y:ref int) =
  elab_write #TNat y (!y + 5);
  ()

val ctx_update_multiple_refs_test : 
  elab_typ' (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit))
let ctx_update_multiple_refs_test (x:ref (ref int)) =
  mst_witness (contains_pred x);
  mst_witness (is_low_pred x);
  let cb : elab_typ' (TArr (TRef TNat) TUnit) = (fun (y:ref int) ->
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
    let r = () in
    assert (shallowly_contained_low r h3);
    assert (inv_low_contains h3);
    assert (modifies_classification Set.empty h0 h3);
    r
  ) in
  cb

val ctx_HO_test1 : 
  elab_typ' (TArr (TRef (TPair (TRef TNat) (TRef TNat))) (TArr TUnit TUnit))
let ctx_HO_test1 (xs:ref ((ref int) * ref int)) =
  let (x', x'') = !xs in
  let h0 = get () in
  eliminate_inv_contains' h0 (TPair (TRef TNat) (TRef TNat)) xs;
  eliminate_inv_low' h0 (TPair (TRef TNat) (TRef TNat)) xs;
  elab_write #(TPair (TRef TNat) (TRef TNat)) xs (x', x');
  mst_witness (is_low_pred xs);
  mst_witness (is_low_pred x');
  mst_witness (is_low_pred x'');
  (fun () -> 
    mst_recall (is_low_pred xs);
    mst_recall (is_low_pred x');
    mst_recall (is_low_pred x'');
    elab_write #(TPair (TRef TNat) (TRef TNat)) xs (x', x''))
  
val ctx_identity :
  elab_typ' (TArr (TRef TNat) (TRef TNat))
let ctx_identity x = x

val ctx_HO_test2 :
  elab_typ' (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test2 f =
  let h0 = get () in
  let x:ref int = f () in
  let h1 = get () in
  elab_write #TNat x (!x + 1);
  let h2 = get () in
  assert (modifies_only_label Low h0 h2);
  ()

val ctx_swap_ref_test :
  elab_typ' (TArr (TRef (TRef TNat)) (TArr (TRef (TRef TNat)) TUnit))
let ctx_swap_ref_test (x:ref (ref int)) =
  mst_witness (contains_pred x);
  mst_witness (is_low_pred x);
  let cb : elab_typ' (TArr (TRef (TRef TNat)) TUnit) = (fun (y: ref (ref int)) ->
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
    let r = () in
    assert (shallowly_contained_low r h2);
    r) in
  cb

val ctx_dynamic_alloc_test :
   elab_typ' (TArr TUnit (TRef TNat))
let ctx_dynamic_alloc_test () = 
  let v = elab_alloc #TNat 0 in 
  v

val ctx_HO_test3 :
  elab_typ' (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test3 f =
  let x:ref int = f () in
  let y:ref int = elab_alloc #TNat (!x + 1) in
  ()

val ctx_returns_callback_test :
  elab_typ' (TArr TUnit (TArr TUnit TUnit))
let ctx_returns_callback_test () =
  let x: ref int = elab_alloc #TNat 13 in
  mst_witness (contains_pred x);
  mst_witness (is_low_pred x);
  let cb : elab_typ' (TArr TUnit TUnit) = (fun() ->
    mst_recall (contains_pred x);
    mst_recall (is_low_pred x);
    elab_write #TNat x (!x % 5)
  ) in
  cb

val ctx_HO_test4 :
  elab_typ' (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test4 f =
  let x:ref int = f () in
  let y:ref (ref int) = elab_alloc #(TRef TNat) x in
  ()

val progr_sep_test: 
  #rp: ref int -> 
  ctx:(elab_typ' (TArr TUnit TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
         
let progr_sep_test #rp f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  f ()

val progr_declassify :
  rp: ref int -> 
  ctx:(elab_typ' (TArr (TRef TNat) TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 -> True))
let progr_declassify rp f =
  let h0 = get () in
  declassify_low' #TNat rp;
  let h1 = get () in
  lemma_declassify_preserves_inv TNat rp h0 h1;
  let r = f rp in  
  r

val progr_declassify_nested:
  rp: ref (ref int) -> 
  ctx:(elab_typ' (TArr (TRef (TRef TNat)) TUnit)) ->
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
  lemma_declassify_preserves_inv TNat p h0 h1;
  declassify_low' #(TRef TNat) rp;
  let h2 = get () in
  lemma_declassify_preserves_inv (TRef TNat) rp h1 h2;
  // let r = elab_alloc (!rp) in (* <-- needed a copy here! *) 
  f rp

val progr_secret_unchanged_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ' (TArr TUnit TUnit)) ->
  IST unit 
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High /\
      satisfy rs h0 is_low_pred))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp))
         
let progr_secret_unchanged_test rp rs ctx = 
  let secret: ref int = ist_alloc #TNat 0 in
  ctx ();
  let v = !secret in
  assert (v == 0);
  ()

val progr_passing_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ' (TArr (TArr TUnit TUnit) TUnit)) ->
  IST unit 
    (requires (fun h0 ->
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High /\
      satisfy rs h0 is_low_pred))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context

// TODO: the callback of the program should be able to modify rp
let progr_passing_callback_test rp rs f =
  let secret: ref int = ist_alloc #TNat 0 in
  let h0 = get () in
  declassify_low' #TNat secret;
  let h1 = get () in
  lemma_declassify_preserves_inv TNat secret h0 h1;
  mst_witness (contains_pred secret);
  mst_witness (is_low_pred secret);
  let cb: elab_typ' (TArr TUnit TUnit) = (fun () -> 
    mst_recall (contains_pred secret);
    mst_recall (is_low_pred secret);
    elab_write #TNat secret (!secret + 1)) in
  f cb;
  ()

val progr_getting_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ' (TArr TUnit (TArr TUnit TUnit))) ->
  IST unit 
    (requires (fun h0 ->
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High /\
      satisfy rs h0 is_low_pred))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp))
let progr_getting_callback_test rp rs f =
  let h0 = get () in
  let cb = f () in
  let h1 = get () in
  cb ();
  let h2 = get () in
  lemma_modifies_only_label_trans Low h0 h1 h2;
  assert (modifies_only_label Low h0 h2);
  ()

(** ** Elaboration of expressions to F* *)
val elab_apply_arrow :
  t1:typ ->
  t2:typ ->
  f:elab_typ' (TArr t1 t2) ->
  (let tt1 = _elab_typ t1 inv_low_contains in
   let tt2 = _elab_typ t2 inv_low_contains in
   mk_tgt_arrow inv_low_contains (dfst tt1) #(dsnd tt1) (dfst tt2) #(dsnd tt2))
let elab_apply_arrow t1 t2 f x = f x

let cast_TArr #t1 #t2 (f : elab_typ' (TArr t1 t2)) (t:typ) (#_:squash (t == TArr t1 t2)) : elab_typ' t = f

type vcontext (g:context) = 
  vx:var{Some? (g vx)} -> 
    ST (elab_typ' (Some?.v (g vx)))
      (fun h -> True)
      (fun h0 x h1 -> h0 == h1 /\ shallowly_contained_low #_ #(elab_typ_tc' (Some?.v (g vx))) x h1)

let vempty : vcontext empty = fun _ -> assert false

let vextend #t (x:elab_typ' t) (#g:context) (ve:vcontext g) : 
  ST (vcontext (extend t g))
    (requires (fun h0 -> shallowly_contained_low #_ #(elab_typ_tc' t) x h0))
    (ensures (fun h0 r h1 -> h0 == h1)) =
  let w1 = (elab_typ_tc' t).witness x contains_pred in
  let w2 = (elab_typ_tc' t).witness x is_low_pred in
  fun y -> 
    if y = 0 then (w1 (); w2 (); x) else ve (y-1)

#push-options "--split_queries always"
let rec elab_exp 
  (#g:context)
  (#e:exp) 
  (#t:typ)
  (tyj:typing g e t)
  (ve:vcontext g)
  : IST (elab_typ' t) 
     (requires (pre_tgt_arrow #unit #witnessable_unit #inv_low_contains ()))
     (ensures (post_tgt_arrow #_ #_ #(elab_typ' t) #(elab_typ_tc' t) #inv_low_contains ())) =
  let h0 = get () in
  match tyj with
  | TyUnit -> ()
  | TyZero -> 0
  | TySucc tyj_s -> 
    1 + (elab_exp tyj_s ve)

  | TyAllocRef #_ #_ #t tyj_e -> begin
    let v : elab_typ' t = elab_exp tyj_e ve in
    let r : ref (elab_typ' t) = elab_alloc #t v in
    r
  end
  | TyReadRef #_ #_ #t tyj_e -> begin
    let r : ref (elab_typ' t) = elab_exp tyj_e ve in
    !r
  end
  | TyWriteRef #_ #_ #_ #t tyj_ref tyj_v -> begin
      let r : ref (elab_typ' t) = elab_exp tyj_ref ve in
      let v : elab_typ' t = elab_exp tyj_v ve in
      elab_write #t r v
  end

  | TyAbs tx #_ #tres tyj_body ->
    let w : mk_tgt_arrow inv_low_contains (elab_typ' tx) #(elab_typ_tc' tx) (elab_typ' tres) #(elab_typ_tc' tres) = 
      (fun (x:elab_typ' tx) -> 
        elab_exp tyj_body (vextend #tx x ve))
    in
    assert (t == TArr tx tres);
    cast_TArr #tx #tres w t
  | TyVar vx -> 
    let Some tx = g vx in
    let x : elab_typ' tx = ve vx in
    x
  | TyApp #_ #_ #_ #tx #tres tyj_f tyj_x ->
    assert ((elab_typ t) == (elab_typ tres));
    let x : elab_typ' tx = elab_exp tyj_x ve in
    let wx1 = (elab_typ_tc' tx).witness x contains_pred in
    let wx2 = (elab_typ_tc' tx).witness x is_low_pred in
    let f : elab_typ' (TArr tx tres) = elab_exp tyj_f ve in
    wx1 (); wx2 ();
    elab_apply_arrow tx tres f x

  | TyInl #_ #_ #t1 #t2 tyj_1 ->
    let v1 : elab_typ' t1 = elab_exp tyj_1 ve in
    Inl #_ #(elab_typ' t2) v1
  | TyInr #_ #_ #t1 #t2 tyj_2 ->
    let v2 : elab_typ' t2 = elab_exp tyj_2 ve in
    Inr #(elab_typ' t1) v2
  | TyCaseSum #_ #_ #_ #_ #tl #tr #tres tyj_c tyj_l tyj_r -> begin
    let vc : either (elab_typ' tl) (elab_typ' tr) = elab_exp tyj_c ve in
    match vc with 
    | Inl x -> 
      let wx1 = (elab_typ_tc' tl).witness x contains_pred in
      let wx2 = (elab_typ_tc' tl).witness x is_low_pred in
      let f : elab_typ' (TArr tl tres) = elab_exp tyj_l ve in
      wx1 (); wx2 ();
      elab_apply_arrow tl tres f x
    | Inr y ->
      let wy1 = (elab_typ_tc' tr).witness y contains_pred in
      let wy2 = (elab_typ_tc' tr).witness y is_low_pred in
      let f : elab_typ' (TArr tr tres) = elab_exp tyj_r ve in
      wy1 (); wy2 ();
      elab_apply_arrow tr tres f y
  end

  | TyFst #_ #_ #tf #ts tyj_e ->
    let v = elab_exp tyj_e ve in
    fst #(elab_typ' tf) #(elab_typ' ts) v
  | TySnd #_ #_ #tf #ts tyj_e ->
    let v = elab_exp tyj_e ve in
    snd #(elab_typ' tf) #(elab_typ' ts) v
  | TyPair #_ #_ #_ #tf #ts tyj_f tyj_s->
    let vf : elab_typ' tf = elab_exp tyj_f ve in
    let wvf1 = (elab_typ_tc' tf).witness vf contains_pred in
    let wvf2 = (elab_typ_tc' tf).witness vf is_low_pred in
    let vs : elab_typ' ts = elab_exp tyj_s ve in
    wvf1 (); wvf2 ();
    (vf, vs)
#pop-options
