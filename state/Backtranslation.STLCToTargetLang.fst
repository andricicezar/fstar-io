module Backtranslation.STLCToTargetLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open SharedRefs
open Witnessable
open TargetLang
open STLC

let rec to_shareable_typ (t:typ0) : shareable_typ =
  match t with
  | TUnit -> SUnit
  | TNat -> SNat
  | TSum t1 t2 -> SSum (to_shareable_typ t1) (to_shareable_typ t2)
  | TPair t1 t2 -> SPair (to_shareable_typ t1) (to_shareable_typ t2)
  | TRef t -> SRef (to_shareable_typ t)
  | TLList t -> SLList (to_shareable_typ t)

unfold
let elab_typ0 (t:typ0) : Type u#0 = 
  to_Type (to_shareable_typ t)

let rec elab_typ0_tc #pspec (t:typ0) : targetlang pspec (elab_typ0 t) = 
  match t with
  | TUnit -> targetlang_unit pspec 
  | TNat -> targetlang_int pspec
  | TSum t1 t2 -> targetlang_sum pspec _ _ #(elab_typ0_tc t1) #(elab_typ0_tc t2)
  | TPair t1 t2 -> targetlang_pair pspec _ _ #(elab_typ0_tc t1) #(elab_typ0_tc t2)
  | TRef t -> targetlang_ref pspec _ #(elab_typ0_tc t) 
  | TLList t -> targetlang_llist pspec _ #(elab_typ0_tc t)


  (**
let rec lemma_123 pspec (#t:typ0) (v:elab_typ0 t) h pred :
  Lemma ((elab_typ0_tc #pspec t).wt.satisfy_on_heap v h pred <==> forall_refs_heap pred h #(to_shareable_typ t) v) 
  // [SMTPat ((elab_typ0_tc t).satisfy v h pred); SMTPat (forallRefsHeap pred h #(to_shareable_typ t) v)]
  by (compute ()) =
  match t with
  | TUnit -> ()
  | TNat -> ()
  | TSum t1 t2 -> begin
    let v : either (elab_typ0 t1) (elab_typ0 t2) = v in
    match v with
    | Inl lv -> lemma_123 pspec lv h pred
    | Inr rv -> lemma_123 pspec rv h pred
  end
  | TPair t1 t2 -> begin
     let v : (elab_typ0 t1) * (elab_typ0 t2) = v in
     lemma_123 pspec (fst v) h pred;
     lemma_123 pspec (snd v) h pred;
     assert ((elab_typ0_tc #pspec t).satisfy_on_heap v h pred <==> forall_refs_heap pred h #(to_shareable_typ t) v)
  end
  | TRef t' -> 
    let aux (#t':typ0) (v:elab_typ0 (TRef t')) : ref (elab_typ0 t') = v in
    let v : ref (elab_typ0 t') = aux v in
    assert ((elab_typ0_tc t).satisfy v h pred <==> forall_refs_heap pred h #(to_shareable_typ t) v) by (compute ())
  | TLList t' -> begin
    let aux (#t':typ0) (v:elab_typ0 (TLList t')) : linkedList (elab_typ0 t') = v in
    let v : linkedList (elab_typ0 t') = aux v in
    match v with
    | LLNil -> ()
    | LLCons v' xsref -> (
      lemma_123 v' h pred;
      let xsref : ref (linkedList (elab_typ0 t')) = xsref in
      assert ((elab_typ0_tc t).satisfy v h pred <==> forall_refs_heap pred h #(to_shareable_typ t) v))
  end**)

open FStar.Universe

let rec _elab_typ (#pspec:targetlang_pspec) (t:typ) : tt:Type u#1 & targetlang pspec tt =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = _elab_typ t1 in
    let tt2 = _elab_typ t2 in
    (| mk_targetlang_arrow pspec (dfst tt1) #(dsnd tt1).wt (dfst tt2) #(dsnd tt2).wt,
       targetlang_arrow pspec (dfst tt1) (dfst tt2)
    |)
  end 
  | TUnit -> (| raise_t unit, solve |)
  | TNat -> (| raise_t int, solve |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 in
    let (| tt2, c_tt2 |) = _elab_typ t2 in
    (| either tt1 tt2, targetlang_sum pspec tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 in
    let (| tt2, c_tt2 |) = _elab_typ t2 in
    (| tt1 * tt2, targetlang_pair pspec tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef _ ->
    let tt = elab_typ0 t in
    let c_tt = elab_typ0_tc t in
    (| raise_t tt, targetlang_univ_raise pspec _ #c_tt |)
  | TLList t ->
    let tt = elab_typ0 t in
    let c_tt = elab_typ0_tc t in
    (| raise_t (linkedList tt), targetlang_univ_raise pspec _ #(targetlang_llist pspec tt #c_tt) |)

let elab_typ (pspec:targetlang_pspec) (t:typ) : Type =
  dfst (_elab_typ #pspec t)

let elab_typ_tc #pspec (t:typ) : targetlang pspec (elab_typ pspec t) =
  dsnd (_elab_typ #pspec t)

unfold
let mk_targetlang_pspec  
  (inv  : heap -> Type0) 
  (prref: ref_pred)
  (hrel : FStar.Preorder.preorder heap) 
  : targetlang_pspec =
  (inv, (fun #a #rel r -> prref #a #rel r), hrel)
  

let elab_poly_typ (t:typ) =
  #inv  : (heap -> Type0) -> 
  #prref: ref_pred ->
  #hrel : FStar.Preorder.preorder heap ->
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  read :  ((#t:typ0) -> r:ref (elab_typ0 t) -> 
            ST (elab_typ0 t) 
              (requires (fun h0 -> inv h0 /\ prref r))
              (ensures  (fun h0 v h1 -> h0 `hrel` h1 /\ inv h1 /\ (elab_typ0_tc #(mk_targetlang_pspec inv prref hrel) t).wt.satisfy v prref))) -> 
  write : ((#t:typ0) -> r:ref (elab_typ0 t) -> v:(elab_typ0 t) -> 
            ST unit
              (requires (fun h0 -> inv h0 /\ prref r /\ (elab_typ0_tc #(mk_targetlang_pspec inv prref hrel) t).wt.satisfy v prref))
              (ensures  (fun h0 _ h1 -> h0 `hrel` h1 /\ inv h1))) ->
  alloc : ((#t:typ0) -> init:(elab_typ0 t) -> 
            ST (ref (elab_typ0 t)) 
              (requires (fun h0 -> inv h0 /\ (elab_typ0_tc #(mk_targetlang_pspec inv prref hrel) t).wt.satisfy init prref))
              (ensures  (fun h0 r h1 -> h0 `hrel` h1 /\ inv h1 /\ prref r))) ->
  (** type of the context: *)
  elab_typ (mk_targetlang_pspec inv prref hrel) t
  
(** ** Examples **) 

val ctx_update_ref_test : 
  elab_poly_typ (TArr (TRef TNat) TUnit)
let ctx_update_ref_test my_read my_write _ y =
  let y : ref int = downgrade_val y in
  my_write #TNat y (my_read #TNat y + 1);
  raise_val ()

val ctx_update_multiple_refs_test : 
  elab_poly_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit))
let ctx_update_multiple_refs_test #inv #prref #hrel my_read my_write _ x =
  let x : ref (ref int) = downgrade_val x in
  let cb : elab_typ (mk_targetlang_pspec inv prref hrel) (TArr (TRef TNat) TUnit) = (fun y ->
    let y : ref int = downgrade_val y in
    let ix : ref int = my_read #(TRef TNat) x in
    my_write #TNat ix (my_read #TNat ix + 1);
    my_write #(TRef TNat) x y;
    my_write #TNat y (my_read #TNat y + 5);
    raise_val () 
  ) in
  cb

val ctx_HO_test1 : 
  elab_poly_typ (TArr (TRef (TPair (TRef TNat) (TRef TNat))) (TArr TUnit TUnit))
let ctx_HO_test1 my_read my_write _ xs =
  let h0 = get () in
  let xs : ref ((ref int) * ref int) = downgrade_val xs in
  let (x', x'') : (ref int) * ref int = my_read #(TPair (TRef TNat) (TRef TNat)) xs in
  my_write #(TPair (TRef TNat) (TRef TNat)) xs (x', x');
  (fun _ -> 
    my_write #(TPair (TRef TNat) (TRef TNat)) xs (x', x'');
    raise_val ())
  
val ctx_identity :
  elab_poly_typ (TArr (TRef TNat) (TRef TNat))
let ctx_identity _ _ _ x = x

val ctx_HO_test2 :
  elab_poly_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test2 my_read my_write _ f =
  let x:ref int = downgrade_val (f (raise_val ())) in
  my_write #TNat x (my_read #TNat x + 1);
  raise_val ()

val ctx_swap_ref_test :
  elab_poly_typ (TArr (TRef (TRef TNat)) (TArr (TRef (TRef TNat)) TUnit))
let ctx_swap_ref_test #inv #prref #hrel my_read my_write _ x =
  let x : ref (ref int) = downgrade_val x in
  let cb : elab_typ (mk_targetlang_pspec inv prref hrel) (TArr (TRef (TRef TNat)) TUnit) = (fun y ->
    let y : ref (ref int) = downgrade_val y in

    let z = my_read #(TRef TNat) x in
    let t = my_read #(TRef TNat) y in
    my_write #(TRef TNat) x t;
    my_write #(TRef TNat) y z;

    raise_val ()) in
  cb

val ctx_dynamic_alloc_test :
   elab_poly_typ (TArr TUnit (TRef TNat))
let ctx_dynamic_alloc_test _ _ my_alloc _ = 
  let v : ref int = my_alloc #TNat 0 in 
  raise_val v

val ctx_HO_test3 :
  elab_poly_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test3 my_read _ my_alloc f =
  let x:ref int = downgrade_val (f (raise_val ())) in
  let y:ref int = my_alloc #TNat (my_read #TNat x + 1) in
  raise_val ()

val ctx_returns_callback_test :
  elab_poly_typ (TArr TUnit (TArr TUnit TUnit))
let ctx_returns_callback_test #inv #prref #hrel my_read my_write my_alloc _ =
  let x: ref int = my_alloc #TNat 13 in
  let cb : elab_typ (mk_targetlang_pspec inv prref hrel) (TArr TUnit TUnit) = (fun _ ->
    my_write #TNat x (my_read #TNat x % 5);
    raise_val ()
  ) in
  cb

val ctx_HO_test4 :
  elab_poly_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test4 _ _ my_alloc f =
  let x:ref int = downgrade_val (f (raise_val ())) in
  let y:ref (ref int) = my_alloc #(TRef TNat) x in
  raise_val ()

let default_spec : targetlang_pspec = (
    (fun h -> 
        trans_shared_contains h /\
        h `contains` map_shared /\ 
        ~(is_shared (map_shared) h) /\
        (forall p. p >= next_addr h ==> ~(sel h map_shared p))),
    (fun #a #rel (r:mref a rel) -> witnessed (contains_pred r) /\ witnessed (is_shared r)),
    (fun h0 h1 -> modifies_only_shared h0 h1 /\ gets_shared Set.empty h0 h1)
)


val progr_sep_test: 
  #rp: ref int -> 
  ctx:(elab_typ default_spec (TArr TUnit TUnit)) ->
  SST unit
    (requires (fun h0 -> 
      satisfy_on_heap rp h0 contains_pred /\
      ~(is_shared rp h0)))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
let progr_sep_test #rp f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  downgrade_val (f (raise_val ()))

val progr_declassify :
  rp: ref int -> 
  ctx:(elab_typ default_spec (TArr (TRef TNat) TUnit)) ->
  SST unit
    (requires (fun h0 -> 
      satisfy_on_heap rp h0 contains_pred /\
      ~(is_shared rp h0)))
    (ensures (fun h0 _ h1 -> True))
let progr_declassify rp f =
  let h0 = get () in
  sst_share #SNat rp;
  let h1 = get () in
  witness (contains_pred rp); witness (is_shared rp);
  let r = downgrade_val (f (raise_val rp)) in  
  r

val progr_declassify_nested:
  rp: ref (ref int) -> 
  ctx:(elab_typ default_spec (TArr (TRef (TRef TNat)) TUnit)) ->
  SST unit
    (requires (fun h0 -> 
      satisfy_on_heap rp h0 contains_pred /\
      ~(is_shared rp h0)))
    (ensures (fun h0 _ h1 -> True))
let progr_declassify_nested rp f =
  let p : ref int = sst_read #(SRef SNat) rp in
  sst_share #SNat p;
  sst_share #(SRef SNat) rp;
  witness (contains_pred rp); witness (is_shared rp);
  // let r = elab_alloc (!rp) in (* <-- needed a copy here! *) 
  downgrade_val (f (raise_val rp))

val progr_secret_unchanged_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ default_spec (TArr TUnit TUnit)) ->
  SST unit 
    (requires (fun h0 -> 
      satisfy_on_heap rp h0 contains_pred /\
      ~(is_shared rp h0) /\
      satisfy_on_heap rs h0 is_shared))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp))
let progr_secret_unchanged_test rp rs ctx = 
  let h0 = get () in
  let secret: ref int = sst_alloc #SNat 0 in
  let h1 = get () in
  downgrade_val (ctx (raise_val ()));
  let v = sst_read #SNat secret in
  ()

val progr_passing_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ default_spec (TArr (TArr TUnit TUnit) TUnit)) ->
  SST unit 
    (requires (fun h0 ->
      satisfy_on_heap rp h0 contains_pred /\
      ~(is_shared rp h0) /\
      satisfy_on_heap rs h0 is_shared))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
// TODO: the callback of the program should be able to modify rp
let progr_passing_callback_test rp rs f =
  let secret: ref int = sst_alloc #SNat 0 in
  sst_share #SNat secret;
  witness (contains_pred secret); witness (is_shared secret);
  let cb: elab_typ default_spec (TArr TUnit TUnit) = (fun _ -> 
    recall (contains_pred secret); recall (is_shared secret);
    sst_write #SNat secret (!secret + 1);
    raise_val ()) in
  downgrade_val (f cb);
  ()

val progr_getting_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ default_spec (TArr TUnit (TArr TUnit TUnit))) ->
  SST unit 
    (requires (fun h0 ->
      satisfy_on_heap rp h0 contains_pred /\
      ~(is_shared rp h0) /\
      satisfy_on_heap rs h0 is_shared))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp))
let progr_getting_callback_test rp rs f =
  let cb = f (raise_val ()) in
  downgrade_val (cb (raise_val ()));
  ()
