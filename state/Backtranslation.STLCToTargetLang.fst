module Backtranslation.STLCToTargetLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open SharedRefs
open Witnessable
open TargetLang
open STLC
open FStar.Universe

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
  (prref: mref_pred)
  (hrel : FStar.Preorder.preorder heap)
  : targetlang_pspec =
  (inv, (prref <: (#a:Type0 -> #rel:FStar.Preorder.preorder a -> mref a rel -> Type0)), hrel)

type tbt_read (inv:heap -> Type0) (prref:mref_pred) (hrel:FStar.Preorder.preorder heap) =
  (#t:typ0) -> r:ref (elab_typ0 t) ->
    ST (elab_typ0 t)
      (requires (fun h0 -> inv h0 /\ prref r))
      (ensures  (fun h0 v h1 -> h0 `hrel` h1 /\ inv h1 /\ (elab_typ0_tc #(mk_targetlang_pspec inv prref hrel) t).wt.satisfy v prref))

type tbt_write (inv:heap -> Type0) (prref:mref_pred) (hrel:FStar.Preorder.preorder heap) =
  (#t:typ0) -> r:ref (elab_typ0 t) -> v:(elab_typ0 t) ->
    ST unit
      (requires (fun h0 -> inv h0 /\ prref r /\ (elab_typ0_tc #(mk_targetlang_pspec inv prref hrel) t).wt.satisfy v prref))
      (ensures  (fun h0 _ h1 -> h0 `hrel` h1 /\ inv h1))

type tbt_alloc (inv:heap -> Type0) (prref:mref_pred) (hrel:FStar.Preorder.preorder heap) =
  (#t:typ0) -> init:(elab_typ0 t) ->
    ST (ref (elab_typ0 t))
      (requires (fun h0 -> inv h0 /\ (elab_typ0_tc #(mk_targetlang_pspec inv prref hrel) t).wt.satisfy init prref))
      (ensures  (fun h0 r h1 -> h0 `hrel` h1 /\ inv h1 /\ prref r))

let elab_poly_typ (t:typ) =
  #inv  : (heap -> Type0) ->
  #prref: mref_pred ->
  #hrel : FStar.Preorder.preorder heap ->
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  read :  tbt_read inv prref hrel ->
  write : tbt_write inv prref hrel ->
  alloc : tbt_alloc inv prref hrel ->
  (** type of the context: *)
  elab_typ (mk_targetlang_pspec inv prref hrel) t

(** ** Examples **)

val ctx_update_ref_test :
  elab_poly_typ (TArr (TRef TNat) TUnit)
let ctx_update_ref_test bt_read bt_write _ y =
  let y : ref int = downgrade_val y in
  bt_write #TNat y (bt_read #TNat y + 1);
  raise_val ()

val ctx_update_multiple_refs_test :
  elab_poly_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit))
let ctx_update_multiple_refs_test #inv #prref #hrel bt_read bt_write _ x =
  let x : ref (ref int) = downgrade_val x in
  let cb : elab_typ (mk_targetlang_pspec inv prref hrel) (TArr (TRef TNat) TUnit) = (fun y ->
    let y : ref int = downgrade_val y in
    let ix : ref int = bt_read #(TRef TNat) x in
    bt_write #TNat ix (bt_read #TNat ix + 1);
    bt_write #(TRef TNat) x y;
    bt_write #TNat y (bt_read #TNat y + 5);
    raise_val ()
  ) in
  cb

val ctx_HO_test1 :
  elab_poly_typ (TArr (TRef (TPair (TRef TNat) (TRef TNat))) (TArr TUnit TUnit))
let ctx_HO_test1 bt_read bt_write _ xs =
  let xs : ref ((ref int) * ref int) = downgrade_val xs in
  let (x', x'') : (ref int) * ref int = bt_read #(TPair (TRef TNat) (TRef TNat)) xs in
  bt_write #(TPair (TRef TNat) (TRef TNat)) xs (x', x');
  (fun _ ->
    bt_write #(TPair (TRef TNat) (TRef TNat)) xs (x', x'');
    raise_val ())

val ctx_identity :
  elab_poly_typ (TArr (TRef TNat) (TRef TNat))
let ctx_identity _ _ _ x = x

val ctx_HO_test2 :
  elab_poly_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test2 bt_read bt_write _ f =
  let x:ref int = downgrade_val (f (raise_val ())) in
  bt_write #TNat x (bt_read #TNat x + 1);
  raise_val ()

val ctx_swap_ref_test :
  elab_poly_typ (TArr (TRef (TRef TNat)) (TArr (TRef (TRef TNat)) TUnit))
let ctx_swap_ref_test #inv #prref #hrel bt_read bt_write _ x =
  let x : ref (ref int) = downgrade_val x in
  let cb : elab_typ (mk_targetlang_pspec inv prref hrel) (TArr (TRef (TRef TNat)) TUnit) = (fun y ->
    let y : ref (ref int) = downgrade_val y in

    let z = bt_read #(TRef TNat) x in
    let t = bt_read #(TRef TNat) y in
    bt_write #(TRef TNat) x t;
    bt_write #(TRef TNat) y z;

    raise_val ()) in
  cb

val ctx_dynamic_alloc_test :
   elab_poly_typ (TArr TUnit (TRef TNat))
let ctx_dynamic_alloc_test _ _ bt_alloc _ =
  let v : ref int = bt_alloc #TNat 0 in
  raise_val v

val ctx_HO_test3 :
  elab_poly_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test3 bt_read _ bt_alloc f =
  let x:ref int = downgrade_val (f (raise_val ())) in
  let y:ref int = bt_alloc #TNat (bt_read #TNat x + 1) in
  raise_val ()

val ctx_returns_callback_test :
  elab_poly_typ (TArr TUnit (TArr TUnit TUnit))
let ctx_returns_callback_test #inv #prref #hrel bt_read bt_write bt_alloc _ =
  let x: ref int = bt_alloc #TNat 13 in
  let cb : elab_typ (mk_targetlang_pspec inv prref hrel) (TArr TUnit TUnit) = (fun _ ->
    bt_write #TNat x (bt_read #TNat x % 5);
    raise_val ()
  ) in
  cb

val ctx_HO_test4 :
  elab_poly_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test4 _ _ bt_alloc f =
  let x:ref int = downgrade_val (f (raise_val ())) in
  let y:ref (ref int) = bt_alloc #(TRef TNat) x in
  raise_val ()

val progr_sep_test:
  #rp: ref int ->
  ctx:(elab_typ default_spec (TArr TUnit TUnit)) ->
  SST unit
    (requires (fun h0 ->
      satisfy_on_heap rp h0 contains_pred /\
      is_private rp h0))
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
      is_private rp h0))
    (ensures (fun h0 _ h1 -> True))
let progr_declassify rp f =
  sst_share #SNat rp;
  witness (contains_pred rp); witness (is_shared rp);
  let r = downgrade_val (f (raise_val rp)) in
  r

val progr_declassify_nested:
  rp: ref (ref int) ->
  ctx:(elab_typ default_spec (TArr (TRef (TRef TNat)) TUnit)) ->
  SST unit
    (requires (fun h0 ->
      satisfy_on_heap rp h0 contains_pred /\
      is_private rp h0 /\
      is_private (sel h0 rp) h0))
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
      is_private rp h0 /\
      satisfy_on_heap rs h0 is_shared))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp))
let progr_secret_unchanged_test rp rs ctx =
  let secret: ref int = sst_alloc #SNat 0 in
  downgrade_val (ctx (raise_val ()));
  let v = sst_read #SNat secret in
  ()

val progr_passing_shared_to_callback_test:
  rp: ref int ->
  rs: ref (ref int) ->
  ctx:(elab_typ default_spec (TArr (TArr TUnit TUnit) TUnit)) ->
  SST unit
    (requires (fun h0 ->
      satisfy_on_heap rp h0 contains_pred /\
      is_private rp h0 /\
      satisfy_on_heap rs h0 is_shared))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
// TODO: the callback of the program should be able to modify rp (DA: now the callbacks can modify encapsulated, not private references)
let progr_passing_shared_to_callback_test rp rs f =
  let secret: ref int = sst_alloc #SNat 0 in
  sst_share #SNat secret;
  witness (contains_pred secret); witness (is_shared secret);
  let cb: elab_typ default_spec (TArr TUnit TUnit) = (fun _ ->
    recall (contains_pred secret); recall (is_shared secret);
    sst_write #SNat secret (!secret + 1);
    raise_val ()) in
  downgrade_val (f cb);
  ()

val progr_passing_encapsulated_to_callback_test:
  rp: ref int ->
  rs: ref (ref int) ->
  ctx:(elab_typ default_spec (TArr (TArr TUnit TUnit) TUnit)) ->
  SST unit
    (requires (fun h0 ->
      satisfy_on_heap rp h0 contains_pred /\
      is_private rp h0 /\
      satisfy_on_heap rs h0 is_shared))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
let progr_passing_encapsulated_to_callback_test rp rs f =
  let secret: ref int = sst_alloc #SNat 0 in
  sst_encapsulate secret;
  witness (contains_pred secret); witness (is_encapsulated secret);
  let cb: elab_typ default_spec (TArr TUnit TUnit) = (fun _ ->
    recall (contains_pred secret); recall (is_encapsulated secret);
    sst_write #SNat secret (!secret + 1);
    raise_val ()) in
  downgrade_val (f cb);
  ()

val progr_passing_private_to_callback_test:
  ctx:(elab_typ default_spec (TArr (TArr TUnit TUnit) TUnit)) ->
  SST unit
    (requires (fun h0 -> True))
    (ensures (fun h0 _ h1 -> True))
[@expect_failure]
let progr_passing_private_to_callback_test f =
  let secret: ref int = sst_alloc #SNat 0 in
  witness (contains_pred secret);
  let cb: elab_typ default_spec (TArr TUnit TUnit) = (fun _ ->
    recall (contains_pred secret);
    // let h0 = get_heap () in
    // assume (is_shared secret h0);
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
      is_private rp h0 /\
      satisfy_on_heap rs h0 is_shared))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp))
let progr_getting_callback_test rp rs f =
  let cb = f (raise_val ()) in
  downgrade_val (cb (raise_val ()));
  ()

(** ** Backtranslation **)

val elab_apply_arrow :
  #pspec : targetlang_pspec ->
  t1:typ ->
  t2:typ ->
  f:elab_typ pspec (TArr t1 t2) ->
  (let tt1 = _elab_typ #pspec t1 in
   let tt2 = _elab_typ #pspec t2 in
   mk_targetlang_arrow pspec (dfst tt1) #(dsnd tt1).wt (dfst tt2) #(dsnd tt2).wt)
let elab_apply_arrow t1 t2 f x = f x

let cast_TArr inv prref hrel (#t1 #t2:typ) (f : elab_typ (mk_targetlang_pspec inv prref hrel) (TArr t1 t2)) (t:typ) (#_:squash (t == TArr t1 t2)) : elab_typ (mk_targetlang_pspec inv prref hrel) t = f

type vcontext pspec (g:context) =
  vx:var{Some? (g vx)} -> elab_typ pspec (Some?.v (g vx))

let vempty pspec : vcontext pspec empty = fun _ -> assert false

let vextend #pspec #t (x:elab_typ pspec t) (#g:context) (ve:vcontext pspec g) : vcontext pspec (extend t g) =
  fun y -> if y = 0 then x else ve (y-1)

let all_refs_contained_and_low (#pspec) (#g:context) (ve:vcontext pspec g) : Type0 =
  forall vx. Some? (g vx) ==>
    (elab_typ_tc #pspec (Some?.v (g vx))).wt.satisfy (ve vx) (Mktuple3?._2 pspec)

let rec downgrade_typ #pspec (t:typ0) (x:elab_typ pspec t) : elab_typ0 t =
  match t with
  | TSum t1 t2 -> begin
    let x : either (elab_typ pspec t1) (elab_typ pspec t2) = x in
    (match x with
    | Inl v -> Inl (downgrade_typ t1 v)
    | Inr v -> Inr (downgrade_typ t2 v)) <: either (elab_typ0 t1) (elab_typ0 t2)
    end
  | TPair t1 t2 -> begin
    let x : elab_typ pspec t1 * elab_typ pspec t2 = x in
    let (v1, v2) = x in
    (downgrade_typ t1 v1, downgrade_typ t2 v2)
  end
  | _ -> downgrade_val x

let rec raise_typ #pspec (t:typ0) (x:elab_typ0 t) : elab_typ pspec t =
  match t with
  | TSum t1 t2 -> begin
    let x : either (elab_typ0 t1) (elab_typ0 t2) = x in
    (match x with
    | Inl v -> Inl (raise_typ t1 v)
    | Inr v -> Inr (raise_typ t2 v)) <: either (elab_typ pspec t1) (elab_typ pspec t2)
    end
  | TPair t1 t2 -> begin
    let x : elab_typ0 t1 * elab_typ0 t2 = x in
    let (v1, v2) = x in
    (raise_typ #pspec t1 v1, raise_typ #pspec t2 v2)
  end
  | _ -> raise_val x

let rec lemma_downgrade_typ #pspec (t:typ0) (x:elab_typ pspec t) :
  Pure unit
    (requires ((elab_typ_tc #pspec t).wt.satisfy x (Mktuple3?._2 pspec)))
    (ensures (fun r -> (elab_typ0_tc #pspec t).wt.satisfy (downgrade_typ t x) (Mktuple3?._2 pspec))) =
  match t with
  | TSum t1 t2 -> begin
    let x : either (elab_typ pspec t1) (elab_typ pspec t2) = x in
    (match x with
    | Inl v -> lemma_downgrade_typ t1 v
    | Inr v -> lemma_downgrade_typ t2 v)
  end
  | TPair t1 t2 -> begin
    let x : elab_typ pspec t1 * elab_typ pspec t2 = x in
    let (v1, v2) = x in
    lemma_downgrade_typ t1 v1;
    lemma_downgrade_typ t2 v2
  end
  | _ -> ()

let rec lemma_raise_typ pspec (t:typ0) (x:elab_typ0 t) :
  Pure unit
    (requires ((elab_typ0_tc #pspec t).wt.satisfy x (Mktuple3?._2 pspec)))
    (ensures (fun r -> (elab_typ_tc #pspec t).wt.satisfy (raise_typ #pspec t x) (Mktuple3?._2 pspec))) =
  match t with
  | TSum t1 t2 -> begin
    let x : either (elab_typ0 t1) (elab_typ0 t2) = x in
    (match x with
    | Inl v -> lemma_raise_typ pspec t1 v
    | Inr v -> lemma_raise_typ pspec t2 v)
  end
  | TPair t1 t2 -> begin
    let x : elab_typ0 t1 * elab_typ0 t2 = x in
    let (v1, v2) = x in
    lemma_raise_typ pspec t1 v1;
    lemma_raise_typ pspec t2 v2
  end
  | _ -> ()

let downgrade #pspec (#t:typ0) (x:elab_typ pspec t) :
  Pure (elab_typ0 t)
    (requires ((elab_typ_tc t).wt.satisfy x (Mktuple3?._2 pspec)))
    (ensures (fun r -> r == downgrade_typ t x /\ (elab_typ0_tc #pspec t).wt.satisfy r (Mktuple3?._2 pspec))) =
    lemma_downgrade_typ t x;
    downgrade_typ t x

let raise #pspec (#t:typ0) (x:elab_typ0 t) :
  Pure (elab_typ pspec t)
    (requires ((elab_typ0_tc #pspec t).wt.satisfy x (Mktuple3?._2 pspec)))
    (ensures (fun r -> r == raise_typ t x /\ (elab_typ_tc t).wt.satisfy r (Mktuple3?._2 pspec))) =
    lemma_raise_typ pspec t x;
    raise_typ t x

let rec backtranslate
  (#inv  : (heap -> Type0))
  (#prref: mref_pred)
  (#hrel : FStar.Preorder.preorder heap)
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  (bt_read :  tbt_read inv prref hrel)
  (bt_write : tbt_write inv prref hrel)
  (bt_alloc : tbt_alloc inv prref hrel)
  (#g:context)
  (#e:exp)
  (#t:typ)
  (tyj:typing g e t)
  (ve:(vcontext (mk_targetlang_pspec inv prref hrel) g){all_refs_contained_and_low ve}) :
  ST (elab_typ (mk_targetlang_pspec inv prref hrel) t)
    (fun h0 -> inv h0)
    (fun h0 r h1 -> inv h1 /\ h0 `hrel` h1 /\ (elab_typ_tc #(mk_targetlang_pspec inv prref hrel) t).wt.satisfy r prref)
    (decreases %[e;1])
=
  let rcall #g #e (#t:typ) = backtranslate #inv #prref #hrel bt_read bt_write bt_alloc #g #e #t in
  let pspec = mk_targetlang_pspec inv prref hrel in

  match tyj with
  | TyUnit -> raise_val ()
  | TyZero -> raise_val 0
  | TySucc tyj_s ->
    raise_val (1 + (downgrade_val (rcall tyj_s ve)))

  | TyAllocRef #_ #_ #t tyj_e -> begin
    let v : elab_typ0 t = downgrade #pspec (rcall tyj_e ve) in
    let r : ref (elab_typ0 t) = bt_alloc #t v in
    raise_val r
  end
  | TyReadRef #_ #_ #t tyj_e -> begin
    let r' : ref (elab_typ0 t) = downgrade (rcall tyj_e ve) in
    raise #pspec #t (bt_read r')
  end
  | TyWriteRef #_ #_ #_ #t tyj_ref tyj_v -> begin
    let r : ref (elab_typ0 t) = downgrade (rcall tyj_ref ve) in
    let v : elab_typ0 t = downgrade (rcall tyj_v ve) in
    bt_write #t r v;
    raise_val ()
  end

  | TyAbs _ _ ->
    backtranslate_eabs #inv #prref #hrel bt_read bt_write bt_alloc #g #e #t tyj ve
  | TyVar vx ->
    let Some tx = g vx in
    let x : elab_typ pspec tx = ve vx in
    x
  | TyApp #_ #_ #_ #tx #tres tyj_f tyj_x ->
    assert ((elab_typ pspec t) == (elab_typ pspec tres));
    let f : elab_typ pspec (TArr tx tres) = rcall tyj_f ve in
    let x : elab_typ pspec tx = rcall tyj_x ve in
    elab_apply_arrow tx tres f x

  | TyInl #_ #_ #t1 #t2 tyj_1 ->
    let v1 : elab_typ pspec t1 = rcall tyj_1 ve in
    Inl #_ #(elab_typ pspec t2) v1
  | TyInr #_ #_ #t1 #t2 tyj_2 ->
    let v2 : elab_typ pspec t2 = rcall tyj_2 ve in
    Inr #(elab_typ pspec t1) v2
  | TyCaseSum #_ #_ #_ #_ #tl #tr #tres tyj_c tyj_l tyj_r -> begin
    let vc : either (elab_typ pspec tl) (elab_typ pspec tr) = rcall tyj_c ve in
    match vc with
    | Inl x ->
      let f : elab_typ pspec (TArr tl tres) = rcall tyj_l ve in
      elab_apply_arrow tl tres f x
    | Inr y ->
      let f : elab_typ pspec (TArr tr tres) = rcall tyj_r ve in
      elab_apply_arrow tr tres f y
  end

  | TyFst #_ #_ #tf #ts tyj_e ->
    let v = rcall tyj_e ve in
    fst #(elab_typ pspec tf) #(elab_typ pspec ts) v
  | TySnd #_ #_ #tf #ts tyj_e ->
    let v = rcall tyj_e ve in
    snd #(elab_typ pspec tf) #(elab_typ pspec ts) v
  | TyPair #_ #_ #_ #tf #ts tyj_f tyj_s->
    let vf : elab_typ pspec tf = rcall tyj_f ve in
    let vs : elab_typ pspec ts = rcall tyj_s ve in
    (vf, vs)
and backtranslate_eabs
  (#inv  : (heap -> Type0))
  (#prref: mref_pred)
  (#hrel : FStar.Preorder.preorder heap)
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  (bt_read :  tbt_read inv prref hrel)
  (bt_write : tbt_write inv prref hrel)
  (bt_alloc : tbt_alloc inv prref hrel)
  (#g:context)
  (#e:exp{EAbs? e})
  (#t:typ)
  (tyj:typing g e t)
  (ve:(vcontext (mk_targetlang_pspec inv prref hrel) g){all_refs_contained_and_low ve}) :
  Tot (elab_typ (mk_targetlang_pspec inv prref hrel) t) (decreases %[e;0]) =
  let pspec = mk_targetlang_pspec inv prref hrel in
  let rcall #g #e (#t:typ) = backtranslate #inv #prref #hrel bt_read bt_write bt_alloc #g #e #t in
  match e with
  | EAbs t1 e1 ->
    let TyAbs tx #_ #tres tyj_body = tyj in
    let w : mk_targetlang_arrow pspec (elab_typ pspec tx) #(elab_typ_tc #pspec tx).wt (elab_typ pspec tres) #(elab_typ_tc #pspec tres).wt =
      (fun (x:elab_typ pspec tx) ->
        let ve' = vextend #pspec #tx x #g ve in
        rcall tyj_body ve')
    in
    assert (t == TArr tx tres);
    cast_TArr inv prref hrel #tx #tres w t


let rec lemma_satisfy_on_heap_eqv_forall_refs_heap pspec (#t:typ0) (v:elab_typ0 t) h (pred:mref_heap_stable_pred) :
  Lemma ((elab_typ0_tc #pspec t).wt.satisfy_on_heap v h pred <==> forall_refs_heap pred h #(to_shareable_typ t) v) =
  match t with
  | TUnit -> ()
  | TNat -> ()
  | TSum t1 t2 -> begin
    let v : either (elab_typ0 t1) (elab_typ0 t2) = v in
    match v with
    | Inl lv -> lemma_satisfy_on_heap_eqv_forall_refs_heap pspec lv h pred
    | Inr rv -> lemma_satisfy_on_heap_eqv_forall_refs_heap pspec rv h pred
  end
  | TPair t1 t2 -> begin
     let v : (elab_typ0 t1) * (elab_typ0 t2) = v in
     lemma_satisfy_on_heap_eqv_forall_refs_heap pspec (fst v) h pred;
     lemma_satisfy_on_heap_eqv_forall_refs_heap pspec (snd v) h pred;
     assert ((elab_typ0_tc #pspec t).wt.satisfy_on_heap v h pred <==> forall_refs_heap pred h #(to_shareable_typ t) v)
  end
  | TRef t' ->
    let aux (#t':typ0) (v:elab_typ0 (TRef t')) : ref (elab_typ0 t') = v in
    let v : ref (elab_typ0 t') = aux v in
    assert ((elab_typ0_tc #pspec t).wt.satisfy_on_heap v h pred <==> forall_refs_heap pred h #(to_shareable_typ t) v) by (compute ())
  | TLList t' -> begin
    let aux (#t':typ0) (v:elab_typ0 (TLList t')) : linkedList (elab_typ0 t') = v in
    let v : linkedList (elab_typ0 t') = aux v in
    match v with
    | LLNil -> ()
    | LLCons v' xsref -> (
      lemma_satisfy_on_heap_eqv_forall_refs_heap pspec v' h pred;
      let xsref : ref (linkedList (elab_typ0 t')) = xsref in
      assert ((elab_typ0_tc #pspec t).wt.satisfy_on_heap v h pred <==> forall_refs_heap pred h #(to_shareable_typ t) v))
  end

let rec lemma_satisfy_eqv_forall_refs pspec (#t:typ0) (v:elab_typ0 t) (pred:mref_pred) :
  Lemma ((elab_typ0_tc #pspec t).wt.satisfy v pred <==> forall_refs pred #(to_shareable_typ t) v) =
  match t with
  | TUnit -> ()
  | TNat -> ()
  | TSum t1 t2 -> begin
    let v : either (elab_typ0 t1) (elab_typ0 t2) = v in
    match v with
    | Inl lv -> lemma_satisfy_eqv_forall_refs pspec lv pred
    | Inr rv -> lemma_satisfy_eqv_forall_refs pspec rv pred
  end
  | TPair t1 t2 -> begin
     let v : (elab_typ0 t1) * (elab_typ0 t2) = v in
     lemma_satisfy_eqv_forall_refs pspec (fst v) pred;
     lemma_satisfy_eqv_forall_refs pspec (snd v) pred;
     assert ((elab_typ0_tc #pspec t).wt.satisfy v pred <==> forall_refs pred #(to_shareable_typ t) v)
  end
  | TRef t' ->
    let aux (#t':typ0) (v:elab_typ0 (TRef t')) : ref (elab_typ0 t') = v in
    let v : ref (elab_typ0 t') = aux v in
    assert ((elab_typ0_tc #pspec t).wt.satisfy v pred <==> forall_refs pred #(to_shareable_typ t) v) by (compute ())
  | TLList t' -> begin
    let aux (#t':typ0) (v:elab_typ0 (TLList t')) : linkedList (elab_typ0 t') = v in
    let v : linkedList (elab_typ0 t') = aux v in
    match v with
    | LLNil -> ()
    | LLCons v' xsref -> (
      lemma_satisfy_eqv_forall_refs pspec v' pred;
      let xsref : ref (linkedList (elab_typ0 t')) = xsref in
      assert ((elab_typ0_tc #pspec t).wt.satisfy v pred <==> forall_refs pred #(to_shareable_typ t) v))
  end

val bt_read : tbt_read (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec)
let bt_read #t r =
  lemma_satisfy_eqv_forall_refs default_spec #(TRef t) r (Mktuple3?._2 default_spec);
  let v = tl_read #(to_shareable_typ t) r in
  lemma_satisfy_eqv_forall_refs default_spec #t v (Mktuple3?._2 default_spec);
  v

val bt_write : tbt_write (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec)
let bt_write #t r v =
  lemma_satisfy_eqv_forall_refs default_spec #(TRef t) r (Mktuple3?._2 default_spec);
  lemma_satisfy_eqv_forall_refs default_spec #t v (Mktuple3?._2 default_spec);
  tl_write #(to_shareable_typ t) r v

val bt_alloc : tbt_alloc (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec)
let bt_alloc #t init =
  lemma_satisfy_eqv_forall_refs default_spec #t init (Mktuple3?._2 default_spec);
  let r = tl_alloc #(to_shareable_typ t) init in
  lemma_satisfy_eqv_forall_refs default_spec #(TRef t) r (Mktuple3?._2 default_spec);
  r
