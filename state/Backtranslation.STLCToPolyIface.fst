module Backtranslation.STLCToPolyIface

open FStar.Tactics
open FStar.Tactics.Typeclasses

open SharedRefs
open Witnessable
open PolyIface
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

instance tc_shareable_type_typ0 (t:typ0) : tc_shareable_type (elab_typ0 t) = {
  __t = to_shareable_typ t;
}

let rec elab_typ0_tc #a3p (t:typ0) : poly_iface a3p (elab_typ0 t) =
  match t with
  | TUnit -> poly_iface_unit a3p
  | TNat -> poly_iface_int a3p
  | TSum t1 t2 -> poly_iface_sum a3p _ #(elab_typ0_tc t1) _ #(elab_typ0_tc t2)
  | TPair t1 t2 -> poly_iface_pair a3p _ #(elab_typ0_tc t1) _ #(elab_typ0_tc t2)
  | TRef t -> poly_iface_ref a3p (elab_typ0 t) #solve
  | TLList t -> poly_iface_llist a3p (elab_typ0 t) #solve

let rec _elab_typ (#a3p:threep) (t:typ) : tt:Type u#1 & poly_iface a3p tt =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = _elab_typ t1 in
    let tt2 = _elab_typ t2 in
    (| mk_poly_arrow a3p (dfst tt1) #(dsnd tt1).wt (dfst tt2) #(dsnd tt2).wt,
       poly_iface_arrow a3p (dfst tt1) (dfst tt2)
    |)
  end
  | TUnit -> (| raise_t unit, solve |)
  | TNat -> (| raise_t int, solve |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 in
    let (| tt2, c_tt2 |) = _elab_typ t2 in
    (| either tt1 tt2, poly_iface_sum a3p tt1 #c_tt1 tt2 #c_tt2 |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 in
    let (| tt2, c_tt2 |) = _elab_typ t2 in
    (| tt1 * tt2, poly_iface_pair a3p tt1 #c_tt1 tt2 #c_tt2 |)
  | TRef _ ->
    let tt = elab_typ0 t in
    let c_tt = elab_typ0_tc t in
    (| raise_t tt, poly_iface_univ_raise a3p _ #c_tt |)
  | TLList t ->
    let tt = elab_typ0 t in
    (| raise_t (linkedList tt), poly_iface_univ_raise a3p _ #(poly_iface_llist a3p tt #(tc_shareable_type_typ0 t)) |)

let elab_typ (a3p:threep) (t:typ) : Type =
  dfst (_elab_typ #a3p t)

let elab_typ_tc #a3p (t:typ) : poly_iface a3p (elab_typ a3p t) =
  dsnd (_elab_typ #a3p t)

type tbt_read (a3p:threep) =
  (#t:typ0) -> r:ref (elab_typ0 t) ->
    ST (elab_typ0 t)
      (requires (fun h0 -> inv a3p h0 /\ prref a3p r))
      (ensures  (fun h0 v h1 -> h0 `hrel a3p` h1 /\ inv a3p h1 /\ (elab_typ0_tc #a3p t).wt.satisfy v (prref a3p)))

type tbt_write (a3p:threep) =
  (#t:typ0) -> r:ref (elab_typ0 t) -> v:(elab_typ0 t) ->
    ST unit
      (requires (fun h0 -> inv a3p h0 /\ prref a3p r /\ (elab_typ0_tc #a3p t).wt.satisfy v (prref a3p)))
      (ensures  (fun h0 _ h1 -> h0 `hrel a3p` h1 /\ inv a3p h1))

type tbt_alloc (a3p:threep) =
  (#t:typ0) -> init:(elab_typ0 t) ->
    ST (ref (elab_typ0 t))
      (requires (fun h0 -> inv a3p h0 /\ (elab_typ0_tc #a3p t).wt.satisfy init (prref a3p)))
      (ensures  (fun h0 r h1 -> h0 `hrel a3p` h1 /\ inv a3p h1 /\ prref a3p r))

let elab_poly_typ (t:typ) =
  #a3p:threep ->
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  read :  tbt_read a3p ->
  write : tbt_write a3p ->
  alloc : tbt_alloc a3p ->
  (** type of the context: *)
  elab_typ a3p t

(** ** Examples **)

val ctx_update_ref_test :
  elab_poly_typ (TArr (TRef TNat) TUnit)
let ctx_update_ref_test bt_read bt_write _ y =
  let y : ref int = downgrade_val y in
  bt_write #TNat y (bt_read #TNat y + 1);
  raise_val ()

val ctx_update_multiple_refs_test :
  elab_poly_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit))
let ctx_update_multiple_refs_test #a3p bt_read bt_write _ x =
  let x : ref (ref int) = downgrade_val x in
  let cb : elab_typ a3p (TArr (TRef TNat) TUnit) = (fun y ->
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
let ctx_swap_ref_test #a3p bt_read bt_write _ x =
  let x : ref (ref int) = downgrade_val x in
  let cb : elab_typ a3p (TArr (TRef (TRef TNat)) TUnit) = (fun y ->
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
let ctx_returns_callback_test #a3p bt_read bt_write bt_alloc _ =
  let x: ref int = bt_alloc #TNat 13 in
  let cb : elab_typ a3p (TArr TUnit TUnit) = (fun _ ->
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

val ctx_unverified_student_hw_sort :
  elab_poly_typ (TArr (TRef (TLList TNat)) TUnit)
let ctx_unverified_student_hw_sort #a3p bt_read bt_write bt_alloc =
  let rec sort (fuel:nat) (l:ref (linkedList int)) : ST unit (pre_poly_arrow a3p l) (post_poly_arrow a3p) =
    if fuel = 0 then () else begin
      let cl : linkedList int = bt_read #(TLList TNat) l in
      match cl with | LLNil -> ()
      | LLCons x tl -> begin
         sort (fuel-1) tl;
         let ctl : linkedList int = bt_read #(TLList TNat) tl in
         match ctl with | LLNil -> ()
         | LLCons x' tl' ->
           if x <= x' then ()
           else begin
             let new_tl = bt_alloc #(TLList TNat) (LLCons x tl') in
             bt_write #(TLList TNat) l (LLCons x' new_tl);
             sort (fuel-1) new_tl;
             ()
           end
      end
    end
  in
  (fun l -> raise_val (sort 1000 (downgrade_val l)))

val progr_sep_test:
  #rp: ref int ->
  ctx:(elab_typ c3p (TArr TUnit TUnit)) ->
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
  ctx:(elab_typ c3p (TArr (TRef TNat) TUnit)) ->
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

#push-options "--split_queries always"
val progr_declassify_nested:
  rp: ref (ref int) ->
  ctx:(elab_typ c3p (TArr (TRef (TRef TNat)) TUnit)) ->
  SST unit
    (requires (fun h0 ->
      satisfy_on_heap rp h0 contains_pred /\
      is_private rp h0 /\
      is_private (sel h0 rp) h0))
    (ensures (fun h0 _ h1 -> True))
let progr_declassify_nested rp f =
  let p : ref int = sst_read rp in
  sst_share #SNat p;
  sst_share #(SRef SNat) rp;
  witness (contains_pred rp);
  witness (is_shared rp);
  downgrade_val (f (raise_val rp))
#pop-options

val progr_secret_unchanged_test:
  rp: ref int ->
  rs: ref (ref int) ->
  ctx:(elab_typ c3p (TArr TUnit TUnit)) ->
  SST unit
    (requires (fun h0 ->
      satisfy_on_heap rp h0 contains_pred /\
      is_private rp h0 /\
      satisfy_on_heap rs h0 is_shared))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp))
let progr_secret_unchanged_test rp rs ctx =
  let secret: ref int = sst_alloc_shareable #SNat 0 in
  downgrade_val (ctx (raise_val ()));
  let v = sst_read secret in
  ()

#push-options "--split_queries always --z3rlimit 10000"
val progr_passing_shared_to_callback_test:
  rp: ref int ->
  rs: ref (ref int) ->
  ctx:(elab_typ c3p (TArr (TArr TUnit TUnit) TUnit)) ->
  SST unit
    (requires (fun h0 ->
      satisfy_on_heap rp h0 contains_pred /\
      is_private rp h0 /\
      satisfy_on_heap rs h0 is_shared))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
// TODO: the callback of the program should be able to modify rp (DA: now the callbacks can modify encapsulated, not private references)
let progr_passing_shared_to_callback_test rp rs f =
  let secret: ref int = sst_alloc_shareable #SNat 0 in
  sst_share #SNat secret;
  witness (contains_pred secret); witness (is_shared secret);
  let cb: elab_typ c3p (TArr TUnit TUnit) = (fun _ ->
    recall (contains_pred secret); recall (is_shared secret);
    sst_write_shareable #SNat secret (!secret + 1);
    raise_val ()) in
  downgrade_val (f cb);
  ()

val progr_passing_encapsulated_to_callback_test:
  rp: ref int ->
  rs: ref (ref int) ->
  ctx:(elab_typ c3p (TArr (TArr TUnit TUnit) TUnit)) ->
  SST unit
    (requires (fun h0 ->
      satisfy_on_heap rp h0 contains_pred /\
      is_private rp h0 /\
      satisfy_on_heap rs h0 is_shared))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
let progr_passing_encapsulated_to_callback_test rp rs f =
  let secret: ref int = sst_alloc_shareable #SNat 0 in
  sst_encapsulate secret;
  witness (contains_pred secret); witness (is_encapsulated secret);
  let cb: elab_typ c3p (TArr TUnit TUnit) = (fun _ ->
    recall (contains_pred secret); recall (is_encapsulated secret);
    sst_write_shareable #SNat secret (!secret + 1);
    raise_val ()) in
  downgrade_val (f cb);
  ()
#pop-options

(*
(** DA: make fails without an assume on this val because of [@expect_failure] *)
val progr_passing_private_to_callback_test:
  ctx:(elab_typ c3p (TArr (TArr TUnit TUnit) TUnit)) ->
  SST unit
    (requires (fun h0 -> True))
    (ensures (fun h0 _ h1 -> True))
[@expect_failure]
let progr_passing_private_to_callback_test f =
  let secret: ref int = sst_alloc #SNat 0 in
  witness (contains_pred secret);
  let cb: elab_typ c3p (TArr TUnit TUnit) = (fun _ ->
    recall (contains_pred secret);
    // let h0 = get_heap () in
    // assume (is_shared secret h0);
    sst_write_shareable #SNat secret (!secret + 1);
    raise_val ()) in
  downgrade_val (f cb);
  ()
*)

val progr_getting_callback_test:
  rp: ref int ->
  rs: ref (ref int) ->
  ctx:(elab_typ c3p (TArr TUnit (TArr TUnit TUnit))) ->
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
  #a3p : threep ->
  t1:typ ->
  t2:typ ->
  f:elab_typ a3p (TArr t1 t2) ->
  (let tt1 = _elab_typ #a3p t1 in
   let tt2 = _elab_typ #a3p t2 in
   mk_poly_arrow a3p (dfst tt1) #(dsnd tt1).wt (dfst tt2) #(dsnd tt2).wt)
let elab_apply_arrow t1 t2 f x = f x

let cast_TArr #a3p (#t1 #t2:typ) (f : elab_typ a3p (TArr t1 t2)) (t:typ) (#_:squash (t == TArr t1 t2)) : elab_typ a3p t = f

type vcontext a3p (g:context) =
  vx:var{Some? (g vx)} -> elab_typ a3p (Some?.v (g vx))

let vempty a3p : vcontext a3p empty = fun _ -> assert false

let vextend #a3p #t (x:elab_typ a3p t) (#g:context) (ve:vcontext a3p g) : vcontext a3p (extend t g) =
  fun y -> if y = 0 then x else ve (y-1)

let all_refs_contained_and_low (#a3p) (#g:context) (ve:vcontext a3p g) : Type0 =
  forall vx. Some? (g vx) ==>
    (elab_typ_tc #a3p (Some?.v (g vx))).wt.satisfy (ve vx) (Mktuple3?._2 a3p)

let rec downgrade_typ #a3p (t:typ0) (x:elab_typ a3p t) : elab_typ0 t =
  match t with
  | TSum t1 t2 -> begin
    let x : either (elab_typ a3p t1) (elab_typ a3p t2) = x in
    (match x with
    | Inl v -> Inl (downgrade_typ t1 v)
    | Inr v -> Inr (downgrade_typ t2 v)) <: either (elab_typ0 t1) (elab_typ0 t2)
    end
  | TPair t1 t2 -> begin
    let x : elab_typ a3p t1 * elab_typ a3p t2 = x in
    let (v1, v2) = x in
    (downgrade_typ t1 v1, downgrade_typ t2 v2)
  end
  | _ -> downgrade_val x

let rec raise_typ #a3p (t:typ0) (x:elab_typ0 t) : elab_typ a3p t =
  match t with
  | TSum t1 t2 -> begin
    let x : either (elab_typ0 t1) (elab_typ0 t2) = x in
    (match x with
    | Inl v -> Inl (raise_typ t1 v)
    | Inr v -> Inr (raise_typ t2 v)) <: either (elab_typ a3p t1) (elab_typ a3p t2)
    end
  | TPair t1 t2 -> begin
    let x : elab_typ0 t1 * elab_typ0 t2 = x in
    let (v1, v2) = x in
    (raise_typ #a3p t1 v1, raise_typ #a3p t2 v2)
  end
  | _ -> raise_val x

let rec lemma_downgrade_typ #a3p (t:typ0) (x:elab_typ a3p t) :
  Pure unit
    (requires ((elab_typ_tc #a3p t).wt.satisfy x (Mktuple3?._2 a3p)))
    (ensures (fun r -> (elab_typ0_tc #a3p t).wt.satisfy (downgrade_typ t x) (Mktuple3?._2 a3p))) =
  match t with
  | TSum t1 t2 -> begin
    let x : either (elab_typ a3p t1) (elab_typ a3p t2) = x in
    (match x with
    | Inl v -> lemma_downgrade_typ t1 v
    | Inr v -> lemma_downgrade_typ t2 v)
  end
  | TPair t1 t2 -> begin
    let x : elab_typ a3p t1 * elab_typ a3p t2 = x in
    let (v1, v2) = x in
    lemma_downgrade_typ t1 v1;
    lemma_downgrade_typ t2 v2
  end
  | _ -> ()

let rec lemma_raise_typ a3p (t:typ0) (x:elab_typ0 t) :
  Pure unit
    (requires ((elab_typ0_tc #a3p t).wt.satisfy x (Mktuple3?._2 a3p)))
    (ensures (fun r -> (elab_typ_tc #a3p t).wt.satisfy (raise_typ #a3p t x) (Mktuple3?._2 a3p))) =
  match t with
  | TSum t1 t2 -> begin
    let x : either (elab_typ0 t1) (elab_typ0 t2) = x in
    (match x with
    | Inl v -> lemma_raise_typ a3p t1 v
    | Inr v -> lemma_raise_typ a3p t2 v)
  end
  | TPair t1 t2 -> begin
    let x : elab_typ0 t1 * elab_typ0 t2 = x in
    let (v1, v2) = x in
    lemma_raise_typ a3p t1 v1;
    lemma_raise_typ a3p t2 v2
  end
  | _ -> ()

let downgrade #a3p (#t:typ0) (x:elab_typ a3p t) :
  Pure (elab_typ0 t)
    (requires ((elab_typ_tc t).wt.satisfy x (Mktuple3?._2 a3p)))
    (ensures (fun r -> r == downgrade_typ t x /\ (elab_typ0_tc #a3p t).wt.satisfy r (Mktuple3?._2 a3p))) =
    lemma_downgrade_typ t x;
    downgrade_typ t x

let raise #a3p (#t:typ0) (x:elab_typ0 t) :
  Pure (elab_typ a3p t)
    (requires ((elab_typ0_tc #a3p t).wt.satisfy x (Mktuple3?._2 a3p)))
    (ensures (fun r -> r == raise_typ t x /\ (elab_typ_tc t).wt.satisfy r (Mktuple3?._2 a3p))) =
    lemma_raise_typ a3p t x;
    raise_typ t x

#push-options "--split_queries always"
let rec backtranslate
  (#a3p:threep)
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  (bt_read :  tbt_read a3p)
  (bt_write : tbt_write a3p)
  (bt_alloc : tbt_alloc a3p)
  (#g:context)
  (#e:exp)
  (#t:typ)
  (tyj:typing g e t)
  (ve:(vcontext a3p g){all_refs_contained_and_low ve}) :
  ST (elab_typ a3p t)
    (fun h0 -> inv a3p h0)
    (fun h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1 /\ (elab_typ_tc #a3p t).wt.satisfy r (prref a3p))
    (decreases %[e;1])
=
  let rcall #g #e (#t:typ) = backtranslate #a3p bt_read bt_write bt_alloc #g #e #t in

  match tyj with
  | TyUnit -> raise_val ()
  | TyZero -> raise_val 0
  | TySucc tyj_s ->
    raise_val (1 + (downgrade_val (rcall tyj_s ve)))

  | TyAllocRef #_ #_ #t tyj_e -> begin
    let v : elab_typ0 t = downgrade #a3p (rcall tyj_e ve) in
    let r : ref (elab_typ0 t) = bt_alloc #t v in
    raise_val r
  end
  | TyReadRef #_ #_ #t tyj_e -> begin
    let r' : ref (elab_typ0 t) = downgrade (rcall tyj_e ve) in
    raise #a3p #t (bt_read r')
  end
  | TyWriteRef #_ #_ #_ #t tyj_ref tyj_v -> begin
    let r : ref (elab_typ0 t) = downgrade (rcall tyj_ref ve) in
    let v : elab_typ0 t = downgrade (rcall tyj_v ve) in
    bt_write #t r v;
    raise_val ()
  end

  | TyAbs _ _ ->
    backtranslate_eabs #a3p bt_read bt_write bt_alloc #g #e #t tyj ve
  | TyVar vx ->
    let Some tx = g vx in
    let x : elab_typ a3p tx = ve vx in
    x
  | TyApp #_ #_ #_ #tx #tres tyj_f tyj_x ->
    assert ((elab_typ a3p t) == (elab_typ a3p tres));
    let f : elab_typ a3p (TArr tx tres) = rcall tyj_f ve in
    let x : elab_typ a3p tx = rcall tyj_x ve in
    elab_apply_arrow tx tres f x

  | TyInl #_ #_ #t1 #t2 tyj_1 ->
    let v1 : elab_typ a3p t1 = rcall tyj_1 ve in
    Inl #_ #(elab_typ a3p t2) v1
  | TyInr #_ #_ #t1 #t2 tyj_2 ->
    let v2 : elab_typ a3p t2 = rcall tyj_2 ve in
    Inr #(elab_typ a3p t1) v2
  | TyCaseSum #_ #_ #_ #_ #tl #tr #tres tyj_c tyj_l tyj_r -> begin
    let vc : either (elab_typ a3p tl) (elab_typ a3p tr) = rcall tyj_c ve in
    match vc with
    | Inl x ->
      let f : elab_typ a3p (TArr tl tres) = rcall tyj_l ve in
      elab_apply_arrow tl tres f x
    | Inr y ->
      let f : elab_typ a3p (TArr tr tres) = rcall tyj_r ve in
      elab_apply_arrow tr tres f y
  end

  | TyFst #_ #_ #tf #ts tyj_e ->
    let v = rcall tyj_e ve in
    fst #(elab_typ a3p tf) #(elab_typ a3p ts) v
  | TySnd #_ #_ #tf #ts tyj_e ->
    let v = rcall tyj_e ve in
    snd #(elab_typ a3p tf) #(elab_typ a3p ts) v
  | TyPair #_ #_ #_ #tf #ts tyj_f tyj_s->
    let vf : elab_typ a3p tf = rcall tyj_f ve in
    let vs : elab_typ a3p ts = rcall tyj_s ve in
    (vf, vs)
and backtranslate_eabs
  (#a3p:threep)
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  (bt_read :  tbt_read a3p)
  (bt_write : tbt_write a3p)
  (bt_alloc : tbt_alloc a3p)
  (#g:context)
  (#e:exp{EAbs? e})
  (#t:typ)
  (tyj:typing g e t)
  (ve:(vcontext a3p g){all_refs_contained_and_low ve}) :
  Tot (elab_typ a3p t) (decreases %[e;0]) =
  let rcall #g #e (#t:typ) = backtranslate #a3p bt_read bt_write bt_alloc #g #e #t in
  match e with
  | EAbs t1 e1 ->
    let TyAbs tx #_ #tres tyj_body = tyj in
    let w : mk_poly_arrow a3p (elab_typ a3p tx) #(elab_typ_tc #a3p tx).wt (elab_typ a3p tres) #(elab_typ_tc #a3p tres).wt =
      (fun (x:elab_typ a3p tx) ->
        let ve' = vextend #a3p #tx x #g ve in
        rcall tyj_body ve')
    in
    assert (t == TArr tx tres);
    cast_TArr #a3p #tx #tres w t
#pop-options

let rec lemma_satisfy_eqv_forall_refs a3p (#t:typ0) (v:elab_typ0 t) (pred:mref_pred) :
  Lemma ((elab_typ0_tc #a3p t).wt.satisfy v pred <==> forall_refs pred #(to_shareable_typ t) v) =
  match t with
  | TUnit -> ()
  | TNat -> ()
  | TSum t1 t2 -> begin
    let v : either (elab_typ0 t1) (elab_typ0 t2) = v in
    match v with
    | Inl lv -> lemma_satisfy_eqv_forall_refs a3p lv pred
    | Inr rv -> lemma_satisfy_eqv_forall_refs a3p rv pred
  end
  | TPair t1 t2 -> begin
     let v : (elab_typ0 t1) * (elab_typ0 t2) = v in
     lemma_satisfy_eqv_forall_refs a3p (fst v) pred;
     lemma_satisfy_eqv_forall_refs a3p (snd v) pred;
     assert ((elab_typ0_tc #a3p t).wt.satisfy v pred <==> forall_refs pred #(to_shareable_typ t) v)
  end
  | TRef t' ->
    let aux (#t':typ0) (v:elab_typ0 (TRef t')) : ref (elab_typ0 t') = v in
    let v : ref (elab_typ0 t') = aux v in
    assert ((elab_typ0_tc #a3p t).wt.satisfy v pred <==> forall_refs pred #(to_shareable_typ t) v) by (compute ())
  | TLList t' -> begin
    let aux (#t':typ0) (v:elab_typ0 (TLList t')) : linkedList (elab_typ0 t') = v in
    let v : linkedList (elab_typ0 t') = aux v in
    match v with
    | LLNil -> ()
    | LLCons v' xsref -> (
      lemma_satisfy_eqv_forall_refs a3p v' pred;
      let xsref : ref (linkedList (elab_typ0 t')) = xsref in
      assert ((elab_typ0_tc #a3p t).wt.satisfy v pred <==> forall_refs pred #(to_shareable_typ t) v))
  end

val bt_read : tbt_read c3p
let bt_read #t r =
  lemma_satisfy_eqv_forall_refs c3p #(TRef t) r (prref_c);
  let v : elab_typ0 t = tl_read #(to_shareable_typ t) r in
  lemma_satisfy_eqv_forall_refs c3p #t v (prref_c);
  v

val bt_write : tbt_write c3p
let bt_write #t r v =
  lemma_satisfy_eqv_forall_refs c3p #(TRef t) r (prref_c);
  lemma_satisfy_eqv_forall_refs c3p #t v (prref_c);
  tl_write #(to_shareable_typ t) r v

val bt_alloc : tbt_alloc c3p
let bt_alloc #t init =
  lemma_satisfy_eqv_forall_refs c3p #t init (prref_c);
  let r = tl_alloc #(to_shareable_typ t) init in
  lemma_satisfy_eqv_forall_refs c3p #(TRef t) r (prref_c);
  r
