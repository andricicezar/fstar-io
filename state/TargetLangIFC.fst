module TargetLangIFC

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses

open Monotonic.IFC.Heap
open IFC.Heap.ST

(** target_lang is a shallow embedding of STLC **)
class target_lang (t:Type) = {
  shallowly_contained : t -> lheap -> Type0;
  shallowly_low : t -> lheap -> Type0;

  shallowly_witness : x:t -> ST (recall:(unit -> ST unit (fun _ -> True) (fun h0 _ h1 -> h0 == h1 /\ shallowly_contained x h1 /\ shallowly_low x h1)))
    (requires (fun h0 -> shallowly_contained x h0 /\ shallowly_low x h0))
    (ensures (fun h0 _ h1 -> h0 == h1))
}

instance target_lang_unit : target_lang unit = {
  shallowly_contained = (fun _ _ -> True);
  shallowly_low = (fun _ _ -> True);
  shallowly_witness = (fun _ -> (fun () -> ()));
}

instance target_lang_int : target_lang int = {
  shallowly_contained = (fun _ _ -> True);
  shallowly_low = (fun _ _ -> True);
  shallowly_witness = (fun _ -> (fun () -> ()));
}

instance target_lang_pair (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (t1 * t2) = {
  shallowly_contained = (fun (x1, x2) h -> c1.shallowly_contained x1 h /\ c2.shallowly_contained x2 h);
  shallowly_low = (fun (x1, x2) h -> c1.shallowly_low x1 h /\ c2.shallowly_low x2 h);
  shallowly_witness = (fun (x1,x2) -> 
    let w1 = c1.shallowly_witness x1 in
    let w2 = c2.shallowly_witness x2 in
    (fun () -> w1 (); w2 ()))
}

instance target_lang_sum (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (either t1 t2) = {
  shallowly_contained = (fun x h ->
    match x with
    | Inl x1 -> c1.shallowly_contained x1 h
    | Inr x2 -> c2.shallowly_contained x2 h);
  shallowly_low = (fun x h ->
    match x with
    | Inl x1 -> c1.shallowly_low x1 h
    | Inr x2 -> c2.shallowly_low x2 h);
  shallowly_witness = (fun x -> 
    match x with 
    | Inl x1 -> (let w = c1.shallowly_witness x1 in (fun () -> w ()))
    | Inr x2 -> (let w = c2.shallowly_witness x2 in (fun () -> w ())))
}

instance target_lang_ref (t:Type) {| c:target_lang t |} : target_lang (ref t) = {
  shallowly_contained = (fun (x:ref t) h -> 
    is_mm x == false /\ contains_pred x h);
  shallowly_low = (fun (x:ref t) h -> is_low_pred x h);
  shallowly_witness = (fun x -> 
    gst_witness (contains_pred x);
    gst_witness (is_low_pred x);
    (fun () -> 
      gst_recall (contains_pred x);
      gst_recall (is_low_pred x)))
}

open FStar.Preorder

let inv_contains_points_to_contains (h:lheap) =
  (* TODO: the forall on target_lang is creating problems in proofs. 
    One solution would be to quantify over STLC types and use elab_typ. However,
    the definitions depend one on other.
  *)
  (forall (a:Type) (c:target_lang a) (r:ref a).
    shallowly_contained r h ==> c.shallowly_contained (sel h r) h)

let inv_low_points_to_low (h:lheap) =
  (forall (a:Type) (c:target_lang a) (r:ref a).
    shallowly_low r h ==> c.shallowly_low (sel h r) h)

let inv_low_contains (h:lheap) = 
  inv_contains_points_to_contains h /\
  inv_low_points_to_low h

unfold let shallowly_contained_low (#a:Type) {| c:target_lang a |} (v:a) (h:lheap) =
  c.shallowly_contained v h /\ c.shallowly_low v h

effect IST (a:Type) (pre:st_pre) (post: (h:lheap -> Tot (st_post' a (pre h)))) =
  ST a 
    (requires (fun h0 -> 
      inv_low_contains h0 /\
      pre h0))
    (ensures (fun h0 r h1 ->
      inv_low_contains h1 /\
      post h0 r h1))

unfold let pre_tgt_arrow
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (h0:lheap) =
  shallowly_contained_low #t1 #tgtx x h0

unfold let post_tgt_arrow
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (#t2:Type) {| tgtr : target_lang t2 |}
  (h0:lheap) (r:t2) (h1:lheap) =
  modifies_only_label Low h0 h1 /\                                       (* allows low references to be modified *)
  modifies_classification Set.empty h0 h1 /\                             (* no modifications of the classification *)
  shallowly_contained_low r h1

let mk_tgt_arrow 
  (t1:Type)
  {| tgt_t1: target_lang t1 |}
  (t2:Type)
  {| c2 : target_lang t2 |}
= x:t1 -> IST t2 
    (requires (pre_tgt_arrow x #tgt_t1))
    (ensures (post_tgt_arrow x #tgt_t1 #t2 #c2))

instance target_lang_arrow 
  (t1:Type)
  {| target_lang t1 |}
  (t2:Type)
  {| target_lang t2 |}
  : target_lang (mk_tgt_arrow t1 t2) = {
    shallowly_contained = (fun _ _ -> True);
    shallowly_low = (fun _ _ -> True);
    shallowly_witness = (fun _ -> (fun () -> ()));
  }


open STLC

(** *** Elaboration of types to F* *)
let rec _elab_typ (t:typ) : tt:Type & target_lang tt =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = _elab_typ t1 in
    let tt2 = _elab_typ t2 in
    (| mk_tgt_arrow      (dfst tt1) #(dsnd tt1) (dfst tt2) #(dsnd tt2),
       target_lang_arrow (dfst tt1) #(dsnd tt1) (dfst tt2) #(dsnd tt2)
    |)
  end 
  | TUnit -> (| unit, target_lang_unit |)
  | TNat -> (| int, target_lang_int |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 in
    let (| tt2, c_tt2 |) = _elab_typ t2 in
    (| either tt1 tt2, target_lang_sum tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 in
    let (| tt2, c_tt2 |) = _elab_typ t2 in
    (| (tt1 * tt2), target_lang_pair tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef t ->
    let (| tt, c_tt |) = _elab_typ t in
    (| ref tt, target_lang_ref tt #c_tt |)

let elab_typ (t:typ) : Type =
  dfst (_elab_typ t)

let elab_typ_tgt (t:typ) : target_lang (elab_typ t)=
  dsnd (_elab_typ t)



(** ** Examples **) 
let write' (#t:Type) {| c:target_lang t |} (r:ref t) (v:t) 
: IST unit
  (requires (fun h0 -> 
    shallowly_contained_low r h0 /\
    shallowly_contained_low v h0))
  (ensures (fun h0 () h1 ->
    write_post r v h0 () h1 /\
    modifies_only_label Low h0 h1 /\
    shallowly_contained_low r h1))
= let h0 = get () in
  r := v;
  let h1 = get () in
  assume (inv_low_points_to_low h1);
  assume (inv_contains_points_to_contains h1);
  ()

let _alloc (#a:Type) (#rel:preorder a) (init:a)
: IST (mref a rel) (fun h -> True) (alloc_post #a #rel init)
=
  let r = alloc init in
  let h1 = get () in
  assume (inv_low_points_to_low h1);
  assume (inv_contains_points_to_contains h1);
  r

val alloc' (#a:Type) {| c:target_lang a |} (init:a)
: IST (ref a)
  (requires (fun h0 ->
    shallowly_contained_low init h0))
  (ensures (fun h0 r h1 -> 
    fresh r h0 h1 /\ 
    modifies Set.empty h0 h1 /\
    modifies_classification Set.empty h0 h1 /\
    sel h1 r == init /\
    shallowly_contained_low r h1))
let alloc' #_ #c init = 
  let r = _alloc init in
  declassify r Low;
  let h1 = get () in
  assume (inv_low_points_to_low h1);
  assume (inv_contains_points_to_contains h1);
  r


let declassify_low' (#a:Type) {| c:target_lang a |} (r:ref a) : ST unit
  (fun h -> shallowly_contained r h /\ inv_contains_points_to_contains h)
  (fun h0 () h1 -> 
    inv_contains_points_to_contains h1 /\
    shallowly_contained_low r h1 /\
    declassify_post r Low h0 () h1)
=
  declassify r Low;
  let h1 = get () in
  assume (inv_contains_points_to_contains h1)



val ctx_update_ref_test : 
  elab_typ (TArr (TRef TNat) TUnit)
let ctx_update_ref_test (y:ref int) =
  write' y (!y + 5);
  ()

val ctx_update_multiple_refs_test : 
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit))
let ctx_update_multiple_refs_test (x:ref (ref int)) =
  gst_witness (contains_pred x);
  gst_witness (is_low_pred x);
  let cb : elab_typ (TArr (TRef TNat) TUnit) = (fun (y:ref int) -> 
    let h0 = get () in
    gst_recall (contains_pred x);
    let ix : ref int = !x in
    eliminate forall (a:Type) (c:target_lang a) (r:ref a). shallowly_contained r h0 ==>
      c.shallowly_contained (sel h0 r) h0 with (ref int) (solve) x;
    gst_recall (is_low_pred x);    
    eliminate forall (a:Type) (c:target_lang a) (r:ref a). shallowly_low r h0 ==>
      c.shallowly_low (sel h0 r) h0 with (ref int) (solve) x;
    write' ix (!ix + 1);
    let h1 = get () in
    write' x y;
    let h2 = get () in
    write' y (!y + 5);
    let h3 = get () in

    lemma_modifies_only_label_trans Low h0 h1 h2;
    lemma_modifies_only_label_trans Low h0 h2 h3;
    assert (modifies_only_label Low h0 h3); // we have an SMT Pat for this, but it does not kick in
    ()  
  ) in
  cb

val ctx_HO_test1 : 
  elab_typ (TArr (TRef (TPair (TRef TNat) (TRef TNat))) (TArr TUnit TUnit))
let ctx_HO_test1 (xs:ref ((ref int) * ref int)) =
  let (x', x'') = !xs in
  let h0 = get () in
  eliminate forall (a:Type) (c:target_lang a) (r:ref a). shallowly_contained r h0 ==>
    c.shallowly_contained (sel h0 r) h0 with ((ref int) * (ref int)) (solve) xs;
  eliminate forall (a:Type) (c:target_lang a) (r:ref a). shallowly_low r h0 ==>
    c.shallowly_low (sel h0 r) h0 with ((ref int) * (ref int)) (solve) xs;
  write' xs (x', x');
  gst_witness (is_low_pred xs);
  gst_witness (is_low_pred x');
  gst_witness (is_low_pred x'');
  (fun () -> 
    gst_recall (is_low_pred xs);
    gst_recall (is_low_pred x');
    gst_recall (is_low_pred x'');
    write' xs (x', x''))
  
val ctx_identity :
  elab_typ (TArr (TRef TNat) (TRef TNat))
let ctx_identity x = x

val ctx_HO_test2 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test2 f =
  let h0 = get () in
  let x:ref int = f () in
  let h1 = get () in
  write' x (!x + 1);
  let h2 = get () in
  assert (modifies_only_label Low h0 h2);
  ()

val ctx_swap_ref_test :
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef (TRef TNat)) TUnit))
let ctx_swap_ref_test (x:ref (ref int)) =
  gst_witness (contains_pred x);
  gst_witness (is_low_pred x);

  let cb : elab_typ (TArr (TRef (TRef TNat)) TUnit) = (fun (y: ref (ref int)) ->
    let h0 = get () in
    gst_recall (contains_pred x);
    eliminate forall (a:Type) (c:target_lang a) (r:ref a). shallowly_contained r h0 ==>
      c.shallowly_contained (sel h0 r) h0 with (ref int) (solve) x;
    gst_recall (is_low_pred x);
    eliminate forall (a:Type) (c:target_lang a) (r:ref a). shallowly_low r h0 ==>
      c.shallowly_low (sel h0 r) h0 with (ref int) (solve) x;

    let z = !x in
    let t = !y in
    write' x t;
    let h1 = get () in
    write' y z;
    let h2 = get () in
    lemma_modifies_only_label_trans Low h0 h1 h2;
    assert (modifies_only_label Low h0 h2); // we have an SMT Pat for this, but it does not kick in
    assert (modifies_classification Set.empty h0 h2);
    ()) in
  cb

val ctx_dynamic_alloc_test :
   elab_typ (TArr TUnit (TRef TNat))
let ctx_dynamic_alloc_test () = 
  let v = alloc' 0 in 
  v

val ctx_HO_test3 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test3 f =
  let x:ref int = f () in
  let y:ref int = alloc' (!x + 1) in
  ()

val ctx_returns_callback_test :
  elab_typ (TArr TUnit (TArr TUnit TUnit))
let ctx_returns_callback_test () =
  let x: ref int = alloc' 13 in
  gst_witness (contains_pred x);
  gst_witness (is_low_pred x);
  let cb : elab_typ (TArr TUnit TUnit) = (fun() ->
    gst_recall (contains_pred x);
    gst_recall (is_low_pred x);
    write' x (!x % 5)
  ) in
  cb

val ctx_HO_test4 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test4 f =
  let x:ref int = f () in
  let y:ref (ref int) = alloc' x in
  ()

val progr_sep_test: 
  #rp: ref int -> 
  ctx:(elab_typ (TArr TUnit TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      shallowly_contained rp h0 /\
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
         
let progr_sep_test #rp f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  f ()

let lemma (#a:Type) {| c:target_lang a |} (x:a) (h0 h1:lheap) : Lemma (
  h0 `lheap_rel` h1 /\ shallowly_low x h0 ==> shallowly_low x h1
) = admit ()


let lemma123 (r:ref int) (h0 h1:lheap) : Lemma
  (requires (modifies_none h0 h1 /\
            h0 `lheap_rel` h1 /\
            equal_dom h0 h1 /\
            modifies_classification (only r) h0 h1 /\
            shallowly_contained r h0 /\ 
            shallowly_contained_low r h1 /\
            inv_low_points_to_low h0))
  (ensures (inv_low_points_to_low h1)) = 
  introduce forall (a:Type) (c:target_lang a) (r:ref a). 
    shallowly_low r h1 ==> c.shallowly_low (sel h1 r) h1
  with begin
    introduce shallowly_low r h1
      ==> c.shallowly_low (sel h1 r) h1
    with _. begin
      introduce shallowly_low r h0 ==> c.shallowly_low (sel h1 r) h1 
      with _. lemma (sel h0 r) h0 h1;
      
      introduce ~(shallowly_low r h0) ==> c.shallowly_low (sel h1 r) h1
      with _. begin
        assert (shallowly_low r h1);
        let v : int = sel h1 r in 
        let c' : target_lang int = solve in
        assert (c'.shallowly_low v h1);
        assume (c.shallowly_low v h1); (* TODO: idk how to get rid of this *)
        ()
      end
    end
  end

val progr_sep_test_alloc:
  rp: ref int -> 
  ctx:(elab_typ (TArr (TRef TNat) TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      shallowly_contained rp h0 /\
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 -> True))
let progr_sep_test_alloc rp f =
  declassify_low' rp;
  let h1 = get () in
  assume (inv_low_points_to_low h1);
  let r = f rp in  
  r

val progr_sep_test_nested:
  rp: ref (ref int) -> 
  ctx:(elab_typ (TArr (TRef (TRef TNat)) TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      shallowly_contained rp h0 /\
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 -> True))
let progr_sep_test_nested rp f =
  let p : ref int = !rp in
  declassify_low' rp;
  declassify_low' p;
  let h1 = get () in
  assume (inv_low_points_to_low h1);

  // let r = alloc' (!rp) in (* <-- needed a copy here! *) 
  f rp

val progr_secret_unchanged_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr TUnit TUnit)) ->
  IST unit 
    (requires (fun h0 -> 
      shallowly_contained rp h0 /\
      label_of rp h0 == High /\
      shallowly_low rs h0))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp))
         
let progr_secret_unchanged_test rp rs ctx = 
  let secret: ref int = _alloc 0 in
  ctx ();
  let v = !secret in
  assert (v == 0);
  ()

val progr_passing_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr (TArr TUnit TUnit) TUnit)) ->
  IST unit 
    (requires (fun h0 ->
      shallowly_contained rp h0 /\
      label_of rp h0 == High /\
      shallowly_low rs h0))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context

// TODO: the callback of the program should be able to modify rp
let progr_passing_callback_test rp rs f =
  let secret: ref int = _alloc 0 in
  declassify_low' secret;
  gst_witness (contains_pred secret);
  gst_witness (is_low_pred secret);
  let cb: elab_typ (TArr TUnit TUnit) = (fun () -> 
    gst_recall (contains_pred secret);
    gst_recall (is_low_pred secret);
    write' secret (!secret + 1)) in
  let h1 = get () in
  assume (inv_low_points_to_low h1);
  f cb;
  ()

val progr_getting_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr TUnit (TArr TUnit TUnit))) ->
  IST unit 
    (requires (fun h0 ->
      shallowly_contained rp h0 /\
      label_of rp h0 == High /\
      shallowly_low rs h0))
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
  f:elab_typ (TArr t1 t2) ->
  (let tt1 = _elab_typ t1 in
   let tt2 = _elab_typ t2 in
   mk_tgt_arrow (dfst tt1) #(dsnd tt1) (dfst tt2) #(dsnd tt2))
let elab_apply_arrow t1 t2 f x = f x

let cast_TArr #t1 #t2 (f : elab_typ (TArr t1 t2)) (t:typ) (#_:squash (t == TArr t1 t2)) : elab_typ t = f

type vcontext (g:context) = 
  vx:var{Some? (g vx)} -> 
    ST (elab_typ (Some?.v (g vx)))
      (fun h -> True)
      (fun h0 x h1 -> h0 == h1 /\ shallowly_contained_low #_ #(elab_typ_tgt (Some?.v (g vx))) x h1)

let vempty : vcontext empty = fun _ -> assert false

let vextend #t (x:elab_typ t) (#g:context) (ve:vcontext g) : 
  ST (vcontext (extend t g))
    (requires (fun h0 -> shallowly_contained_low #_ #(elab_typ_tgt t) x h0))
    (ensures (fun h0 r h1 -> h0 == h1)) =
  let w = (elab_typ_tgt t).shallowly_witness x in
  fun y -> 
    if y = 0 then (w (); x) else ve (y-1)

#push-options "--split_queries always"
let rec elab_exp 
  (#g:context)
  (#e:exp) 
  (#t:typ)
  (tyj:typing g e t)
  (ve:vcontext g)
  : IST (elab_typ t) 
     (requires (pre_tgt_arrow () #target_lang_unit))
     (ensures (post_tgt_arrow () #_ #(elab_typ t) #(elab_typ_tgt t))) =
  let h0 = get () in
  match tyj with
  | TyUnit -> ()
  | TyZero -> 0
  | TySucc tyj_s -> 
    1 + (elab_exp tyj_s ve)

  | TyAllocRef #_ #_ #t tyj_e -> begin
    let v : elab_typ t = elab_exp tyj_e ve in
    let r : ref (elab_typ t) = alloc' #_ #(elab_typ_tgt t) v in
    r
  end
  | TyReadRef #_ #_ #t tyj_e -> begin
    let r : ref (elab_typ t) = elab_exp tyj_e ve in
    !r
  end
  | TyWriteRef #_ #_ #_ #t tyj_ref tyj_v -> begin
      let r : ref (elab_typ t) = elab_exp tyj_ref ve in
      let v : elab_typ t = elab_exp tyj_v ve in
      write' #_ #(elab_typ_tgt t) r v
  end

  | TyAbs tx #_ #tres tyj_body ->
    let w : mk_tgt_arrow (elab_typ tx) #(elab_typ_tgt tx) (elab_typ tres) #(elab_typ_tgt tres) = 
      (fun (x:elab_typ tx) -> 
        elab_exp tyj_body (vextend #tx x ve))
    in
    assert (t == TArr tx tres);
    cast_TArr #tx #tres w t
  | TyVar vx -> 
    let Some tx = g vx in
    let x : elab_typ tx = ve vx in
    x
  | TyApp #_ #_ #_ #tx #tres tyj_f tyj_x ->
    assert ((elab_typ t) == (elab_typ tres));
    let x : elab_typ tx = elab_exp tyj_x ve in
    let wx = (elab_typ_tgt tx).shallowly_witness x in
    let f : elab_typ (TArr tx tres) = elab_exp tyj_f ve in
    wx ();
    elab_apply_arrow tx tres f x

  | TyInl #_ #_ #t1 #t2 tyj_1 ->
    let v1 : elab_typ t1 = elab_exp tyj_1 ve in
    Inl #_ #(elab_typ t2) v1
  | TyInr #_ #_ #t1 #t2 tyj_2 ->
    let v2 : elab_typ t2 = elab_exp tyj_2 ve in
    Inr #(elab_typ t1) v2
  | TyCaseSum #_ #_ #_ #_ #tl #tr #tres tyj_c tyj_l tyj_r -> begin
    let vc : either (elab_typ tl) (elab_typ tr) = elab_exp tyj_c ve in
    match vc with 
    | Inl x -> 
      let wx = (elab_typ_tgt tl).shallowly_witness x in
      let f : elab_typ (TArr tl tres) = elab_exp tyj_l ve in
      wx ();
      elab_apply_arrow tl tres f x
    | Inr y ->
      let wy = (elab_typ_tgt tr).shallowly_witness y in
      let f : elab_typ (TArr tr tres) = elab_exp tyj_r ve in
      wy ();
      elab_apply_arrow tr tres f y
  end

  | TyFst #_ #_ #tf #ts tyj_e ->
    let v = elab_exp tyj_e ve in
    fst #(elab_typ tf) #(elab_typ ts) v
  | TySnd #_ #_ #tf #ts tyj_e ->
    let v = elab_exp tyj_e ve in
    snd #(elab_typ tf) #(elab_typ ts) v
  | TyPair #_ #_ #_ #tf #ts tyj_f tyj_s->
    let vf : elab_typ tf = elab_exp tyj_f ve in
    let wvf = (elab_typ_tgt tf).shallowly_witness vf in
    let vs : elab_typ ts = elab_exp tyj_s ve in
    wvf ();
    (vf, vs)
#pop-options
