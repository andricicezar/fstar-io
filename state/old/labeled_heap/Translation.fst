module Translation

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Universe 

open Labeled.Monotonic.Heap
open Labeled.MST
open Witnessable
open TargetLang
open STLC

(** ** Elaboration of expressions to F* *)
val elab_apply_arrow :
  t1:typ ->
  t2:typ ->
  f:elab_typ (TArr t1 t2) ->
  (let tt1 = _elab_typ t1 in
   let tt2 = _elab_typ t2 in
   mk_tgt_arrow (dfst tt1) #(dsnd tt1) (dfst tt2) #(dsnd tt2))
let elab_apply_arrow t1 t2 f x = f x

let cast_TArr (#t1 #t2:typ) (f : elab_typ (TArr t1 t2)) (t:typ) (#_:squash (t == TArr t1 t2)) : elab_typ t = f

type vcontext (g:context) = 
  vx:var{Some? (g vx)} -> elab_typ (Some?.v (g vx))

let vempty : vcontext empty = fun _ -> assert false

let vextend #t (x:elab_typ t) (#g:context) (ve:vcontext g) : vcontext (extend t g) =
  fun y -> if y = 0 then x else ve (y-1)

let all_refs_contained_and_low (#g:context) (ve:vcontext g) (h:lheap) : Type0 =
  forall vx. Some? (g vx) ==> shallowly_contained_low (ve vx) #(elab_typ_tc (Some?.v (g vx))) h

let stable_refs_contained_and_low (#g:context) (ve:vcontext g) : Lemma (stable (all_refs_contained_and_low ve)) [SMTPat (all_refs_contained_and_low ve)] = 
  introduce forall h0 h1. (h0 `lheap_rel` h1 /\ all_refs_contained_and_low ve h0) ==> all_refs_contained_and_low ve h1 with begin
    introduce (h0 `lheap_rel` h1 /\ all_refs_contained_and_low ve h0) ==> all_refs_contained_and_low ve h1 with _. begin      
      introduce forall vx. Some? (g vx) ==> shallowly_contained_low (ve vx) #(elab_typ_tc (Some?.v (g vx))) h1 with begin
        introduce Some? (g vx) ==> shallowly_contained_low (ve vx) #(elab_typ_tc (Some?.v (g vx))) h1 with hyp0. begin
          eliminate forall vx. Some? (g vx) ==> shallowly_contained_low (ve vx) #(elab_typ_tc (Some?.v (g vx))) h0 with vx;
          eliminate Some? (g vx) ==> shallowly_contained_low (ve vx) #(elab_typ_tc (Some?.v (g vx))) h0 with hyp0;
          (elab_typ_tc (Some?.v (g vx))).satisfy_monotonic (ve vx) contains_pred h0 h1;
          (elab_typ_tc (Some?.v (g vx))).satisfy_monotonic (ve vx) is_low_pred h0 h1
        end
      end
    end  
  end

let rec downgrade_typ (t:typ0) (x:elab_typ t) : elab_typ0 t =
  match t with
  | TSum t1 t2 -> begin
    let x : either (elab_typ t1) (elab_typ t2) = x in
    (match x with
    | Inl v -> Inl (downgrade_typ t1 v)
    | Inr v -> Inr (downgrade_typ t2 v)) <: either (elab_typ0 t1) (elab_typ0 t2)
    end
  | TPair t1 t2 -> begin
    let x : elab_typ t1 * elab_typ t2 = x in
    let (v1, v2) = x in
    (downgrade_typ t1 v1, downgrade_typ t2 v2)
  end
  | _ -> downgrade_val x

let rec raise_typ (t:typ0) (x:elab_typ0 t) : elab_typ t =
  match t with
  | TSum t1 t2 -> begin
    let x : either (elab_typ0 t1) (elab_typ0 t2) = x in
    (match x with
    | Inl v -> Inl (raise_typ t1 v)
    | Inr v -> Inr (raise_typ t2 v)) <: either (elab_typ t1) (elab_typ t2)
    end
  | TPair t1 t2 -> begin
    let x : elab_typ0 t1 * elab_typ0 t2 = x in
    let (v1, v2) = x in
    (raise_typ t1 v1, raise_typ t2 v2)
  end
  | _ -> raise_val x

let rec lemma_downgrade_typ (t:typ0) (x:elab_typ t) :
  ST unit
    (requires (fun h -> shallowly_contained_low x #(elab_typ_tc t) h))
    (ensures (fun h0 r h1 -> h0 == h1 /\ shallowly_contained_low (downgrade_typ t x) #(elab_typ0_tc t) h1)) =
  match t with
  | TSum t1 t2 -> begin
    let x : either (elab_typ t1) (elab_typ t2) = x in
    (match x with
    | Inl v -> lemma_downgrade_typ t1 v
    | Inr v -> lemma_downgrade_typ t2 v)
  end
  | TPair t1 t2 -> begin
    let x : elab_typ t1 * elab_typ t2 = x in
    let (v1, v2) = x in
    lemma_downgrade_typ t1 v1;
    lemma_downgrade_typ t2 v2
  end
  | _ -> ()

let rec lemma_raise_typ (t:typ0) (x:elab_typ0 t) :
  ST unit
    (requires (fun h -> shallowly_contained_low x #(elab_typ0_tc t) h))
    (ensures (fun h0 r h1 -> h0 == h1 /\ shallowly_contained_low (raise_typ t x) #(elab_typ_tc t) h1)) =
  match t with
  | TSum t1 t2 -> begin
    let x : either (elab_typ0 t1) (elab_typ0 t2) = x in
    (match x with
    | Inl v -> lemma_raise_typ t1 v
    | Inr v -> lemma_raise_typ t2 v)
  end
  | TPair t1 t2 -> begin
    let x : elab_typ0 t1 * elab_typ0 t2 = x in
    let (v1, v2) = x in
    lemma_raise_typ t1 v1;
    lemma_raise_typ t2 v2
  end
  | _ -> ()

let downgrade (#t:typ0) (x:elab_typ t) :
  ST (elab_typ0 t)
    (requires (fun h -> shallowly_contained_low x #(elab_typ_tc t) h))
    (ensures (fun h0 r h1 -> h0 == h1 /\ r == downgrade_typ t x /\ shallowly_contained_low r #(elab_typ0_tc t) h1)) =
    lemma_downgrade_typ t x;
    downgrade_typ t x

let raise (#t:typ0) (x:elab_typ0 t) :
  ST (elab_typ t)
    (requires (fun h -> shallowly_contained_low x #(elab_typ0_tc t) h))
    (ensures (fun h0 r h1 -> h0 == h1 /\ r == raise_typ t x /\ shallowly_contained_low r #(elab_typ_tc t) h1)) =
    lemma_raise_typ t x;
    raise_typ t x

#push-options "--split_queries always"
let rec elab_exp 
  (#g:context)
  (#e:exp) 
  (#t:typ)
  (tyj:typing g e t)
  (ve:vcontext g)
  : IST (elab_typ t) 
      (requires (fun h0 -> 
        all_refs_contained_and_low ve h0 /\
        pre_tgt_arrow #unit #witnessable_unit () h0))
      (ensures (fun h0 r h1 ->
        post_tgt_arrow #_ #_ #(elab_typ t) #(elab_typ_tc t) () h0 r h1))
      =
  let h0 = get () in
  mst_witness (all_refs_contained_and_low ve);
  match tyj with
  | TyUnit -> raise_val ()
  | TyZero -> raise_val 0
  | TySucc tyj_s -> 
    raise_val (1 + (downgrade_val (elab_exp tyj_s ve)))

  | TyAllocRef #_ #_ #t tyj_e -> begin
    let v : elab_typ0 t = downgrade (elab_exp tyj_e ve) in
    let r : ref (elab_typ0 t) = elab_alloc #t v in
    raise_val r
  end
  | TyReadRef #_ #_ #t tyj_e -> begin
    let r' : ref (elab_typ0 t) = downgrade (elab_exp tyj_e ve) in
    raise #t (!r')
  end
  | TyWriteRef #_ #_ #_ #t tyj_ref tyj_v -> begin
    let r : ref (elab_typ0 t) = downgrade (elab_exp tyj_ref ve) in
    let v : elab_typ0 t = downgrade (elab_exp tyj_v ve) in
    elab_write #t r v;
    raise_val ()
  end

  | TyAbs tx #_ #tres tyj_body ->
    let w : mk_tgt_arrow (elab_typ tx) #(elab_typ_tc tx) (elab_typ tres) #(elab_typ_tc tres) = 
      (fun (x:elab_typ tx) -> 
        mst_recall (all_refs_contained_and_low ve);
        let ve' = vextend #tx x ve in
        elab_exp tyj_body ve')
    in
    assert (t == TArr tx tres);
    cast_TArr #tx #tres w t
  | TyVar vx -> 
    let Some tx = g vx in
    let x : elab_typ tx = ve vx in
    x
  | TyApp #_ #_ #_ #tx #tres tyj_f tyj_x ->
    assert ((elab_typ t) == (elab_typ tres));
    let f : elab_typ (TArr tx tres) = elab_exp tyj_f ve in
    let x : elab_typ tx = elab_exp tyj_x ve in
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
      let wx1 = (elab_typ_tc tl).witness x contains_pred in
      let wx2 = (elab_typ_tc tl).witness x is_low_pred in
      let f : elab_typ (TArr tl tres) = elab_exp tyj_l ve in
      wx1 (); wx2 ();
      elab_apply_arrow tl tres f x
    | Inr y ->
      let wy1 = (elab_typ_tc tr).witness y contains_pred in
      let wy2 = (elab_typ_tc tr).witness y is_low_pred in
      let f : elab_typ (TArr tr tres) = elab_exp tyj_r ve in
      wy1 (); wy2 ();
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
    let wvf1 = (elab_typ_tc tf).witness vf contains_pred in
    let wvf2 = (elab_typ_tc tf).witness vf is_low_pred in
    let vs : elab_typ ts = elab_exp tyj_s ve in
    wvf1 (); wvf2 ();
    (vf, vs)
#pop-options