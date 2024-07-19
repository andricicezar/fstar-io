module TargetLang

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ref

let (@) = FStar.List.Tot.append
let (⊆) = Set.subset
let (⊎) = Set.union
let (∩) = Set.intersect
let subtract (#a:eqtype) (s1:Set.set a) (s2:Set.set a) : Set.set a =
  Set.intersect s1 (Set.complement s2)

type tfootprint = Set.set nat

(** target_lang is a shallow embedding of STLC **)
class target_lang (t:Type) = {
  footprint : t -> heap -> (erased tfootprint); // TODO: if there is a cycle, this would diverge
                     // I suppose it is not a problem because we are in GTot?

  footprint_after_write : t -> heap -> #a:Type -> ref a -> tfootprint -> erased tfootprint;

  dcontains : t -> heap -> Type0;

  footprint_after_write_law : v:t -> h0:heap -> #a:Type -> r:(ref a) -> fp_r:tfootprint ->
    Lemma (
      footprint_after_write v h0 r fp_r ⊆ footprint v h0 ⊎ fp_r);
}

instance target_lang_unit : target_lang unit = {
  footprint = (fun _ _ -> Set.empty);
  footprint_after_write = (fun _ _ _ _ -> Set.empty);
  footprint_after_write_law = (fun _ _ _ _ -> ());
  dcontains = (fun _ _ -> True);
}

instance target_lang_int : target_lang int = {
  footprint = (fun _ _ -> Set.empty);
  footprint_after_write = (fun _ _ _ _ -> Set.empty);
  footprint_after_write_law = (fun _ _ _ _ -> ());
  dcontains = (fun _ _ -> True);
}

instance target_lang_pair (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (t1 * t2) = {
  footprint = (fun (x1, x2) h -> 
    (c1.footprint x1 h) ⊎ (c2.footprint x2 h));
  footprint_after_write = (fun (x1, x2) h r fp_r -> 
    (c1.footprint_after_write x1 h r fp_r) ⊎ (c2.footprint_after_write x2 h r fp_r));
  footprint_after_write_law = (fun (x1,x2) h r fp_r ->
    c1.footprint_after_write_law x1 h r fp_r;
    c2.footprint_after_write_law x2 h r fp_r
  );
  dcontains = (fun (x1, x2) h -> c1.dcontains x1 h /\ c2.dcontains x2 h);
}

instance target_lang_sum (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (either t1 t2) = {
  footprint = (fun x h -> 
     match x with
     | Inl x1 -> c1.footprint x1 h
     | Inr x2 -> c2.footprint x2 h);
  footprint_after_write = (fun x h r fp_r ->
    match x with
    | Inl x1 -> c1.footprint_after_write x1 h r fp_r
    | Inr x2 -> c2.footprint_after_write x2 h r fp_r);
  footprint_after_write_law = (fun x h r fp_r ->
    match x with
    | Inl x1 -> c1.footprint_after_write_law x1 h r fp_r
    | Inr x2 -> c2.footprint_after_write_law x2 h r fp_r
  );
  dcontains = (fun x h ->
    match x with
    | Inl x1 -> c1.dcontains x1 h
    | Inr x2 -> c2.dcontains x2 h);
}

instance target_lang_ref (t:Type) {| c:target_lang t |} : target_lang (ref t) = {
  footprint = (fun x h -> 
    !{x} ⊎ (c.footprint (sel h x) h)); // <--- following x in h
  
  footprint_after_write = (fun x h r fp_r ->
    if addr_of x = addr_of r then !{x} ⊎ fp_r
    else !{x} ⊎ c.footprint_after_write (sel h x) h r fp_r);
  
  footprint_after_write_law = (fun v h r fp_r ->
    c.footprint_after_write_law (sel h v) h r fp_r);
  
  dcontains = (fun x h -> h `contains` x /\ c.dcontains (sel h x) h);
}

let pre_tgt_arrow
  (#tscope:Type) (scope:tscope) {| tgts:target_lang tscope |} 
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (h0:heap) =
  dcontains (scope, x) h0

let post_tgt_arrow
  (#tscope:Type) (scope:tscope) {| tgts:target_lang tscope |} 
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (#t2:t1 -> Type) {| tgtr : (x:t1 -> target_lang (t2 x)) |}
  (h0:heap) (r:t2 x) (hf:heap) =
  let fp0 = tgts.footprint scope h0 in
  let fpf = tgts.footprint scope hf in
  modifies fp0 h0 hf /\ 
  equal_dom h0 hf /\ 
  ((tgtr x).footprint r hf) ⊆ fp0 /\ 
  fpf ⊆ fp0 /\ 
  tgts.dcontains scope hf /\ 
  ((tgtr x).dcontains r hf)

unfold let mk_tgt_arrow  
  (t1:Type)
  {| tgt_t1: target_lang t1 |}
  (t2:t1 -> Type) 
  (#tscope:Type)
  (scope:tscope)
  {| tgt_scope:target_lang tscope |}
  {| c2 : (x:t1 -> target_lang (t2 x)) |}
= x:t1 -> ST (t2 x) 
    (requires (pre_tgt_arrow scope #tgt_scope x #tgt_t1))
    (ensures (post_tgt_arrow scope #tgt_scope x #tgt_t1 #t2 #c2))

instance target_lang_arrow 
  (t1:Type)
  {| target_lang t1 |}
  (t2:t1 -> Type) 
  (#tscope:Type)
  (scope:tscope)
  {| target_lang tscope |}
  {| (x:t1 -> target_lang (t2 x)) |}
  : target_lang (mk_tgt_arrow t1 t2 scope) = {
    footprint = (fun _ _ -> Set.empty); // <-- TODO: why no footprint for functions?
    footprint_after_write = (fun _ _ _ _ -> Set.empty);
    footprint_after_write_law = (fun _ _ _ _ -> ());
    dcontains = (fun _ _ -> True);
  }


(** ** Lemmas on target lang **)
class target_lang_rels (a:Type) {| target_lang a |} (b:Type) {| target_lang b |} = {
  footprint_footprint_after_write : r:ref a -> v:b -> h0:heap -> h1:heap -> fp_r:tfootprint -> 
    Lemma (requires (
      dcontains r h0 /\
      dcontains v h0 /\
      equal_dom h0 h1 /\
      modifies !{r} h0 h1 /\
      footprint r h1 ⊆ fp_r
    ))
    (ensures (footprint v h1 ⊆ footprint_after_write v h0 r fp_r))
}

instance target_lang_rels_unit (a:Type) {| target_lang a |} : target_lang_rels a unit = {
  footprint_footprint_after_write = (fun _ _ _ _ _ -> ())
}

instance target_lang_rels_int (a:Type) {| target_lang a |} : target_lang_rels a int = {
  footprint_footprint_after_write = (fun _ _ _ _ _ -> ())
}

instance target_lang_rels_pair
  (a:Type) {| target_lang a |}
  (b1:Type) {| target_lang b1 |}
  (b2:Type) {| target_lang b2 |} 
  {| target_lang_rels a b1 |}
  {| target_lang_rels a b2 |}
  : target_lang_rels a (b1 * b2) = {
  footprint_footprint_after_write = (fun r (v1, v2) h0 h1 fp_r ->
    footprint_footprint_after_write r v1 h0 h1 fp_r;
    footprint_footprint_after_write r v2 h0 h1 fp_r
  )
}

instance target_lang_rels_sums
  (a:Type) {| target_lang a |}
  (b1:Type) {| target_lang b1 |}
  (b2:Type) {| target_lang b2 |} 
  {| target_lang_rels a b1 |}
  {| target_lang_rels a b2 |}
  : target_lang_rels a (either b1 b2) = {
  footprint_footprint_after_write = (fun r v h0 h1 fp_r ->
    match v with
    | Inl v1 -> footprint_footprint_after_write r v1 h0 h1 fp_r
    | Inr v2 -> footprint_footprint_after_write r v2 h0 h1 fp_r
  )
}

instance target_lang_rels_refs (a:Type) (b:Type) (#_:squash (a =!= b)) {| target_lang a |} {| target_lang b |} {| c1:target_lang_rels a b |}  : target_lang_rels a (ref b) = {
  footprint_footprint_after_write = (fun r (v:ref b) h0 h1 fp_r ->
    lemma_distinct_addrs_distinct_types h0 r v;
    c1.footprint_footprint_after_write r (sel h0 v) h0 h1 fp_r;
    assert ((!{v} ⊎ (footprint (sel h1 v) h1)) ⊆ !{v} ⊎ footprint_after_write (sel h0 v) h0 r fp_r);
    lemma_modifies_and_equal_dom_sel_diff_addr !{r} h0 h1 v;
    assert (sel h0 v == sel h1 v);
    assert (footprint v h1 ⊆ footprint_after_write v h0 r fp_r)
  )
}

instance target_lang_rels_refs' (a:Type) {| target_lang a |} {| c1:target_lang_rels a a |} : target_lang_rels a (ref a) = {
  footprint_footprint_after_write = (fun r (v:ref a) h0 h1 fp_r ->
    if compare_addrs v r then begin
      lemma_sel_same_addr h0 v r;
      assert ((!{v} ⊎ (footprint (sel h1 v) h1)) ⊆ (!{v} ⊎ fp_r));
      assert (footprint r h1 ⊆ fp_r);
      assert (footprint v h1 ⊆ footprint_after_write v h0 r fp_r)
    end else begin
      c1.footprint_footprint_after_write r (sel h0 v) h0 h1 fp_r;
      assert ((!{v} ⊎ (footprint (sel h1 v) h1)) ⊆ !{v} ⊎ footprint_after_write (sel h0 v) h0 r fp_r);
      lemma_modifies_and_equal_dom_sel_diff_addr !{r} h0 h1 v;
      assert (sel h0 v == sel h1 v);
      assert (footprint v h1 ⊆ footprint_after_write v h0 r fp_r)
    end
  )
}

instance target_lang_rels_arrow
  (a:Type) {| target_lang a |}
  (t1:Type) {| target_lang t1 |}
  (t2:t1 -> Type) {| (x:t1 -> target_lang (t2 x)) |}
  (#tscope:Type)
  (scope:tscope)
  {| target_lang tscope |} :
  target_lang_rels a (mk_tgt_arrow t1 t2 scope) = {
    footprint_footprint_after_write = (fun _ _ _ _ _ -> ())
  }

let stable_footprint_v (#t:Type) {| target_lang t |} (* {| target_lang_rels t t |} *) (r:ref t) (v:t) (h0 h1:heap) :
  Lemma
    (requires (
      dcontains r h0 /\
      dcontains v h0 /\
      equal_dom h0 h1 /\

      modifies !{r} h0 h1 /\
      sel h1 r == v 
    ))
    (ensures (footprint v h1 ⊆ footprint v h0))
= // assume (!{r} `Set.disjoint` footprint v h0);
  assume (!{r} ⊆ footprint v h0); // TODO: regression here after removing law1.
  let fpr = !{r} ⊎ (footprint v h0) in
  footprint_after_write_law v h0 r fpr;
  assert (footprint_after_write v h0 r fpr ⊆ fpr ⊎ fpr);
  assert (footprint_after_write v h0 r fpr ⊆ fpr);
  assume (footprint r h1 ⊆ fpr);
  admit ();
  // footprint_footprint_after_write r v h0 h1 fpr;
  assert (footprint v h1 ⊆ footprint_after_write v h0 r fpr)

let footprint_r_after_write 
  (#tscope:Type) {| target_lang tscope |} (scope:tscope)
  (#t:Type) {| target_lang t |} (* {| target_lang_rels t tscope |}*)
  (r:ref t) (v:t)
  (fp:Set.set nat)
  (h0 h1:heap)
  : Lemma
  (requires (
    equal_dom h0 h1 /\
    dcontains scope h0 /\
    dcontains r h0 /\
    modifies !{r} h0 h1 /\
    sel h1 r == v /\
    footprint scope h0 ⊆ fp /\

    !{r} ⊆ fp /\
    footprint v h0 ⊆ fp
  ))
  (ensures (footprint scope h1 ⊆ (fp ⊎ footprint r h1)))
= footprint_after_write_law scope h0 r (footprint r h1);
  assert (footprint_after_write scope h0 r (footprint r h1) ⊆ footprint scope h0 ⊎ footprint r h1);
  assert (footprint_after_write scope h0 r (footprint r h1) ⊆ fp ⊎ footprint r h1);
  admit ();
  // footprint_footprint_after_write r scope h0 h1 (footprint r h1);
  assert (footprint scope h1 ⊆ footprint_after_write scope h0 r (footprint r h1))

let equal_dom_preserves_dcontains (#t:Type) {| target_lang t |} (x:t) (h0 h1:heap) : Lemma
  (requires (equal_dom h0 h1 /\ dcontains x h0))
  (ensures (dcontains x h1)) = admit ()





open STLC

(** *** Elaboration of types to F* *)
let rec _elab_typ (t:typ) (#tscope:Type) (scope:tscope) {| c_scope:target_lang tscope |} : tt:Type & target_lang tt =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = _elab_typ t1 #tscope scope #c_scope in
    let tt2 (x:dfst tt1) = _elab_typ t2 #(tscope * dfst tt1) (scope, x) #(target_lang_pair tscope (dfst tt1) #c_scope #(dsnd tt1)) in
    (| mk_tgt_arrow      (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) scope #c_scope #(fun x -> dsnd (tt2 x)),
       target_lang_arrow (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) scope #c_scope #(fun x -> dsnd (tt2 x))
    |)
  end 
  | TUnit -> (| unit, target_lang_unit |)
  | TNat -> (| int, target_lang_int |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 scope #c_scope in
    let (| tt2, c_tt2 |) = _elab_typ t2 scope #c_scope in
    (| either tt1 tt2, target_lang_sum tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 scope #c_scope in
    let (| tt2, c_tt2 |) = _elab_typ t2 scope #c_scope in
    (| (tt1 * tt2), target_lang_pair tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef t ->
    let (| tt, c_tt |) = _elab_typ t scope #c_scope in
    (| ref tt, target_lang_ref tt #c_tt |)

let elab_typ (t:typ) (#tscope:Type) (scope:tscope) {| c_scope : target_lang tscope |} : Type =
  dfst (_elab_typ t scope #c_scope)

let elab_typ_tgt (t:typ) (#tscope:Type) (scope:tscope) {| c_scope : target_lang tscope |} : target_lang (elab_typ t scope)=
  dsnd (_elab_typ t scope #c_scope)

let elab_typ' (t:typ) (#tscope:typ) (scope:dfst (_elab_typ tscope ())) : Type =
  let (| ty, c_scope |) = _elab_typ tscope () in
  elab_typ t #ty scope #c_scope

let elab_typ_tgt' (t:typ) (#tscope:typ) (scope:dfst (_elab_typ tscope ())) : target_lang (elab_typ' t scope)=
  let (| ty, c_scope |) = _elab_typ tscope () in
  elab_typ_tgt t #ty scope #c_scope

// val elab_typ_test1 : elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit))
// let elab_typ_test1 (x:ref (ref int)) (y:ref int) =
//   let ix = !x in
//   ix := !ix + 1;
//   x := y;
//   y := !y + 5;
//   ()

// val elab_typ_test2 : elab_typ (TArr TUnit (TRef TNat))
// let elab_typ_test2 () = alloc 0
  
// val elab_typ_test2' : elab_typ (TArr (TRef TNat) (TRef TNat))
// let elab_typ_test2' x = x

// val elab_typ_test3 : elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
// let elab_typ_test3 f =
//   let x:ref int = f () in
//   x := !x + 1;
//   ()

val sep : ref int -> ref (ref int) -> heap -> Type0
let sep rp rs h =
  let fp_rs = !{rs} ⊎ !{sel h rs} in 
  let fp_rp = !{rp} in
  (h `contains` rs /\ h `contains` (sel h rs)) /\
  (h `contains` rp) /\
  Set.disjoint fp_rp fp_rs

val progr: 
  rp: ref int -> 
  rs: ref (ref int) -> 
  ctx:(elab_typ (TArr TUnit TUnit) rs) -> 
  ST int (requires (fun h0 -> sep rp rs h0))
      (ensures (fun _ _ h1 -> sep rp rs h1))
         
let progr rp rs f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  f ();
  !rp


(** *** Elaboration of expressions to F* *)
type vcontext (g:context) = x:var{Some? (g x)} -> elab_typ (Some?.v (g x)) ()

let vempty : vcontext empty = fun _ -> assert false

let vextend #t (x:elab_typ t ()) (#g:context) (ve:vcontext g) : vcontext (extend t g) =
  fun y -> if y = 0 then x else ve (y-1)

//let cast_TArr #t1 #t2 (h : (elab_typ t1 -> Tot (elab_typ t2))) : elab_typ (TArr t1 t2) = h

// let rec fnrec (#a:Type) (n:nat) (acc:a) (iter:a -> a): Tot a =
//   if n = 0 then acc else fnrec (n-1) (iter acc) iter


val elab_apply_arrow :
  t1:typ ->
  t2:typ ->
  #tscope:Type ->
  scope:tscope ->
  {| c_scope: target_lang tscope |} -> 
  f:elab_typ (TArr t1 t2) scope #c_scope ->
  (let tt1 = _elab_typ t1 scope #c_scope in
   let tt2 (x:(dfst tt1)) = _elab_typ t2 (scope, x) #(target_lang_pair tscope (dfst tt1) #c_scope #(dsnd tt1)) in
   mk_tgt_arrow (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) scope #c_scope #(fun x -> dsnd (tt2 x)))
let elab_apply_arrow t1 t2 #tscope scope #c_scope f x = f x

let rec elab_exp 
  (#g:context)
  (#e:exp) 
  (#t:typ)
  (tyj:typing g e t)
  (ve:vcontext g)
  (#tscope:typ)
  (scope:elab_typ tscope ())
  : ST (elab_typ' t scope) 
     (requires (pre_tgt_arrow scope #(elab_typ_tgt tscope ()) ()))
     (ensures (post_tgt_arrow scope #(elab_typ_tgt tscope ()) () #_ #(fun _ -> elab_typ' t scope) #(fun _ -> elab_typ_tgt' t scope)))
     (decreases e) =
  let tgt_scope = elab_typ_tgt tscope () in
  let h0 = gst_get () in
  let fp0 = tgt_scope.footprint scope h0 in
  match tyj with
  | TyUnit -> ()
  | TyZero -> 0
  | TyReadRef #_ #_ #t tyj_e -> begin
    let r : ref (elab_typ' t scope) = elab_exp tyj_e ve scope in
    read r
  end
  | TyWriteRef #_ #_ #_ #t tyj_ref tyj_v -> begin
    let r : ref (elab_typ' t scope) = elab_exp tyj_ref ve scope in // <-- this is effectful and modifies fp
      let h1 = gst_get () in
      let fp1 = tgt_scope.footprint scope h1 in
      let tgt_r = elab_typ_tgt' (TRef t) scope in
      
      assert (tgt_r.dcontains r h1);
      
    let v : elab_typ' t scope = elab_exp tyj_v ve scope in // this is effectul and modifies fp
      let h2 = gst_get () in
      let fp2 = tgt_scope.footprint scope h2 in
      let tgt_v = elab_typ_tgt' t scope in

    write r v;
      let h3 = gst_get () in
      let fp3 = tgt_scope.footprint scope h3 in
      let fp_r = tgt_r.footprint r in
      let fp_v = tgt_v.footprint v in
      assert (tgt_v.footprint v h2 ⊆ fp1);
      
      // assert (fp2 ⊆ fp1 ⊆ fp0);
      assert (tgt_r.footprint r h1 ⊆ fp0);
      equal_dom_preserves_dcontains r h1 h2;
      equal_dom_preserves_dcontains scope h1 h2;
      footprint_r_after_write scope r v fp0 h2 h3;
      assert (fp3 ⊆ fp0 ⊎ fp_r h3);
      // assert ((fp2 `subtract` fp_r h2) ⊆ fp0);
      assert (fp_r h3 `Set.equal` !{r} ⊎ fp_v h3);
      stable_footprint_v r v h2 h3;
      assert (fp_v h3 ⊆ fp_v h2);
      assert (!{r} ⊆ fp0 /\ fp_v h2 ⊆ fp0 /\ fp_r h3 ⊆ fp0);

      // post
      assert (fp3 ⊆ fp0);
      equal_dom_preserves_dcontains scope h2 h3;
      assert (tgt_scope.dcontains scope h3);
    ()
  end
  | _ -> admit ()

  // | TyAllocRef #_ #_ #t tyj_e -> begin
  //   let v : elab_typ t = elab_exp tyj_e ve scope #sfp in
  //   let r = alloc v in
  //   r
  // end

  (**
  | TySucc hs ->
    1 + (elab_exp hs ve)
  | TyNRec h1 h2 h3 -> admit ()
    // let v1 = elab_exp h1 ve in
    // let v2 : elab_typ t = elab_exp h2 ve in
    // let v3 : elab_typ (TArr t t) = elab_exp h3 ve in
    // fnrec #(elab_typ t) v1 v2 v3
  | TyInl #_ #_ #t1 #t2 h1 ->
    let v = elab_exp h1 ve in
    Inl #(elab_typ t1) #(elab_typ t2) v
  | TyInr #_ #_ #t1 #t2 h1 ->
    let v = elab_exp h1 ve in
    Inr #(elab_typ t1) #(elab_typ t2) v
  | TyCaseSum h1 h2 h3 ->
    let v1 = elab_exp h1 ve in
    let v2 = elab_exp h2 ve in
    let v3 = elab_exp h3 ve in
    (match v1 with | Inl x -> v2 x | Inr y -> v3 y)
  | TyCaseNat h1 h2 h3 ->
    let v1 = elab_exp h1 ve in
    let v2 = elab_exp h2 ve in
    let v3 = elab_exp h3 ve in
    (match v1 with | 0 -> v2 () | _ -> v3 (v1-1))
  | TyVar x -> ve x
  | TyAbs t1 #_ #t2 h1 -> admit ()
    // assert (t == TArr t1 t2);
    // let w : elab_typ t1 -> Tot (elab_typ t2) =
    // (fun x -> elab_exp h1 (vextend x ve)) in
    // cast_TArr w
  | TyApp #_ #_ #_ #t1 #t2 h1 h2 ->
    assert ((elab_typ t) == (elab_typ t2));
    (* TODO: Should we change the order here, first evaluate argument? *)
    let v1 : elab_typ (TArr t1 t2) = elab_exp h1 ve in
    let v2 : elab_typ t1 = elab_exp h2 ve in
    v1 v2
  | TyFst #_ #_ #t1 #t2 h1 ->
    let v = elab_exp h1 ve in
    fst #(elab_typ t1) #(elab_typ t2) v
  | TySnd #_ #_ #t1 #t2 h1 ->
    let v = elab_exp h1 ve in
    snd #(elab_typ t1) #(elab_typ t2) v
  | TyPair h1 h2 ->
    let v1 = elab_exp h1 ve in
    let v2 = elab_exp h2 ve in
    (v1, v2)
**)
