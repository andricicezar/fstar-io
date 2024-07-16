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

  // footprint_after_write_law3 : v:t -> h0:heap -> h1:heap -> #a:Type -> r:(ref a) -> fp_r:erased tfootprint ->
  //   Lemma 
  //     (requires (
  //       modifies !{r} h0 h1 /\ 
  //       // footprint r h1 ⊆ fp_r /\
  //       dcontains v h0 /\ 
  //       h0 `contains` r))
  //     (ensures (footprint v h1 ⊆ footprint_after_write v h0 r fp_r));

  law1 : (s: Set.set nat) -> (v:t) -> h0:heap -> h1:heap -> 
    Lemma
      (requires (
        modifies s h0 h1 /\ 
        (s `Set.disjoint` footprint v h0) /\ 
        dcontains v h0))
      (ensures footprint v h0 `Set.equal` footprint v h1);
}

instance target_lang_unit : target_lang unit = {
  footprint = (fun _ _ -> Set.empty);
  footprint_after_write = (fun _ _ _ _ -> Set.empty);
  footprint_after_write_law = (fun _ _ _ _ -> ());
  dcontains = (fun _ _ -> True);
  law1 = (fun _ _ _ _ -> ());
}

instance target_lang_int : target_lang int = {
  footprint = (fun _ _ -> Set.empty);
  footprint_after_write = (fun _ _ _ _ -> Set.empty);
  footprint_after_write_law = (fun _ _ _ _ -> ());
  dcontains = (fun _ _ -> True);
  law1 = (fun _ _ _ _ -> ());
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
  law1 = (fun s (x1, x2) h0 h1 -> 
    c1.law1 s x1 h0 h1;
    c2.law1 s x2 h0 h1
  );
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
  law1 = (fun s x h0 h1 ->
    match x with
    | Inl x1 -> c1.law1 s x1 h0 h1
    | Inr x2 -> c2.law1 s x2 h0 h1
  );
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
  law1 = (fun s v h0 h1 -> c.law1 s (sel h0 v) h0 h1);
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

let mk_tgt_arrow  
  (t1:Type)
  {| target_lang t1 |}
  (t2:t1 -> Type) 
  (#tscope:Type)
  (scope:tscope)
  {| sfp:target_lang tscope |}
  {| c2 : (x:t1 -> target_lang (t2 x)) |}
= x:t1 -> ST (t2 x) 
    (requires (pre_tgt_arrow scope x))
    (ensures (post_tgt_arrow scope x))

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
    law1 = (fun _ _ _ _ -> ());
  }

open STLC

(** *** Elaboration of types to F* *)
let rec elab_typ' (t:typ) (#tscope:Type) (scope:tscope) {| c_scope:target_lang tscope |} : tt:Type & target_lang tt =
  match t with
  | TArr t1 t2 -> begin
    let (| tt1, c_tt1 |) = elab_typ' t1 scope #c_scope in
    let tt2 (x:tt1) = elab_typ' t2 (scope, x) #(target_lang_pair tscope tt1 #c_scope #c_tt1) in
    (| mk_tgt_arrow      tt1 #c_tt1 (fun x -> dfst (tt2 x)) scope #c_scope #(fun x -> dsnd (tt2 x)),
       target_lang_arrow tt1 #c_tt1 (fun x -> dfst (tt2 x)) scope #c_scope #(fun x -> dsnd (tt2 x))
    |)
  end 
  | TUnit -> (| unit, target_lang_unit |)
  | TNat -> (| int, target_lang_int |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = elab_typ' t1 scope #c_scope in
    let (| tt2, c_tt2 |) = elab_typ' t2 scope #c_scope in
    (| either tt1 tt2, target_lang_sum tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = elab_typ' t1 scope #c_scope in
    let (| tt2, c_tt2 |) = elab_typ' t2 scope #c_scope in
    (| (tt1 * tt2), target_lang_pair tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef t ->
    let (| tt, c_tt |) = elab_typ' t scope #c_scope in
    (| ref tt, target_lang_ref tt #c_tt |)

let elab_typ (t:typ) : Type =
  dfst (elab_typ' t ())

let elab_typ_footprint (t:typ) =
  dsnd (elab_typ' t ())

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
  ctx:(dfst (elab_typ' (TArr TUnit TUnit) rs)) -> 
  ST int (requires (fun h0 -> sep rp rs h0))
      (ensures (fun _ _ h1 -> sep rp rs h1))
         
let progr rp rs f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  f ();
  !rp

(** *** Elaboration of expressions to F* *)
type vcontext (g:context) = x:var{Some? (g x)} -> elab_typ (Some?.v (g x))

let vempty : vcontext empty = fun _ -> assert false

let vextend #t (x:elab_typ t) (#g:context) (ve:vcontext g) : vcontext (extend t g) =
  fun y -> if y = 0 then x else ve (y-1)


//let cast_TArr #t1 #t2 (h : (elab_typ t1 -> Tot (elab_typ t2))) : elab_typ (TArr t1 t2) = h

// let rec fnrec (#a:Type) (n:nat) (acc:a) (iter:a -> a): Tot a =
//   if n = 0 then acc else fnrec (n-1) (iter acc) iter

let footprint_footprint_after_write
  (#t:Type) {| c:target_lang t |} (r:ref t)
  (#a:Type) {| target_lang a |} (v:a)
  (h0 h1:heap) (fp_r:tfootprint):
  Lemma
    (requires (
      dcontains r h0 /\
      dcontains v h0 /\
      equal_dom h0 h1 /\
      modifies !{r} h0 h1 /\
      footprint r h1 ⊆ fp_r
    ))
    (ensures (footprint v h1 ⊆ footprint_after_write v h0 r fp_r))
  = admit ()

let stable_footprint_v (#t:Type) {| target_lang t |} (r:ref t) (v:t) (h0 h1:heap) :
  Lemma
    (requires (
      dcontains r h0 /\
      dcontains v h0 /\
      equal_dom h0 h1 /\

      modifies !{r} h0 h1 /\
      sel h1 r == v 
    ))
    (ensures (footprint v h1 ⊆ footprint v h0))
  =
  introduce !{r} `Set.disjoint` footprint v h0 ==> footprint v h1 ⊆ footprint v h0
  with _. begin
    law1 !{r} v h0 h1
  end;
  introduce !{r} ⊆ footprint v h0 ==> footprint v h1 ⊆ footprint v h0
  with _. begin
    let fpr = !{r} ⊎ (footprint v h0) in
    footprint_after_write_law v h0 r fpr;
    assert (footprint_after_write v h0 r fpr ⊆ fpr ⊎ fpr);
    assert (footprint_after_write v h0 r fpr ⊆ fpr);
    assume (footprint r h1 ⊆ fpr);
    footprint_footprint_after_write r v h0 h1 fpr;
    assert (footprint v h1 ⊆ footprint_after_write v h0 r fpr)
  end

let footprint_r_after_write 
  (#tscope:Type) {| target_lang tscope |} (scope:tscope)
  (#t:Type) {| target_lang t |} (r:ref t) (v:t)
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
  = 
  introduce !{r} `Set.disjoint` footprint scope h0 ==> footprint scope h1 ⊆ (fp ⊎ footprint r h1)
  with _. begin
    law1 !{r} scope h0 h1
  end;
  introduce !{r} ⊆ footprint scope h0 ==> footprint scope h1 ⊆ footprint scope h0 ⊎ footprint r h1
  with _. begin
    footprint_after_write_law scope h0 r (footprint r h1);
    assert (footprint_after_write scope h0 r (footprint r h1) ⊆ footprint scope h0 ⊎ footprint r h1);
    assert (footprint_after_write scope h0 r (footprint r h1) ⊆ fp ⊎ footprint r h1);
    footprint_footprint_after_write r scope h0 h1 (footprint r h1);
    assert (footprint scope h1 ⊆ footprint_after_write scope h0 r (footprint r h1))
  end

let equal_dom_preserves_dcontains (#t:Type) {| target_lang t |} (x:t) (h0 h1:heap) : Lemma
  (requires (equal_dom h0 h1 /\ dcontains x h0))
  (ensures (dcontains x h1)) = admit ()

let rec elab_exp 
  (#g:context)
  (#e:exp) 
  (#t:typ)
  (tyj:typing g e t)
  (ve:vcontext g)
  (#tscope:Type)
  (scope:tscope)
  {| sfp:target_lang tscope |}    
  : ST (elab_typ t) 
     (requires (pre_tgt_arrow scope ()))
     (ensures (post_tgt_arrow scope () #_ #(fun _ -> elab_typ t) #(fun _ -> elab_typ_footprint t)))
    //  (ensures (fun h0 r hf ->
    //     let fp0 = sfp.footprint scope h0 in
    //     let fpf = sfp.footprint scope hf in
    //     modifies fp0 h0 hf /\ 
    //     equal_dom h0 hf /\
    //     ((elab_typ_footprint t).footprint r hf ⊆ fp0) /\
    //     fpf ⊆ fp0 /\ 
    //     sfp.dcontains scope hf /\
    //     (elab_typ_footprint t).dcontains r hf
    //     ))
     (decreases e) =
  let h0 = gst_get () in
  let fp0 = sfp.footprint scope h0 in
  match tyj with
  | TyUnit -> ()
  | TyZero -> 0
  | TyReadRef #_ #_ #t tyj_e -> begin
    let r : ref (elab_typ t) = elab_exp tyj_e ve scope #sfp in
    read r
  end
  | TyWriteRef #_ #_ #_ #t tyj_ref tyj_v -> begin
    let r : ref (elab_typ t) = elab_exp tyj_ref ve scope #sfp in // <-- this is effectful and modifies fp
      let h1 = gst_get () in
      let fp1 = sfp.footprint scope h1 in
      let tgr = elab_typ_footprint (TRef t) in
      
      assert (tgr.dcontains r h1);
      
    let v : elab_typ t = elab_exp tyj_v ve scope #sfp in // this is effectul and modifies fp
      let h2 = gst_get () in
      let fp2 = sfp.footprint scope h2 in
      let tgv = elab_typ_footprint t in

      assert (fp2 ⊆ fp0);
    write r v;
      let h3 = gst_get () in
      let fp3 = sfp.footprint scope h3 in
      let fp_r = tgr.footprint r in
      let fp_v = tgv.footprint v in
      assert (tgv.footprint v h2 ⊆ fp1);
      
      // assert (fp2 ⊆ fp1 ⊆ fp0);
      assert (tgr.footprint r h1 ⊆ fp0);
      equal_dom_preserves_dcontains r h1 h2;
      equal_dom_preserves_dcontains scope h1 h2;
      footprint_r_after_write scope r v fp0 h2 h3;
      assert (fp3 ⊆ fp0 ⊎ fp_r h3);
      // assert ((fp2 `subtract` fp_r h2) ⊆ fp0);
      assert (fp_r h3 `Set.equal` !{r} ⊎ fp_v h3);
      stable_footprint_v #_ #tgv r v h2 h3;
      assert (fp_v h3 ⊆ fp_v h2);
      assert (!{r} ⊆ fp0 /\ fp_v h2 ⊆ fp0 /\ fp_r h3 ⊆ fp0);

      // post
      assert (fp3 ⊆ fp0);
      equal_dom_preserves_dcontains scope h2 h3;
      assert (sfp.dcontains scope h3);
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
