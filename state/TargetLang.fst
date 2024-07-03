module TargetLang

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ref

type tfootprint = Set.set nat

(** target_lang is a shallow embedding of STLC **)
class target_lang (t:Type) = {
    footprint : t -> heap -> (erased tfootprint)
}

instance target_lang_unit : target_lang unit = {
    footprint = fun _ _ -> Set.empty
}

instance target_lang_int : target_lang int = {
    footprint = fun _ _ -> Set.empty
}

instance target_lang_pair (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (t1 * t2) = {
    footprint = fun (x1, x2) h -> 
        (c1.footprint x1 h) `Set.union` 
        (c2.footprint x2 h)
}

instance target_lang_sum (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (either t1 t2) = {
    footprint = fun x h -> 
        match x with
        | Inl x1 -> c1.footprint x1 h
        | Inr x2 -> c2.footprint x2 h
}

instance target_lang_ref (t:Type) {| c:target_lang t |} : target_lang (ref t) = {
    footprint = fun x h -> 
        (only x) `Set.union`
        (c.footprint (sel h x) h) // <--- following x in h
}

let mk_tgt_arrow  
  (t1:Type)
  {| target_lang t1 |}
  (t2:t1 -> Type) 
  (#tscope:Type)
  (scope:tscope)
  {| target_lang tscope |}
  {| c2 : (x:t1 -> target_lang (t2 x)) |}
=
  x:t1 -> ST (t2 x) 
     (requires (fun _ -> True))
     (ensures (fun h0 r h1 -> 
        let fp0 = (target_lang_pair tscope t1).footprint (scope, x) h0 in
     //    let fp1 = (target_lang_pair tscope t1).footprint (scope, x) h1 in
        (modifies fp0 h0 h1)
     //    (exists fp1' fp1''. Set.disjoint fp1' fp1'' /\ Set.equal fp1 (Set.union fp1' fp1'') /\
     //                        fp1' `Set.subset` fp0 /\ (forall ad. ad `Set.mem` fp1'' ==> addr_unused_in ad h0))
         ///\
     //    (forall z. Set.mem z ((c2 x).footprint r h1) ==> Set.mem z fp \/ addr_unused_in z h0) // <-- returned references either are already in scope or are fresh
 ))

instance target_lang_arrow 
    (t1:Type)
    {| target_lang t1 |}
    (t2:t1 -> Type) 
    (#tscope:Type)
    (scope:tscope)
    {| target_lang tscope |}
    {| (x:t1 -> target_lang (t2 x)) |}
    : 
    target_lang (mk_tgt_arrow t1 t2 scope) = {
    footprint = fun _ _ -> Set.empty           // <-- TODO: why no footprint for functions?
}

open STLC

(** *** Elaboration of types to F* *)
let rec elab_typ' (t:typ) (#tscope:Type) (scope:tscope) (c_scope:target_lang tscope) : tt:Type & target_lang tt =
  match t with
  | TArr t1 t2 -> begin
     let (| tt1, c_tt1 |) = elab_typ' t1 scope c_scope in
     let tt2 (x:tt1) = elab_typ' t2 (scope, x) (target_lang_pair tscope tt1 #c_scope #c_tt1) in
     (| mk_tgt_arrow      tt1 #c_tt1 (fun x -> dfst (tt2 x)) scope #c_scope #(fun x -> dsnd (tt2 x)),
        target_lang_arrow tt1 #c_tt1 (fun x -> dfst (tt2 x)) scope #c_scope #(fun x -> dsnd (tt2 x))
     |)
  end 
  | TUnit -> (| unit, target_lang_unit |)
  | TNat -> (| int, target_lang_int |)
  | TSum t1 t2 ->
     let (| tt1, c_tt1 |) = elab_typ' t1 scope c_scope in
     let (| tt2, c_tt2 |) = elab_typ' t2 scope c_scope in
     (| either tt1 tt2, target_lang_sum tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
     let (| tt1, c_tt1 |) = elab_typ' t1 scope c_scope in
     let (| tt2, c_tt2 |) = elab_typ' t2 scope c_scope in
     (| (tt1 * tt2), target_lang_pair tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef t ->
     let (| tt, c_tt |) = elab_typ' t scope c_scope in
     (| ref tt, target_lang_ref tt #c_tt |)

let elab_typ (t:typ) : Type =
  dfst (elab_typ' t () target_lang_unit)

let elab_typ_footprint (t:typ) =
  dsnd (elab_typ' t () target_lang_unit)

val elab_typ_test1 : elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit))
let elab_typ_test1 (x:ref (ref int)) (y:ref int) =
  let ix = !x in
  ix := !ix + 1;
  x := y;
  y := !y + 5;
  ()

val elab_typ_test2 : elab_typ (TArr TUnit (TRef TNat))
let elab_typ_test2 () = alloc 0
  
val elab_typ_test2' : elab_typ (TArr (TRef TNat) (TRef TNat))
let elab_typ_test2' x = x

// val elab_typ_test3 : elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
// let elab_typ_test3 f =
//   let x:ref int = f () in
//   x := !x + 1;
//   ()

(*** NOT UPDATED FROM HERE **)
(** *** Elaboration of expressions to F* *)
type vcontext (g:context) = x:var{Some? (g x)} -> elab_typ (Some?.v (g x))

let vempty : vcontext empty = fun _ -> assert false

let vextend #t (x:elab_typ t) (#g:context) (ve:vcontext g) : vcontext (extend t g) =
  fun y -> if y = 0 then x else ve (y-1)


//let cast_TArr #t1 #t2 (h : (elab_typ t1 -> Tot (elab_typ t2))) : elab_typ (TArr t1 t2) = h

open FStar.List.Tot

// let rec fnrec (#a:Type) (n:nat) (acc:a) (iter:a -> a): Tot a =
//      if n = 0 then acc else fnrec (n-1) (iter acc) iter

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
     (requires (fun _ -> True))
     (ensures (fun h0 r h1 ->
          let fp0 = sfp.footprint scope h0 in
          let fp1 = sfp.footprint scope h1 in
          (modifies fp0 h0 h1)))
     (decreases e) = // <-- TODO: ST is divergent, can we state that this terminates?
     // let h0 = gst_get () in
     // let fp = sfp.footprint scope h0 in
     match tyj with
     | TyUnit -> ()
     | TyZero -> 0
     | TyAllocRef #_ #_ #t tyj_e -> begin
          let v : elab_typ t = elab_exp tyj_e ve scope #sfp in
          alloc v // <-- either this modifies the footprint or not
     end
     | TyReadRef #_ #_ #t tyj_e -> begin
          let v : ref (elab_typ t) = elab_exp tyj_e ve scope #sfp in
          read v
     end
     | TyWriteRef #_ #_ #_ #t tyj_ref tyj_v -> begin
               let h0 = gst_get () in
               let fp0 = sfp.footprint scope h0 in
          let r : ref (elab_typ t) = elab_exp tyj_ref ve scope #sfp in // <-- this is effectful and modifies fp
               let h1 = gst_get () in
          let v : elab_typ t = elab_exp tyj_v ve scope #sfp in // this is effectul and modifies fp
               let h2 = gst_get () in
               assume (modifies fp0 h0 h2);
          write r v;
               let h3 = gst_get () in
               assert (modifies (only r) h2 h3);
               assume (Set.subset (only r) fp0);
               assert (modifies fp0 h0 h3);
          ()
     end
     | _ -> admit ()

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
