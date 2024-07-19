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
  (leaked:tfootprint)
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (h0:heap) =
  dcontains x h0

let post_tgt_arrow
  (leaked:tfootprint)
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (#t2:t1 -> Type) {| tgtr : (x:t1 -> target_lang (t2 x)) |}
  (h0:heap) (r:t2 x) (h1:heap) =
  let leaked = leaked ⊎ tgtx.footprint x h0 in
  modifies leaked h0 h1 /\ 
  equal_dom h0 h1 /\ 
  ((tgtr x).footprint r h1) ⊆ leaked /\ 
  ((tgtr x).dcontains r h1)

unfold let mk_tgt_arrow  
  (t1:Type)
  {| tgt_t1: target_lang t1 |}
  (t2:t1 -> Type) 
  (leaked:tfootprint)
  {| c2 : (x:t1 -> target_lang (t2 x)) |}
= x:t1 -> ST (t2 x) 
    (requires (pre_tgt_arrow leaked x #tgt_t1))
    (ensures (post_tgt_arrow leaked x #tgt_t1 #t2 #c2))

instance target_lang_arrow 
  (t1:Type)
  {| target_lang t1 |}
  (t2:t1 -> Type)
  (leaked:tfootprint)
  {| (x:t1 -> target_lang (t2 x)) |}
  : target_lang (mk_tgt_arrow t1 t2 leaked) = {
    footprint = (fun _ _ -> Set.empty); // <-- TODO: why no footprint for functions?
    footprint_after_write = (fun _ _ _ _ -> Set.empty);
    footprint_after_write_law = (fun _ _ _ _ -> ());
    dcontains = (fun _ _ -> True);
  }

open STLC

(** TODO:
  let f : x:ref t   -> unit -> unit
                    ^       ^
                    |       |
                    |       here x can have a different footprint, thus it is leaked again. 
                    |       also, anything that was in x, could have a different footprint, thus it is leaked.
                    the entire footprint of x is leaked
**)

(** *** Elaboration of types to F* *)
let rec _elab_typ (t:typ) (leaked:tfootprint) : tt:Type & target_lang tt =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = _elab_typ t1 leaked in
    let tt2 (x:dfst tt1) = _elab_typ t2 leaked in (* TODO: <-- leaked has to be extend with the footprint of x at this point *)
    (| mk_tgt_arrow      (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) leaked #(fun x -> dsnd (tt2 x)),
       target_lang_arrow (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) leaked #(fun x -> dsnd (tt2 x))
    |)
  end 
  | TUnit -> (| unit, target_lang_unit |)
  | TNat -> (| int, target_lang_int |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 leaked in
    let (| tt2, c_tt2 |) = _elab_typ t2 leaked in
    (| either tt1 tt2, target_lang_sum tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 leaked in
    let (| tt2, c_tt2 |) = _elab_typ t2 leaked in
    (| (tt1 * tt2), target_lang_pair tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef t ->
    let (| tt, c_tt |) = _elab_typ t leaked in
    (| ref tt, target_lang_ref tt #c_tt |)

let elab_typ (t:typ) (leaked:tfootprint) : Type =
  dfst (_elab_typ t leaked)

let elab_typ_tgt (t:typ) (leaked:tfootprint) : target_lang (elab_typ t leaked)=
  dsnd (_elab_typ t leaked)

// let elab_typ' (t:typ) (#tleaked:typ) (leaked:dfst (_elab_typ tleaked ())) : Type =
//   let (| ty, c_leaked |) = _elab_typ tleaked () in
//   elab_typ t #ty leaked

// let elab_typ_tgt' (t:typ) (#tleaked:typ) (leaked:dfst (_elab_typ tleaked ())) : target_lang (elab_typ' t leaked)=
//   let (| ty, c_leaked |) = _elab_typ tleaked () in
//   elab_typ_tgt t #ty leaked #c_leaked

val elab_typ_test0 : elab_typ (TArr (TRef TNat) TUnit) Set.empty
let elab_typ_test0 (y:ref int) =
  y := !y + 5;
  ()

val elab_typ_test1 : elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit)) Set.empty
let elab_typ_test1 (x:ref (ref int)) (y:ref int) =
  let ix = !x in
  ix := !ix + 1;
  x := y;
  y := !y + 5;
  ()

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

// let rec elab_exp 
//   (#g:context)
//   (#e:exp) 
//   (#t:typ)
//   (tyj:typing g e t)
//   (ve:vcontext g)
//   (#tleaked:typ)
//   (leaked:elab_typ tleaked ())
//   : ST (elab_typ' t leaked) 
//      (requires (pre_tgt_arrow leaked #(elab_typ_tgt tleaked ()) ()))
//      (ensures (post_tgt_arrow leaked #(elab_typ_tgt tleaked ()) () #_ #(fun _ -> elab_typ' t leaked) #(fun _ -> elab_typ_tgt' t leaked)))
//      (decreases e) =
//   admit ()