module TargetLangStatic

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
  dcontains : t -> heap -> Type0;
}

instance target_lang_unit : target_lang unit = {
  footprint = (fun _ _ -> Set.empty);
  dcontains = (fun _ _ -> True);
}

instance target_lang_int : target_lang int = {
  footprint = (fun _ _ -> Set.empty);
  dcontains = (fun _ _ -> True);
}

instance target_lang_pair (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (t1 * t2) = {
  footprint = (fun (x1, x2) h -> 
    (c1.footprint x1 h) ⊎ (c2.footprint x2 h));
  dcontains = (fun (x1, x2) h -> c1.dcontains x1 h /\ c2.dcontains x2 h);
}

instance target_lang_sum (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (either t1 t2) = {
  footprint = (fun x h -> 
     match x with
     | Inl x1 -> c1.footprint x1 h
     | Inr x2 -> c2.footprint x2 h);
  dcontains = (fun x h ->
    match x with
    | Inl x1 -> c1.dcontains x1 h
    | Inr x2 -> c2.dcontains x2 h);
}

instance target_lang_ref (t:Type) {| c:target_lang t |} : target_lang (ref t) = {
  footprint = (fun x h -> 
    !{x} ⊎ (c.footprint (sel h x) h)); // <--- following x in h
  dcontains = (fun x h -> h `contains` x /\ c.dcontains (sel h x) h);
}

let sep
  (#trp:Type) (rp:trp) {| tgt_rp: target_lang trp |}
  (#trs:Type) (rs:trs) {| tgt_rs: target_lang trs |}
  h =
  dcontains rp h /\ dcontains rs h /\                       (* required to instantiate the properties of modifies *)
  footprint rp h `Set.disjoint` footprint rs h              (* separation *)

unfold let pre_tgt_arrow
  (#trp:Type) (rp:trp) {| tgt_rp: target_lang trp |}
  (#trs:Type) (rs:trs) {| tgt_rs: target_lang trs |}
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (h0:heap) =
  sep rp rs h0 /\                                                       (* our property *)

  dcontains x h0 /\                                                     (* being pedantic *)
  tgtx.footprint x h0 ⊆ (Set.complement (tgt_rp.footprint rp h0))       (* allowing the computation to modify x *)


let post_tgt_arrow
  (#trp:Type) (rp:trp) {| tgt_rp: target_lang trp |}
  (#trs:Type) (rs:trs) {| tgt_rs: target_lang trs |}
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (#t2:t1 -> Type) {| tgtr : (x:t1 -> target_lang (t2 x)) |}
  (h0:heap) (r:t2 x) (h1:heap) =
  sep rp rs h1 /\                                                       (* invariant, as in pre *)
  
  modifies (Set.complement (tgt_rp.footprint rp h0)) h0 h1 /\          (* allowing the computation to modify anything that is not in rp *)
  tgt_rp.footprint rp h0 == tgt_rp.footprint rp h1 /\                  (* pedantic, should follow from modifies? *)

  equal_dom h0 h1 /\                                                    (* no dynamic allocation *)

  ((tgtr x).footprint r h1) ⊆ (Set.complement (tgt_rp.footprint rp h0)) /\  (* returned values must be in rs and allocated *)
  ((tgtr x).dcontains r h1)

unfold let mk_tgt_arrow  
  (#trp:Type) (rp:trp) {| tgt_rp: target_lang trp |}
  (#trs:Type) (rs:trs) {| tgt_rs: target_lang trs |}
  (t1:Type)
  {| tgt_t1: target_lang t1 |}
  (t2:t1 -> Type) 
  {| c2 : (x:t1 -> target_lang (t2 x)) |}
= x:t1 -> ST (t2 x) 
    (requires (pre_tgt_arrow rp rs x #tgt_t1))
    (ensures (post_tgt_arrow rp rs x #tgt_t1 #t2 #c2))

instance target_lang_arrow 
  (#trp:Type) (rp:trp) {| tgt_rp: target_lang trp |}
  (#trs:Type) (rs:trs) {| tgt_rs: target_lang trs |}
  (t1:Type)
  {| target_lang t1 |}
  (t2:t1 -> Type)
  {| (x:t1 -> target_lang (t2 x)) |}
  : target_lang (mk_tgt_arrow rp rs t1 t2) = {
    footprint = (fun _ _ -> Set.empty); // <-- TODO: why no footprint for functions?
    dcontains = (fun _ _ -> True);
  }

open STLC

(** TODO:
  let f : x:ref t   -> unit -> unit
                    ^       ^
                    |       |
                    |       here x can have a different footprint, thus it is protected again. 
                    |       also, anything that was in x, could have a different footprint, thus it is protected.
                    the entire footprint of x is protected
**)

(** *** Elaboration of types to F* *)
let rec _elab_typ (t:typ) (#trp:Type) (rp:trp) {| tgt_rp: target_lang trp |} (#trs:Type) (rs:trs) {| tgt_rs: target_lang trs |} : tt:Type & target_lang tt =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = _elab_typ t1 rp #tgt_rp rs #tgt_rs in
    let tt2 (x:dfst tt1) = _elab_typ t2 rp #tgt_rp rs #tgt_rs in
    (| mk_tgt_arrow      rp #tgt_rp rs #tgt_rs (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) #(fun x -> dsnd (tt2 x)),
       target_lang_arrow rp #tgt_rp rs #tgt_rs (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) #(fun x -> dsnd (tt2 x))
    |)
  end 
  | TUnit -> (| unit, target_lang_unit |)
  | TNat -> (| int, target_lang_int |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 rp #tgt_rp rs #tgt_rs in
    let (| tt2, c_tt2 |) = _elab_typ t2 rp #tgt_rp rs #tgt_rs in
    (| either tt1 tt2, target_lang_sum tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 rp #tgt_rp rs #tgt_rs in
    let (| tt2, c_tt2 |) = _elab_typ t2 rp #tgt_rp rs #tgt_rs in
    (| (tt1 * tt2), target_lang_pair tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef t ->
    let (| tt, c_tt |) = _elab_typ t rp #tgt_rp rs #tgt_rs in
    (| ref tt, target_lang_ref tt #c_tt |)

let elab_typ (t:typ) (#trp:Type) (rp:trp) {| tgt_rp: target_lang trp |} (#trs:Type) (rs:trs) {| tgt_rs: target_lang trs |} : Type =
  dfst (_elab_typ t rp rs)

let elab_typ_tgt (t:typ) (#trp:Type) (rp:trp) {| tgt_rp: target_lang trp |} (#trs:Type) (rs:trs) {| tgt_rs: target_lang trs |}: target_lang (elab_typ t rp rs)=
  dsnd (_elab_typ t rp rs)

val elab_typ_test0 : 
  #rp:ref int ->
  #rs:ref (ref int) ->
  elab_typ (TArr (TRef TNat) TUnit) rp rs
let elab_typ_test0 (y:ref int) =
  assume (int =!= ref int);
  y := !y + 5;
  ()

val elab_typ_test1 : 
  #rp:ref int ->
  #rs:ref (ref int) ->
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit)) rp rs
let elab_typ_test1 #rp #rs (x:ref (ref int)) (y:ref int) =
  assume (int =!= ref int);
  let h0 = gst_get () in
  assume (footprint x h0 ⊆ Set.complement (footprint rp h0)); (** TODO: this is a pre of partially applying x,
                                                                        but not when applying y *)
  let ix = !x in
  ix := !ix + 1;
  x := y;
  y := !y + 5;
  ()

val elab_typ_test1' :
  #rp:ref int ->
  #rs:ref (ref int * ref int) -> 
  elab_typ (TArr (TRef (TPair (TRef TNat) (TRef TNat))) (TArr TUnit TUnit)) rp rs
let elab_typ_test1' #rp #rs (xs:(ref ((ref int) * ref int))) =
  let (x', x'') = !xs in
  xs := (x', x');
  (fun () ->
    let h0 = get () in
    assume (dcontains xs h0); (* TODO: we know nothing of xs, x' and x'' *)
    assume (sep x' rp h0);
    assume (sep x'' rp h0);
    xs := (x', x'')
  )
  
val elab_typ_test2' : 
  #rp:ref int ->
  #rs:ref (ref int) ->
  elab_typ (TArr (TRef TNat) (TRef TNat)) rp rs
let elab_typ_test2' x = x

val elab_typ_test3 : 
  #rp:ref int ->
  #rs:ref (ref int) ->
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit) rp rs
let elab_typ_test3 f =
  assume (int =!= ref int);
  let x:ref int = f () in
  x := !x + 1;
  ()

val progr: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr TUnit TUnit) rp rs) ->
  ST int (requires (fun h0 -> sep rp rs h0))
      (ensures (fun _ _ h1 -> sep rp rs h1))
         
let progr rp rs f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  f ();
  !rp