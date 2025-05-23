module TargetLangStaticFP

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
  deep_contains : heap -> t -> Type0;
  deep_recall : (r:t) -> ST unit 
              (requires (fun h -> True))
              (ensures  (fun h0 _ h1 -> h0 == h1 /\ h1 `deep_contains` r));
  deep_equality : heap -> heap -> t -> Type0;
}

instance target_lang_unit : target_lang unit = {
  footprint = (fun _ _ -> Set.empty);
  deep_contains = (fun _ _ -> True);
  deep_recall = (fun _ -> ());
  deep_equality = (fun _ _ _ -> True)
}

instance target_lang_int : target_lang int = {
  footprint = (fun _ _ -> Set.empty);
  deep_contains = (fun _ _ -> True);
  deep_recall = (fun _ -> ());
  deep_equality = (fun _ _ _ -> True)
}

instance target_lang_pair (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (t1 * t2) = {
  footprint = (fun (x1, x2) h -> 
    (c1.footprint x1 h) ⊎ (c2.footprint x2 h));
  deep_contains = (fun h (x1, x2) -> h `deep_contains` x1 /\ h `deep_contains` x2);
  deep_recall = (fun (x1, x2) -> c1.deep_recall x1; c2.deep_recall x2);
  deep_equality = (fun h0 h1 (x1, x2) -> deep_equality h0 h1 x1 /\ deep_equality h0 h1 x2)
}

instance target_lang_sum (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (either t1 t2) = {
  footprint = (fun x h -> 
     match x with
     | Inl x1 -> c1.footprint x1 h
     | Inr x2 -> c2.footprint x2 h);
  deep_contains = (fun h x ->
    match x with
    | Inl x1 -> h `deep_contains` x1
    | Inr x2 -> h `deep_contains` x2);
  deep_recall = (fun x ->
    match x with
    | Inl x1 -> c1.deep_recall x1
    | Inr x2 -> c2.deep_recall x2);
  deep_equality = (fun h0 h1 x ->
    match x with
    | Inl x1 -> c1.deep_equality h0 h1 x1
    | Inr x2 -> c2.deep_equality h0 h1 x2)
}

instance target_lang_ref (t:Type) {| c:target_lang t |} : target_lang (ref t) = {
  footprint = (fun x h -> 
    !{x} ⊎ (c.footprint (sel h x) h)); // <--- following x in h
  deep_contains = (fun h x -> h `contains` x /\  h `deep_contains` (sel h x));
  deep_recall = (fun x -> recall x; c.deep_recall !x);
  deep_equality = (fun h0 h1 x -> (sel h0 x == sel h1 x) /\ c.deep_equality h0 h1 (sel h0 x))
}

let if_not_private_never_private (rp:tfootprint) (h:heap) =
  forall a (c:target_lang (ref a)) (x:ref a). ~(addr_of x `Set.mem` rp) ==>
    c.footprint x h `Set.disjoint` rp

unfold let pre_tgt_arrow
  (rp:tfootprint)
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (h0:heap) =
  h0 `deep_contains` x /\                                               (* being pedantic *)
  tgtx.footprint x h0 `Set.disjoint` rp /\    (* allowing the computation to modify x *)
  if_not_private_never_private rp h0

let post_tgt_arrow
  (rp:tfootprint)
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (#t2:t1 -> Type) {| tgtr : (x:t1 -> target_lang (t2 x)) |}
  (h0:heap) (r:t2 x) (h1:heap) =
  if_not_private_never_private rp h1 /\
    
  modifies (Set.complement rp) h0 h1 /\          (* allowing the computation to modify anything that is not in rp *)

  // equal_dom h0 h1 /\                                                    (* no dynamic allocation *)

  ((tgtr x).footprint r h1) `Set.disjoint` rp /\  (* returned values must be in rs and allocated *)
  ((tgtr x).deep_contains h1 r)

unfold let mk_tgt_arrow  
  (rp:tfootprint)
  (t1:Type)
  {| tgt_t1: target_lang t1 |}
  (t2:t1 -> Type) 
  {| c2 : (x:t1 -> target_lang (t2 x)) |}
= x:t1 -> ST (t2 x) 
    (requires (pre_tgt_arrow rp x #tgt_t1))
    (ensures (post_tgt_arrow rp x #tgt_t1 #t2 #c2))

instance target_lang_arrow 
  (rp:tfootprint)
  (t1:Type)
  {| target_lang t1 |}
  (t2:t1 -> Type)
  {| (x:t1 -> target_lang (t2 x)) |}
  : target_lang (mk_tgt_arrow rp t1 t2) = {
    footprint = (fun _ _ -> Set.empty); // <-- TODO: why no footprint for functions?
    deep_contains = (fun _ _ -> True);
    deep_recall = (fun _ -> ());
    deep_equality = (fun _ _ _ -> True)
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
let rec _elab_typ (t:typ) (rp:tfootprint) : tt:Type & target_lang tt =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = _elab_typ t1 rp in
    let tt2 (x:dfst tt1) = _elab_typ t2 rp in
    (| mk_tgt_arrow      rp (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) #(fun x -> dsnd (tt2 x)),
       target_lang_arrow rp (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) #(fun x -> dsnd (tt2 x))
    |)
  end 
  | TUnit -> (| unit, target_lang_unit |)
  | TNat -> (| int, target_lang_int |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 rp in
    let (| tt2, c_tt2 |) = _elab_typ t2 rp in
    (| either tt1 tt2, target_lang_sum tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 rp in
    let (| tt2, c_tt2 |) = _elab_typ t2 rp in
    (| (tt1 * tt2), target_lang_pair tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef t ->
    let (| tt, c_tt |) = _elab_typ t rp in
    (| ref tt, target_lang_ref tt #c_tt |)

let elab_typ (t:typ) (rp:tfootprint) : Type =
  dfst (_elab_typ t rp)

let elab_typ_tgt (t:typ) (rp:tfootprint) : target_lang (elab_typ t rp)=
  dsnd (_elab_typ t rp)

(** ** Examples **)

let write' (rp:tfootprint) (#a:Type) {| c:target_lang a |} (r:ref a) (v:a) : ST unit
  (requires (fun h0 -> footprint r h0 `Set.disjoint` rp /\
                       footprint v h0 `Set.disjoint` rp /\
                       if_not_private_never_private rp h0))
  (ensures (fun h0 _ h1 -> 
                      h0 `contains` r /\ modifies (only r) h0 h1 /\ equal_dom h0 h1 /\ sel h1 r == v /\
                      footprint r h1 `Set.disjoint` rp /\
                      if_not_private_never_private rp h1)) =
  admit ();
  write r v

let alloc' (rp:tfootprint) (#a:Type) {| c:target_lang a |} (v:a) : ST (ref a)
  (requires (fun h0 -> footprint v h0 `Set.disjoint` rp /\
                       if_not_private_never_private rp h0))
  (ensures (fun h0 r h1 -> 
                      fresh r h0 h1 /\ modifies Set.empty h0 h1 /\ sel h1 r == v /\
                      ~(addr_of r `Set.mem` rp) /\ (*TODO: idk if this can be proven *)
                      footprint r h1 `Set.disjoint` rp /\
                      if_not_private_never_private rp h1)) =
  admit ();
  alloc v


val ctx_update_ref_test : 
  #rp:tfootprint ->
  elab_typ (TArr (TRef TNat) TUnit) rp
let ctx_update_ref_test #rp (y:ref int) =
  write' rp y (!y + 5);
  ()

val ctx_update_multiple_refs_test : 
  #rp:tfootprint ->
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit)) rp
let ctx_update_multiple_refs_test #rp (x:ref (ref int)) (y:ref int) =
  assume (ref int =!= int);
  deep_recall x; (* Fstar forgets that x is contained **)
  let ix = !x in
  write' rp ix (!ix + 1);
  write' rp x y;
  write' rp y (!y + 5);
  ()

val ctx_HO_test1 : 
  #rp:tfootprint ->
  elab_typ (TArr (TRef (TPair (TRef TNat) (TRef TNat))) (TArr TUnit TUnit)) rp
let ctx_HO_test1 #rp (xs:ref ((ref int) * ref int)) =
  let (x', x'') = !xs in
  write' rp xs (x', x');  // xs := (x', x');
  (fun () ->
    deep_recall xs;
    recall x';
    recall x'';
    write' rp xs (x', x'')
  )
  
val ctx_identity : 
  #rrs:tfootprint ->
  elab_typ (TArr (TRef TNat) (TRef TNat)) rrs
let ctx_identity x = x

val ctx_HO_test2 : 
  #rp:tfootprint ->
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit) rp
let ctx_HO_test2 #rp f =
  let x:ref int = f () in
  write' rp x (!x + 1);
  ()

val ctx_swap_ref_test :
  #rp:tfootprint ->
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef (TRef TNat)) TUnit)) rp
let ctx_swap_ref_test #rp (x y: ref (ref int)) =
  assume (int =!= ref int);
  assume (ref (ref int) =!= ref int);
  let h0 = gst_get () in
  deep_recall x;
  let z = !x in
  let t = !y in
  assert (footprint x h0 `Set.disjoint` rp);
  assert (footprint t h0 `Set.disjoint` rp);
  write' rp x t;
  write' rp y z;
  ()

val ctx_dynamic_alloc_test :
   #rp:tfootprint ->
   elab_typ (TArr TUnit (TRef TNat)) rp
let ctx_dynamic_alloc_test #rp () = 
  let v = alloc' rp 0 in 
  v

val ctx_HO_test3 :
  #rp:tfootprint ->
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit) rp
let ctx_HO_test3 #rp f =
  let x:ref int = f () in
  let y: ref int = alloc' rp (!x + 1) in
  ()

val ctx_returns_callback_test :
  #rp:tfootprint ->
  elab_typ (TArr TUnit (TArr TUnit TUnit)) rp
let ctx_returns_callback_test #rp () =
  let x: ref int = alloc' rp 13 in
   let cb : elab_typ (TArr TUnit TUnit) rp = (fun() ->
     recall x;
     write' rp x (!x % 5)
   ) in
  cb

val ctx_HO_test4 :
   #rp:tfootprint ->
   elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit) rp
let ctx_HO_test4 #rp f =
  let x:ref int = f () in
  let y: ref (ref int) = alloc' rp x in
  ()

val progr_sep_test: 
  #rp: ref int -> 
  #rs: ref (ref int) ->
  #frp:tfootprint ->
  ctx:(elab_typ (TArr TUnit TUnit) frp) ->
  ST unit 
    (requires (fun h0 -> 
      if_not_private_never_private frp h0 /\
      h0 `deep_contains` rs /\ h0 `deep_contains` rp /\
      footprint rp h0 `Set.equal` frp /\
      footprint rs h0 `Set.disjoint` frp))
    (ensures (fun h0 _ h1 -> footprint rs h0 `Set.disjoint` frp /\
                             sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
         
let progr_sep_test f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  f ()

val progr_secret_unchanged_test: 
  #rp: ref int -> 
  #rs: ref (ref int) ->
  #frp:tfootprint ->
  ctx:(elab_typ (TArr TUnit TUnit) frp) ->
  ST unit 
    (requires (fun h0 -> 
      if_not_private_never_private frp h0 /\
      h0 `deep_contains` rs /\ h0 `deep_contains` rp /\
      footprint rp h0 `Set.equal` frp /\
      footprint rs h0 `Set.disjoint` frp))
    (ensures (fun h0 _ h1 -> footprint rs h0 `Set.disjoint` frp /\
                             sel h0 rp == sel h1 rp))
         
// let progr_secret_unchanged_test #rp #rs #frp ctx = 
//   let secret: ref int = alloc' frp 0 in
//   // TODO:    ^^^ one would need an alloc that reuses a address from frp.
//   ctx ();
//   let v = !secret in
//   assert (v == 0);
//   deep_recall rs;
//   admit ();
//   ()

// val progr_passing_callback_test: 
//   #rp: ref int -> 
//   #rs: ref (ref int) ->
//   #rrs:tfootprint ->
//   #rrp:tfootprint ->
//   ctx:(elab_typ (TArr (TArr TUnit TUnit) TUnit) rrs) ->
//   ST unit 
//     (requires (fun h0 -> 
//       self_contained_region_inv rrs h0 /\
//       sep rp rrp rs rrs h0 /\
//       is_eternal_region rrs))
//     (ensures (fun h0 _ h1 -> sep rp rrp rs rrs h1 /\
//                              sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context

// // TODO: the callback of the program should be able to modify rp
// let progr_passing_callback_test #_ #rs #rrs #rrp f =
//   let secret: ref int = ralloc' rrs 0 in
//   let cb: elab_typ (TArr TUnit TUnit) rrs = (fun () -> write' rp secret (!secret + 1)) in
//   f cb;
//   deep_recall rs;
//   ()

// val progr_getting_callback_test: 
//   #rp: ref int -> 
//   #rs: ref (ref int) ->
//   #rrs:tfootprint ->
//   #frp:tfootprint ->
//   ctx:(elab_typ (TArr TUnit (TArr TUnit TUnit)) rrs) ->
//   ST unit 
//     (requires (fun h0 -> 
//       if_not_private_never_private frp h0
//       sep rp rrp rs rrs h0 /\
//       is_eternal_region rrs))
//     (ensures (fun h0 _ h1 -> sep rp rrp rs rrs h1 /\
//                              sel h0 rp == sel h1 rp))

// let progr_getting_callback_test #_ #rs #rrs #rrp f =
//   let cb = f () in
//   cb ();
//   deep_recall rs;
//   ()

val progr123 : 
  (#t:Type) ->
  {| c:target_lang t |} ->
  rp: ref t ->
  #frp : tfootprint ->
  ctx:(elab_typ (TArr TUnit TUnit) frp) ->
  ST unit 
    (requires (fun h0 ->
      h0 `deep_contains` rp /\
      footprint rp h0 `Set.equal` frp /\
      if_not_private_never_private frp h0))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp))
         
let progr123 rp f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  f ()