module TargetLangHS

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses

open FStar.HyperStack
open FStar.HyperStack.ST 

let (@) = FStar.List.Tot.append
let (⊆) = Set.subset
let (⊎) = Set.union
let (∩) = Set.intersect

let subtract (#a:eqtype) (s1:Set.set a) (s2:Set.set a) : Set.set a =
  Set.intersect s1 (Set.complement s2)

type tfootprint = Set.set nat

(** target_lang is a shallow embedding of STLC **)
class target_lang (t:Type) = {
  dcontains : t -> mem -> Type0;
  regional : t -> mem -> rid -> Type0;
}

instance target_lang_unit : target_lang unit = {
  dcontains = (fun _ _ -> True);
  regional = (fun _ _ _ -> True);
}

instance target_lang_int : target_lang int = {
  dcontains = (fun _ _ -> True);
  regional = (fun _ _ _ -> True);
}

instance target_lang_pair (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (t1 * t2) = {
  dcontains = (fun (x1, x2) h -> c1.dcontains x1 h /\ c2.dcontains x2 h);
  regional = (fun (x1, x2) h rr -> c1.regional x1 h rr /\ c2.regional x2 h rr);
}

instance target_lang_sum (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (either t1 t2) = {
  dcontains = (fun x h ->
    match x with
    | Inl x1 -> c1.dcontains x1 h
    | Inr x2 -> c2.dcontains x2 h);
  regional = (fun x h rr ->
    match x with
    | Inl x1 -> c1.regional x1 h rr
    | Inr x2 -> c2.regional x2 h rr);
}

instance target_lang_ref (t:Type) {| c:target_lang t |} : target_lang (reference t) = {
  dcontains = (fun (x:reference t) h -> h `contains` x /\ c.dcontains (sel h x) h);
  regional = (fun (x:reference t) h rr -> frameOf x == rr /\ c.regional (sel h x) h rr);  
}

let self_contained_region_inv (rr:rid) (h:mem) : Type0 =
  forall a (c:target_lang (reference a)) (r:reference a). frameOf r == rr ==> 
    c.dcontains r h /\ c.regional r h rr

unfold let pre_tgt_arrow
  (rrs:rid)
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (h0:mem) =
  regional x h0 rrs /\                                                     (* x is in region rs *)
  dcontains x h0 /\                                                       (* required to instantiate the properties of modifies *)
  self_contained_region_inv rrs h0 /\
  is_eternal_region rrs                                                    (* required for using ralloc *)

let post_tgt_arrow
  (rrs:rid)
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (#t2:t1 -> Type) {| tgtr : (x:t1 -> target_lang (t2 x)) |}
  (h0:mem) (r:t2 x) (h1:mem) =
  modifies (Set.singleton rrs) h0 h1 /\                                  (* allow region rs to be modified *)

  // equal_dom h0 h1 /\                                                  (* no dynamic allocation *)
  self_contained_region_inv rrs h1 /\

  ((tgtr x).regional r h1 rrs) /\
  ((tgtr x).dcontains r h1)
(* TODO: what prevents the computation to allocate things in rp? *)


unfold let mk_tgt_arrow  
  (rrs:rid)
  (t1:Type)
  {| tgt_t1: target_lang t1 |}
  (t2:t1 -> Type) 
  {| c2 : (x:t1 -> target_lang (t2 x)) |}
= x:t1 -> ST (t2 x) 
    (requires (pre_tgt_arrow rrs x #tgt_t1))
    (ensures (post_tgt_arrow rrs x #tgt_t1 #t2 #c2))

instance target_lang_arrow 
  (rrs:rid)
  (t1:Type)
  {| target_lang t1 |}
  (t2:t1 -> Type)
  {| (x:t1 -> target_lang (t2 x)) |}
  : target_lang (mk_tgt_arrow rrs t1 t2) = {
    dcontains = (fun _ _ -> True);
    regional = (fun _ _ _ -> True);
  }

open STLC

(** *** Elaboration of types to F* *)
let rec _elab_typ (t:typ) (rrs:rid) : tt:Type & target_lang tt =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = _elab_typ t1 rrs in
    let tt2 (x:dfst tt1) = _elab_typ t2 rrs in
    (| mk_tgt_arrow      rrs (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) #(fun x -> dsnd (tt2 x)),
       target_lang_arrow rrs (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) #(fun x -> dsnd (tt2 x))
    |)
  end 
  | TUnit -> (| unit, target_lang_unit |)
  | TNat -> (| int, target_lang_int |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 rrs in
    let (| tt2, c_tt2 |) = _elab_typ t2 rrs in
    (| either tt1 tt2, target_lang_sum tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 rrs in
    let (| tt2, c_tt2 |) = _elab_typ t2 rrs in
    (| (tt1 * tt2), target_lang_pair tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef t ->
    let (| tt, c_tt |) = _elab_typ t rrs in
    (| reference tt, target_lang_ref tt #c_tt |)

let elab_typ (t:typ) (rrs:rid) : Type =
  dfst (_elab_typ t rrs)

let elab_typ_tgt (t:typ) (rrs:rid): target_lang (elab_typ t rrs)=
  dsnd (_elab_typ t rrs)

let write' (#t:Type) {| c:target_lang t |} (r:reference t) (v:t) : ST unit
  (requires (fun h0 -> 
    dcontains r h0 /\ c.dcontains v h0 /\
    regional r h0 (frameOf r) /\ c.regional v h0 (frameOf r) /\
    self_contained_region_inv (frameOf r) h0))
  (ensures (fun h0 u h1 -> 
    assign_post r v h0 u h1 /\
    dcontains r h1 /\
    regional r h1 (frameOf r) /\
    self_contained_region_inv (frameOf r) h1))
= 
  let h0 = get () in
  assert (forall a (c:target_lang (reference a)) (r':reference a). frameOf r' == frameOf r ==> 
    c.dcontains r' h0 /\ c.regional r' h0 (frameOf r));
  r := v;
  let h1 = get () in
  assume (dcontains r h1);
  assume (regional r h1 (frameOf r));
  assume (forall a (c:target_lang (reference a)) (r':reference a). 
    frameOf r' == frameOf r ==> c.dcontains r' h1 /\ c.regional r' h1 (frameOf r))


val ralloc' (#a:Type) {| c:target_lang a |} (i:rid) (init:a)
  :ST (reference a) (requires (fun m -> is_eternal_region i /\ c.regional init m i))
                    (ensures (fun h0 r h1 -> ralloc_post i init h0 r h1 /\ 
                      regional r h1 i /\
                      (forall (r:rid) . self_contained_region_inv r h0 ==> self_contained_region_inv r h1)
                    ))
let ralloc' i v = 
  let r = ralloc i v in
  admit();
  r

val elab_typ_test0 : 
  #rrs:rid ->
  elab_typ (TArr (TRef TNat) TUnit) rrs
let elab_typ_test0 (y:reference int) =
  write' y (!y + 5);
  ()

val elab_typ_test1 : 
  #rrs:rid ->
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit)) rrs
let elab_typ_test1 #rrs (x:reference (reference int)) (y:reference int) =
  let h0 = get () in
  assert ((elab_typ_tgt (TRef (TRef TNat)) rrs).dcontains x h0); // (this is from a previous pre, and we have to recall)
  let ix = !x in
  write' ix (!ix + 1);
  write' x y;
  write' y (!y + 5);
  ()

val elab_typ_test1' : 
  #rrs:rid ->
  elab_typ (TArr (TRef (TPair (TRef TNat) (TRef TNat))) (TArr TUnit TUnit)) rrs
let elab_typ_test1' #rrs (xs:reference ((reference int) * reference int)) =
  let (x', x'') = !xs in
  write' xs (x', x');
  // xs := (x', x');
  (fun () ->
    let h0 = get () in
    assert ((elab_typ_tgt (TRef (TPair (TRef TNat) (TRef TNat))) rrs).dcontains xs h0);
    (** why do I have to give the specific instance here? *)
    write' xs (x', x'')
  )

// val elab_typ_test2 : elab_typ (TArr TUnit (TRef TNat))
// let elab_typ_test2 () = alloc 0
  
val elab_typ_test2' : 
  #rrs:rid ->
  elab_typ (TArr (TRef TNat) (TRef TNat)) rrs
let elab_typ_test2' x = x

val elab_typ_test3 : 
  #rrs:rid ->
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit) rrs
let elab_typ_test3 f =
  let x:reference int = f () in
  write' x (!x + 1);
  ()

val elab_typ_test4 :
  #rrs:rid ->
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef (TRef TNat)) TUnit)) rrs
let elab_typ_test4 #rrs (x y: reference (reference int)) =
  let h0 = get () in
  assert ((elab_typ_tgt (TRef (TRef TNat)) rrs).dcontains x h0);
  let z = !x in
  let t = !y in
  write' x t;
  write' y z;
  let h1 = get () in 
  assert (regional y h0 rrs);
  ()

val elab_typ_test5 :
   #rrs:rid ->
   elab_typ (TArr TUnit (TRef TNat)) rrs
let elab_typ_test5 #rrs () = 
  let v = ralloc' rrs 0 in 
  v

val elab_typ_test6 :
  #rrs:rid ->
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit) rrs
let elab_typ_test6 #rrs f =
  let x:reference int = f () in
  let y: reference int = ralloc' rrs (!x + 1) in
  ()

let sep
  (#trp:Type) (rp:trp) {| tgt_rp: target_lang trp |}
  (rrp:rid)
  (#trs:Type) (rs:trs) {| tgt_rs: target_lang trs |}
  (rrs:rid)
  h =
  dcontains rp h /\ dcontains rs h /\                       (* required to instantiate the properties of modifies *)
  rrp <> rrs /\                                             (* separation *)
                  (* TODO: this is not enough, because one could be a child of the other. *)
  regional rp h rrp /\ regional rs h rrs

val progr: 
  #rp: reference int -> 
  #rs: reference (reference int) ->
  #rrs:rid ->
  #rrp:rid ->
  ctx:(elab_typ (TArr TUnit TUnit) rrs) ->
  ST unit 
    (requires (fun h0 -> 
      self_contained_region_inv rrs h0 /\
      sep rp rrp rs rrs h0 /\
      is_eternal_region rrs))
    (ensures (fun h0 _ h1 -> sep rp rrp rs rrs h1 /\
                            sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
         
let progr #_ #rs #rrs f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  f ();
  let h1 = get () in
  eliminate forall a (c:target_lang (reference a)) (r:reference a). frameOf r == rrs ==> 
    c.dcontains r h1 /\ c.regional r h1 rrs with (reference int) (solve) rs;
  ()

val progr2: 
  #rp: reference int -> 
  #rs: reference (reference int) ->
  #rrs:rid ->
  #rrp:rid ->
  ctx:(elab_typ (TArr TUnit TUnit) rrs) ->
  ST unit 
    (requires (fun h0 -> 
      self_contained_region_inv rrs h0 /\
      sep rp rrp rs rrs h0 /\
      is_eternal_region rrs /\
      is_eternal_region rrp))
    (ensures (fun h0 _ h1 -> sep rp rrp rs rrs h1 /\
                             sel h0 rp == sel h1 rp))
         
let progr2 #_ #rs #rrs #rrp ctx = 
  let secret: reference int = ralloc' rrp 0 in
  ctx ();
  let v = !secret in
  assert (v == 0);
  let h1 = get () in
  eliminate forall a (c:target_lang (reference a)) (r:reference a). frameOf r == rrs ==> 
    c.dcontains r h1 /\ c.regional r h1 rrs with (reference int) (solve) rs;
  ()

// Test with program passing callback
val cb: rrs: rid -> secret: reference int -> elab_typ (TArr TUnit TUnit) rrs 
let cb rrs secret () =
  assume (frameOf secret == rrs);
  let h0 = get() in
  assume (h0 `contains` secret);
   write' secret (!secret + 1)

val progr3: 
  #rp: reference int -> 
  #rs: reference (reference int) ->
  #rrs:rid ->
  #rrp:rid ->
  ctx:(elab_typ (TArr (TArr TUnit TUnit) TUnit) rrs) ->
  ST unit 
    (requires (fun h0 -> 
      self_contained_region_inv rrs h0 /\
      sep rp rrp rs rrs h0 /\
      is_eternal_region rrs))
    (ensures (fun h0 _ h1 -> sep rp rrp rs rrs h1 /\
                             sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context

// mini to do: the callback of the program should be able to modify rp

let progr3 #_ #rs #rrs #rrp f =
  let secret: reference int = ralloc' rrs 0 in
  let cb: elab_typ (TArr TUnit TUnit) rrs = cb rrs secret in
  f cb;
  let h1 = get () in
    eliminate forall a (c:target_lang (reference a)) (r:reference a). frameOf r == rrs ==> 
     c.dcontains r h1 /\ c.regional r h1 rrs with (reference int) (solve) rs;
  ()

// Test with program getting a callback
val progr4: 
  #rp: reference int -> 
  #rs: reference (reference int) ->
  #rrs:rid ->
  #rrp:rid ->
  ctx:(elab_typ (TArr TUnit (TArr TUnit TUnit)) rrs) ->
  ST unit 
    (requires (fun h0 -> 
      self_contained_region_inv rrs h0 /\
      sep rp rrp rs rrs h0 /\
      is_eternal_region rrs))
    (ensures (fun h0 _ h1 -> sep rp rrp rs rrs h1 /\
                             sel h0 rp == sel h1 rp))

let progr4 #_ #rs #rrs #rrp f =
  let cb = f () in
  cb ();
  let h1 = get () in
     eliminate forall a (c:target_lang (reference a)) (r:reference a). frameOf r == rrs ==> 
      c.dcontains r h1 /\ c.regional r h1 rrs with (reference int) (solve) rs;
  ()