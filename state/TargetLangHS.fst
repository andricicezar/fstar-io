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
  regional = (fun (x1, x2) h r -> c1.regional x1 h r /\ c2.regional x2 h r);
}

instance target_lang_sum (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (either t1 t2) = {
  dcontains = (fun x h ->
    match x with
    | Inl x1 -> c1.dcontains x1 h
    | Inr x2 -> c2.dcontains x2 h);
  regional = (fun x h r ->
    match x with
    | Inl x1 -> c1.regional x1 h r
    | Inr x2 -> c2.regional x2 h r);
}

instance target_lang_ref (t:Type) {| c:target_lang t |} : target_lang (reference t) = {
  dcontains = (fun (x:reference t) h -> h `contains` x /\ c.dcontains (sel h x) h);
  regional = (fun (x:reference t) h r -> frameOf x == r /\ c.regional (sel h x) h r);  
}

let self_contained_region_inv (rs:rid) (h:mem) : Type0 =
  forall a (c:target_lang (reference a)) (r:reference a). frameOf r == rs ==> 
    c.dcontains r h /\ c.regional r h rs

unfold let pre_tgt_arrow
  (rs:rid)
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (h0:mem) =
  regional x h0 rs /\                                                     (* x is in region rs *)
  dcontains x h0 /\                                                       (* required to instantiate the properties of modifies *)
  self_contained_region_inv rs h0

let post_tgt_arrow
  (rs:rid)
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (#t2:t1 -> Type) {| tgtr : (x:t1 -> target_lang (t2 x)) |}
  (h0:mem) (r:t2 x) (h1:mem) =
  modifies (Set.singleton rs) h0 h1 /\                                  (* allow region rs to be modified *)

  // equal_dom h0 h1 /\                                                  (* no dynamic allocation *)
  // self_contained_region_inv rs h0

  ((tgtr x).regional r h1 rs) /\
  ((tgtr x).dcontains r h1)

unfold let mk_tgt_arrow  
  (rs:rid)
  (t1:Type)
  {| tgt_t1: target_lang t1 |}
  (t2:t1 -> Type) 
  {| c2 : (x:t1 -> target_lang (t2 x)) |}
= x:t1 -> ST (t2 x) 
    (requires (pre_tgt_arrow rs x #tgt_t1))
    (ensures (post_tgt_arrow rs x #tgt_t1 #t2 #c2))

instance target_lang_arrow 
  (rs:rid)
  (t1:Type)
  {| target_lang t1 |}
  (t2:t1 -> Type)
  {| (x:t1 -> target_lang (t2 x)) |}
  : target_lang (mk_tgt_arrow rs t1 t2) = {
    dcontains = (fun _ _ -> True);
    regional = (fun _ _ _ -> True);
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
let rec _elab_typ (t:typ) (rs:rid) : tt:Type & target_lang tt =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = _elab_typ t1 rs in
    let tt2 (x:dfst tt1) = _elab_typ t2 rs in
    (| mk_tgt_arrow      rs (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) #(fun x -> dsnd (tt2 x)),
       target_lang_arrow rs (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) #(fun x -> dsnd (tt2 x))
    |)
  end 
  | TUnit -> (| unit, target_lang_unit |)
  | TNat -> (| int, target_lang_int |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 rs in
    let (| tt2, c_tt2 |) = _elab_typ t2 rs in
    (| either tt1 tt2, target_lang_sum tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 rs in
    let (| tt2, c_tt2 |) = _elab_typ t2 rs in
    (| (tt1 * tt2), target_lang_pair tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef t ->
    let (| tt, c_tt |) = _elab_typ t rs in
    (| reference tt, target_lang_ref tt #c_tt |)

let elab_typ (t:typ) (rs:rid) : Type =
  dfst (_elab_typ t rs)

let elab_typ_tgt (t:typ) (rs:rid): target_lang (elab_typ t rs)=
  dsnd (_elab_typ t rs)

val elab_typ_test0 : 
  #rs:rid ->
  elab_typ (TArr (TRef TNat) TUnit) rs
let elab_typ_test0 (y:reference int) =
  y := !y + 5;
  ()

val elab_typ_test1 : 
  #rs:rid ->
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit)) rs
let elab_typ_test1 #rs (x:reference (reference int)) (y:reference int) =
  let h0 = get () in
  assert ((elab_typ_tgt (TRef (TRef TNat)) rs).dcontains x h0); // (this is from a previous pre, and we have to recall)
  let ix = !x in
  ix := !ix + 1;
  x := y;
  y := !y + 5;
  ()

val elab_typ_test1' : 
  #rs:rid ->
  elab_typ (TArr (TRef (TPair (TRef TNat) (TRef TNat))) (TArr TUnit TUnit)) rs
let elab_typ_test1' #rs (xs:reference ((reference int) * reference int)) =
  let (x', x'') = !xs in
  xs := (x', x');
  (fun () ->
    let h0 = get () in
    assert ((elab_typ_tgt (TRef (TPair (TRef TNat) (TRef TNat))) rs).dcontains xs h0);
    (** why do I have to give the specific instance here? *)
    xs := (x', x'')
  )

// val elab_typ_test2 : elab_typ (TArr TUnit (TRef TNat))
// let elab_typ_test2 () = alloc 0
  
val elab_typ_test2' : 
  #rs:rid ->
  elab_typ (TArr (TRef TNat) (TRef TNat)) rs
let elab_typ_test2' x = x

val elab_typ_test3 : 
  #rs:rid ->
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit) rs
let elab_typ_test3 f =
  let x:reference int = f () in
  x := !x + 1;
  ()

let sep
  (#trp:Type) (rp:trp) {| tgt_rp: target_lang trp |}
  (rrp:rid)
  (#trs:Type) (rs:trs) {| tgt_rs: target_lang trs |}
  (rrs:rid)
  h =
  dcontains rp h /\ dcontains rs h /\                       (* required to instantiate the properties of modifies *)
  rrp <> rrs /\                                             (* separation *)
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
      sep rp rrp rs rrs h0))
    (ensures (fun _ _ h1 -> sep rp rrp rs rrs h1))
         
let progr #_ #rs #rrs f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  f ();
  let h1 = get () in
  assume (self_contained_region_inv rrs h1); // this should be a post of f
  eliminate forall a (c:target_lang (reference a)) (r:reference a). frameOf r == rrs ==> 
    c.dcontains r h1 /\ c.regional r h1 rrs with (reference int) (solve) rs;
  ()