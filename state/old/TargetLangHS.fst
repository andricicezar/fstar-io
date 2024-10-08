module TargetLangHS

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses

open FStar.HyperStack
open FStar.HyperStack.ST 

type rref (t:Type) = r:(reference t){
    not (is_mm r) /\
    is_eternal_region (frameOf r)} (* type of unfreeable heap references allocated in regions *)

(** target_lang is a shallow embedding of STLC **)
class target_lang (t:Type) = {
  deep_contains : mem -> t -> Type0;
  has_frame : t -> rid -> Type0; (** shallow check of the region of a value **)
  regional : t -> mem -> rid -> Type0; (** deep check of the region of a value **)
  deep_recall : (r:t) -> Stack unit 
              (requires (fun h -> True))
              (ensures  (fun h0 _ h1 -> h0 == h1 /\ h1 `deep_contains` r))
}

instance target_lang_unit : target_lang unit = {
  deep_contains = (fun _ _ -> True);
  has_frame = (fun _ _ -> True);
  regional = (fun _ _ _ -> True);
  deep_recall = (fun _ -> ())
}

instance target_lang_int : target_lang int = {
  deep_contains = (fun _ _ -> True);
  has_frame = (fun _ _ -> True);
  regional = (fun _ _ _ -> True);
  deep_recall = (fun _ -> ());
}

instance target_lang_pair (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (t1 * t2) = {
  deep_contains = (fun h (x1, x2) -> h `deep_contains` x1 /\ h `deep_contains` x2);
  has_frame = (fun (x1, x2) rr -> x1 `has_frame` rr /\ x2 `has_frame` rr);
  regional = (fun (x1, x2) h rr -> c1.regional x1 h rr /\ c2.regional x2 h rr);
  deep_recall = (fun (x1, x2) -> c1.deep_recall x1; c2.deep_recall x2)
}

instance target_lang_sum (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (either t1 t2) = {
  deep_contains = (fun h x ->
    match x with
    | Inl x1 -> h `deep_contains` x1
    | Inr x2 -> h `deep_contains` x2);
  has_frame = (fun x rr ->
    match x with
    | Inl x1 -> x1 `has_frame` rr
    | Inr x2 -> x2 `has_frame` rr);
  regional = (fun x h rr ->
    match x with
    | Inl x1 -> c1.regional x1 h rr
    | Inr x2 -> c2.regional x2 h rr);
  deep_recall = (fun x ->
    match x with
    | Inl x1 -> c1.deep_recall x1
    | Inr x2 -> c2.deep_recall x2)
}

instance target_lang_ref (t:Type) {| c:target_lang t |} : target_lang (rref t) = {
  deep_contains = (fun h (x:rref t) -> h `contains` x /\ h `deep_contains` (sel h x));
  has_frame = (fun (x:rref t) rr -> frameOf x == rr);
  regional = (fun (x:rref t) h rr -> frameOf x == rr /\ c.regional (sel h x) h rr);  
  deep_recall = (fun (x:rref t) -> recall x; c.deep_recall !x)
}

let self_contained_region_inv (rr:erid) (h:mem) : Type0 =
  forall a (c:target_lang (rref a)) (r:rref a). h `contains` r /\ frameOf r == rr ==> 
    h `c.deep_contains` r /\ c.regional r h rr

unfold let pre_tgt_arrow
  (rrs:erid)
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (h0:mem) =
  h0 `deep_contains` x /\                                                 (* required to instantiate the properties of modifies *)
  regional x h0 rrs /\                                                    (* x is deeply in region rs *)
  self_contained_region_inv rrs h0 /\
  is_eternal_region rrs                                                   (* required for using ralloc *)

let post_tgt_arrow
  (rrs:erid)
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (#t2:t1 -> Type) {| tgtr : (x:t1 -> target_lang (t2 x)) |}
  (h0:mem) (r:t2 x) (h1:mem) =
  modifies (Set.singleton rrs) h0 h1 /\                                  (* allow region rs to be modified *)

  self_contained_region_inv rrs h1 /\

  (h1 `(tgtr x).deep_contains` r) /\
  ((tgtr x).regional r h1 rrs)                                           (* x is deeply in region rs *)
(* TODO: what prevents the computation to allocate things in rp?
    If necessary, we can dissable it by adding the following postcondition:
      forall rrp. disjoint rrp rrs ==> equal_heap_dom rrp h0 h1 -- disables allocation in other regions
 *)

let mk_tgt_arrow  
  (rrs:erid)
  (t1:Type)
  {| tgt_t1: target_lang t1 |}
  (t2:t1 -> Type) (* TODO: this dependency is not needed anymore *)
  {| c2 : (x:t1 -> target_lang (t2 x)) |}
= x:t1 -> ST (t2 x) 
    (requires (pre_tgt_arrow rrs x #tgt_t1))
    (ensures (post_tgt_arrow rrs x #tgt_t1 #t2 #c2))

instance target_lang_arrow 
  (rrs:erid)
  (t1:Type)
  {| target_lang t1 |}
  (t2:t1 -> Type)
  {| (x:t1 -> target_lang (t2 x)) |}
  : target_lang (mk_tgt_arrow rrs t1 t2) = {
    deep_contains = (fun _ _ -> True);
    has_frame = (fun _ _ -> True);
    regional = (fun _ _ _ -> True);
    deep_recall = (fun _ -> ())
  }

open STLC

(** *** Elaboration of types to F* *)
let rec _elab_typ (t:typ) (rrs:erid) : tt:Type & target_lang tt =
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
    (| rref tt, target_lang_ref tt #c_tt |)

let elab_typ (t:typ) (rrs:erid) : Type =
  dfst (_elab_typ t rrs)

let elab_typ_tgt (t:typ) (rrs:erid): target_lang (elab_typ t rrs)=
  dsnd (_elab_typ t rrs)



(** ** Examples **) 
let write' (#t:Type) {| c:target_lang t |} (r:rref t) (v:t) : ST unit
  (requires (fun h0 -> 
    h0 `deep_contains` r /\ h0 `c.deep_contains` v /\
    regional r h0 (frameOf r) /\ c.regional v h0 (frameOf r) /\
    self_contained_region_inv (frameOf r) h0))
  (ensures (fun h0 u h1 -> 
    assign_post r v h0 u h1 /\
    h1 `deep_contains` r /\
    regional r h1 (frameOf r) /\
    self_contained_region_inv (frameOf r) h1))
= 
  let h0 = get () in
  assert (forall a (c:target_lang (rref a)) (r':rref a). h0 `contains` r' /\ frameOf r' == frameOf r ==> 
    h0 `c.deep_contains` r' /\ c.regional r' h0 (frameOf r));
  r := v;
  let h1 = get () in
  assume (h1 `deep_contains` r);
  assume (regional r h1 (frameOf r));
  assume (forall a (c:target_lang (rref a)) (r':rref a). 
    h1 `contains` r' /\ frameOf r' == frameOf r ==> h1 `c.deep_contains` r' /\ c.regional r' h1 (frameOf r))


val ralloc' (#a:Type) {| c:target_lang a |} (i:erid) (init:a)
  :ST (rref a) (requires (fun m -> is_eternal_region i /\ c.regional init m i))
                    (ensures (fun h0 r h1 -> ralloc_post i init h0 r h1 /\ 
                      regional r h1 i /\
                      (forall (r:erid) . self_contained_region_inv r h0 ==> self_contained_region_inv r h1)
                    ))
let ralloc' #_ #c i v = 
  let h0 = get () in
  let r = ralloc i v in
  let h1 = get () in
  assume ((target_lang_ref _ #c).regional r h1 i);
  assume (forall (r:erid) . self_contained_region_inv r h0 ==> self_contained_region_inv r h1);
  r

let sep
  (#trp:Type) (rp:trp) {| tgt_rp: target_lang trp |}
  (rrp:erid)
  (#trs:Type) (rs:trs) {| tgt_rs: target_lang trs |}
  (rrs:erid)
  h =
  h `deep_contains` rp /\ h `deep_contains` rs /\           (* required to instantiate the properties of modifies *)                                            (* separation *)
  disjoint rrp rrs /\                                       (* ensures disjointness of regions *)
  regional rp h rrp /\ regional rs h rrs 

val ctx_update_ref_test : 
  #rrs:erid ->
  elab_typ (TArr (TRef TNat) TUnit) rrs
let ctx_update_ref_test (y:rref int) =
  write' y (!y + 5);
  ()

val ctx_update_multiple_refs_test : 
  #rrs:erid ->
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit)) rrs
let ctx_update_multiple_refs_test #rrs (x:rref (rref int)) (y:rref int) =
  deep_recall x; (* Fstar forgets that x is contained **)
  let ix = !x in
  write' ix (!ix + 1);
  write' x y;
  write' y (!y + 5);
  ()

val ctx_HO_test1 : 
  #rrs:erid ->
  elab_typ (TArr (TRef (TPair (TRef TNat) (TRef TNat))) (TArr TUnit TUnit)) rrs
let ctx_HO_test1 #rrs (xs:rref ((rref int) * rref int)) =
  let (x', x'') = !xs in
  write' xs (x', x');  // xs := (x', x');
  (fun () ->
    deep_recall xs;
    recall x';
    recall x'';
    write' xs (x', x'')
  )
  
val ctx_identity : 
  #rrs:erid ->
  elab_typ (TArr (TRef TNat) (TRef TNat)) rrs
let ctx_identity x = x

val ctx_HO_test2 : 
  #rrs:erid ->
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit) rrs
let ctx_HO_test2 f =
  let x:rref int = f () in
  write' x (!x + 1);
  ()

val ctx_swap_ref_test :
  #rrs:erid ->
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef (TRef TNat)) TUnit)) rrs
let ctx_swap_ref_test #rrs (x y: rref (rref int)) =
  deep_recall x;
  let z = !x in
  let t = !y in
  write' x t;
  write' y z;
  ()

val ctx_dynamic_alloc_test :
   #rrs:erid ->
   elab_typ (TArr TUnit (TRef TNat)) rrs
let ctx_dynamic_alloc_test #rrs () = 
  let v = ralloc' rrs 0 in 
  v

val ctx_HO_test3 :
  #rrs:erid ->
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit) rrs
let ctx_HO_test3 #rrs f =
  let x:rref int = f () in
  let y: rref int = ralloc' rrs (!x + 1) in
  ()

val ctx_returns_callback_test :
  #rrs:erid ->
  elab_typ (TArr TUnit (TArr TUnit TUnit)) rrs
let ctx_returns_callback_test #rrs () =
  let x: rref int = ralloc' rrs 13 in
   let cb : elab_typ (TArr TUnit TUnit) rrs = (fun() ->
     recall x;
     write' x (!x % 5)
   ) in
cb

val ctx_HO_test4 :
   #rrs:erid ->
   elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit) rrs
let ctx_HO_test4 #rrs f =
  let x:rref int = f () in
  let y: rref (rref int) = ralloc' rrs x in
  ()

val progr_sep_test: 
  #rp: rref int -> 
  #rs: rref (rref int) ->
  #rrs:erid ->
  #rrp:erid ->
  ctx:(elab_typ (TArr TUnit TUnit) rrs) ->
  ST unit 
    (requires (fun h0 -> 
      self_contained_region_inv rrs h0 /\
      sep rp rrp rs rrs h0 /\
      is_eternal_region rrs))
    (ensures (fun h0 _ h1 -> sep rp rrp rs rrs h1 /\
                            sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
         
let progr_sep_test #_ #rs #rrs f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  f ();
  deep_recall rs;
  ()

val progr_secret_unchanged_test: 
  #rp: rref int -> 
  #rs: rref (rref int) ->
  #rrs:erid ->
  #rrp:erid ->
  ctx:(elab_typ (TArr TUnit TUnit) rrs) ->
  ST unit 
    (requires (fun h0 -> 
      self_contained_region_inv rrs h0 /\
      sep rp rrp rs rrs h0 /\
      is_eternal_region rrs /\
      is_eternal_region rrp))
    (ensures (fun h0 _ h1 -> sep rp rrp rs rrs h1 /\
                             sel h0 rp == sel h1 rp))
         
let progr_secret_unchanged_test #_ #rs #rrs #rrp ctx = 
  let secret: rref int = ralloc' rrp 0 in
  ctx ();
  let v = !secret in
  assert (v == 0);
  deep_recall rs;
  ()

val progr_passing_callback_test: 
  #rp: rref int -> 
  #rs: rref (rref int) ->
  #rrs:erid ->
  #rrp:erid ->
  ctx:(elab_typ (TArr (TArr TUnit TUnit) TUnit) rrs) ->
  ST unit 
    (requires (fun h0 -> 
      self_contained_region_inv rrs h0 /\
      sep rp rrp rs rrs h0 /\
      is_eternal_region rrs))
    (ensures (fun h0 _ h1 -> sep rp rrp rs rrs h1 /\
                             sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context

// TODO: the callback of the program should be able to modify rp
let progr_passing_callback_test #_ #rs #rrs #rrp f =
  let secret: rref int = ralloc' rrs 0 in
  let cb: elab_typ (TArr TUnit TUnit) rrs = (fun () -> write' secret (!secret + 1)) in
  f cb;
  deep_recall rs;
  ()

val progr_getting_callback_test: 
  #rp: rref int -> 
  #rs: rref (rref int) ->
  #rrs:erid ->
  #rrp:erid ->
  ctx:(elab_typ (TArr TUnit (TArr TUnit TUnit)) rrs) ->
  ST unit 
    (requires (fun h0 -> 
      self_contained_region_inv rrs h0 /\
      sep rp rrp rs rrs h0 /\
      is_eternal_region rrs))
    (ensures (fun h0 _ h1 -> sep rp rrp rs rrs h1 /\
                             sel h0 rp == sel h1 rp))

let progr_getting_callback_test #_ #rs #rrs #rrp f =
  let cb = f () in
  cb ();
  deep_recall rs;
  ()

(** ** Elaboration of expressions to F* *)
let rec regional_implies_has_frame #rrs #t (x:elab_typ t rrs)
: Stack unit
    (requires (fun h0 ->
      (elab_typ_tgt t rrs).regional x h0 rrs))
    (ensures (fun h0 _ h1 -> h0 == h1 /\
      (elab_typ_tgt t rrs).has_frame x rrs))
= match t with
  | TArr t1 t2 -> ()
  | TUnit -> ()
  | TNat -> ()
  | TSum t1 t2 -> begin
      let x : either (elab_typ t1 rrs) (elab_typ t2 rrs) = x in
      match x with 
      | Inl x1 -> regional_implies_has_frame x1
      | Inr x2 -> regional_implies_has_frame x2
  end
  | TPair t1 t2 -> begin
      let (x1, x2) : (elab_typ t1 rrs * elab_typ t2 rrs) = x in
      regional_implies_has_frame x1;
      regional_implies_has_frame x2
  end
  | TRef t -> begin
      let x : rref (elab_typ t rrs) = x in
      ()
  end

let rec dcontains_in_self_contained_implies_regional #rrs #t (x:elab_typ t rrs)
: Stack unit
    (requires (fun h0 ->
      (elab_typ_tgt t rrs).has_frame x rrs
      /\ (elab_typ_tgt t rrs).deep_contains h0 x
      /\ self_contained_region_inv rrs h0
      ))
    (ensures (fun h0 _ h1 -> h0 == h1 /\
      (elab_typ_tgt t rrs).regional x h1 rrs))
= match t with
  | TArr t1 t2 -> ()
  | TUnit -> ()
  | TNat -> ()
  | TSum t1 t2 -> begin
      let x : either (elab_typ t1 rrs) (elab_typ t2 rrs) = x in
      match x with 
      | Inl x1 -> dcontains_in_self_contained_implies_regional x1
      | Inr x2 -> dcontains_in_self_contained_implies_regional x2
  end
  | TPair t1 t2 -> begin
      let (x1, x2) : (elab_typ t1 rrs * elab_typ t2 rrs) = x in
      dcontains_in_self_contained_implies_regional x1;
      dcontains_in_self_contained_implies_regional x2
  end
  | TRef t -> begin
      let x : rref (elab_typ t rrs) = x in
      ()
  end

val elab_apply_arrow :
  rrs:erid ->
  t1:typ ->
  t2:typ ->
  f:elab_typ (TArr t1 t2) rrs ->
  (let tt1 = _elab_typ t1 rrs in
   let tt2 (x:(dfst tt1)) = _elab_typ t2 rrs in
   mk_tgt_arrow rrs (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) #(fun x -> dsnd (tt2 x)))
let elab_apply_arrow rs t1 t2 f x = f x

unfold let elab_typ' rrs t = elab_typ t rrs
unfold let elab_typ_tgt' rrs t = elab_typ_tgt t rrs

let cast_TArr #t1 #t2 #rrs (f : elab_typ (TArr t1 t2) rrs) (t:typ) (#_:squash (t == TArr t1 t2)) : elab_typ t rrs = f

type vcontext (rrs:erid) (g:context) = 
  vx:var{Some? (g vx)} -> x:(elab_typ (Some?.v (g vx)) rrs){(elab_typ_tgt (Some?.v (g vx)) rrs).has_frame x rrs}

let vempty (rrs:erid) : vcontext rrs empty = fun _ -> assert false

let vextend #t rrs (x:(elab_typ t rrs){(elab_typ_tgt t rrs).has_frame x rrs}) (#g:context) (ve:vcontext rrs g) : vcontext rrs (extend t g) =
  fun y -> if y = 0 then x else ve (y-1)

#push-options "--split_queries always"
let rec elab_exp 
  (rrs:erid)
  (#g:context)
  (#e:exp) 
  (#t:typ)
  (tyj:typing g e t)
  (ve:vcontext rrs g)
  : ST (elab_typ t rrs) 
     (requires (pre_tgt_arrow rrs () #target_lang_unit))
     (ensures (post_tgt_arrow rrs () #_ #(fun _ -> elab_typ t rrs) #(fun _ -> elab_typ_tgt t rrs)))
     (decreases e) =
  let elab_exp #g #e #t = elab_exp rrs #g #e #t in
  let elab_typ = elab_typ' rrs in
  let elab_typ_tgt = elab_typ_tgt' rrs in
  let h0 = get () in
  match tyj with
  | TyUnit -> ()
  | TyZero -> 0
  | TySucc tyj_s -> 
    1 + (elab_exp tyj_s ve)

  | TyAllocRef #_ #_ #t tyj_e -> begin
    let v : elab_typ t = elab_exp tyj_e ve in
    let r = ralloc' #_ #(elab_typ_tgt t) rrs v in
    r
  end
  | TyReadRef #_ #_ #t tyj_e -> begin
    let r : ref (elab_typ t) = elab_exp tyj_e ve in
    !r
  end
  | TyWriteRef #_ #_ #_ #t tyj_ref tyj_v -> begin
      let r : ref (elab_typ t) = elab_exp tyj_ref ve in
      let v : elab_typ t = elab_exp tyj_v ve in
      recall r;
      write' #_ #(elab_typ_tgt t) r v
  end

  | TyAbs tx #_ #tres tyj_body ->
    let w : mk_tgt_arrow rrs (elab_typ tx) #(elab_typ_tgt tx) (fun x -> elab_typ tres) #(fun x -> elab_typ_tgt tres) = 
      (fun (x:elab_typ tx) -> 
        regional_implies_has_frame #rrs #tx x; 
        elab_exp tyj_body (vextend #tx rrs x ve))
    in
    assert (t == TArr tx tres);
    cast_TArr #tx #tres #rrs w t
  | TyVar vx -> 
    let Some tx = g vx in
    let x : elab_typ tx = ve vx in
    (elab_typ_tgt tx).deep_recall x;
    dcontains_in_self_contained_implies_regional #rrs #tx x;
    x
  | TyApp #_ #_ #_ #tx #tres tyj_f tyj_x ->
    assert ((elab_typ t) == (elab_typ tres));
    let x : elab_typ tx = elab_exp tyj_x ve in
    regional_implies_has_frame #rrs #tx x;
    let f : elab_typ (TArr tx tres) = elab_exp tyj_f ve in
    (elab_typ_tgt tx).deep_recall x;
    dcontains_in_self_contained_implies_regional #rrs #tx x;
    elab_apply_arrow rrs tx tres f x

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
      regional_implies_has_frame #rrs #tl x;
      let f : elab_typ (TArr tl tres) = elab_exp tyj_l ve in
      (elab_typ_tgt tl).deep_recall x;
      dcontains_in_self_contained_implies_regional #rrs #tl x;
      elab_apply_arrow rrs tl tres f x
    | Inr y ->
      regional_implies_has_frame #rrs #tr y;
      let f : elab_typ (TArr tr tres) = elab_exp tyj_r ve in
      (elab_typ_tgt tr).deep_recall y;
      dcontains_in_self_contained_implies_regional #rrs #tr y;
      elab_apply_arrow rrs tr tres f y
  end

  | TyFst #_ #_ #tf #ts tyj_e ->
    let v = elab_exp tyj_e ve in
    fst #(elab_typ tf) #(elab_typ ts) v
  | TySnd #_ #_ #tf #ts tyj_e ->
    let v = elab_exp tyj_e ve in
    snd #(elab_typ tf) #(elab_typ ts) v
  | TyPair #_ #_ #_ #tf #ts tyj_f tyj_s->
    let vf : elab_typ tf = elab_exp tyj_f ve in
    regional_implies_has_frame #rrs #tf vf;
    let vs : elab_typ ts = elab_exp tyj_s ve in
    (elab_typ_tgt tf).deep_recall vf;
    dcontains_in_self_contained_implies_regional #rrs #tf vf;
    (vf, vs)
  #pop-options