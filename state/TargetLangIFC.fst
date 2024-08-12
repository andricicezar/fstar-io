module TargetLangIFC

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses

open Monotonic.IFC.Heap
open IFC.Heap.ST


let prog () =
  let r : ref int = alloc 0 in
  let h0 = get () in
  assert (label_of r h0 == High);
  declassify r Low;
  assert (label_of r h0 == High);
  let h1 = get () in
  assert (label_of r h1 == Low);
  let r1 : ref int = alloc 0 in
  declassify r1 Medium;
  ()

(** target_lang is a shallow embedding of STLC **)
class target_lang (t:Type) = {
  witnessed_with_low : t -> Type0;
}
  
instance target_lang_unit : target_lang unit = {
  witnessed_with_low = (fun _ -> True);
}

instance target_lang_int : target_lang int = {
  witnessed_with_low = (fun _ -> True);
}

instance target_lang_pair (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (t1 * t2) = {
  witnessed_with_low = (fun (x1, x2) -> c1.witnessed_with_low x1 /\ c2.witnessed_with_low x2);
}

instance target_lang_sum (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (either t1 t2) = {
  witnessed_with_low = (fun x ->
    match x with
    | Inl x1 -> c1.witnessed_with_low x1
    | Inr x2 -> c2.witnessed_with_low x2);
}

instance target_lang_ref (t:Type) {| c:target_lang t |} : target_lang (ref t) = {
  witnessed_with_low = (fun (x:ref t) -> witnessed (is_low_pred x));
}

open FStar.Preorder

let inv_low_points_to_low (h:lheap) =
  forall (a:Type) (c:target_lang a) (r:ref a). witnessed (is_low_pred r) ==>
    c.witnessed_with_low (sel h r)

effect IST (a:Type) (pre:st_pre) (post: (h:lheap -> Tot (st_post' a (pre h)))) =
  ST a 
    (requires (fun h0 -> 
      inv_low_points_to_low h0 /\
      pre h0))
    (ensures (fun h0 r h1 ->
      inv_low_points_to_low h1 /\
      post h0 r h1))

let alloc (#a:Type) (#rel:preorder a) (init:a)
: IST (mref a rel) (fun h -> True) (alloc_post #a #rel init)
=
  let r = alloc init in
  let h1 = get () in
  assume (inv_low_points_to_low h1);
  r

unfold let pre_tgt_arrow
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (h0:lheap) =
  witnessed_with_low x                                           (* x is Low *)

let post_tgt_arrow
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (#t2:t1 -> Type) {| tgtr : (x:t1 -> target_lang (t2 x)) |}
  (h0:lheap) (r:t2 x) (h1:lheap) =
  modifies_only_label Low h0 h1 /\                                       (* allows low references to be modified *)
  modifies_classification Set.empty h0 h1 /\                             (* no modifications of the classification *)

  ((tgtr x).witnessed_with_low r)                                (* r is deeply labeled with Low *)

let mk_tgt_arrow 
  (t1:Type)
  {| tgt_t1: target_lang t1 |}
  (t2:t1 -> Type) (* TODO: this dependency is not needed anymore *)
  {| c2 : (x:t1 -> target_lang (t2 x)) |}
= x:t1 -> IST (t2 x) 
    (requires (pre_tgt_arrow x #tgt_t1))
    (ensures (post_tgt_arrow x #tgt_t1 #t2 #c2))

instance target_lang_arrow 
  (t1:Type)
  {| target_lang t1 |}
  (t2:t1 -> Type)
  {| (x:t1 -> target_lang (t2 x)) |}
  : target_lang (mk_tgt_arrow t1 t2) = {
    witnessed_with_low = (fun _ -> True);
  }


open STLC

(** *** Elaboration of types to F* *)
let rec _elab_typ (t:typ) : tt:Type & target_lang tt =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = _elab_typ t1 in
    let tt2 (x:dfst tt1) = _elab_typ t2 in
    (| mk_tgt_arrow      (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) #(fun x -> dsnd (tt2 x)),
       target_lang_arrow (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) #(fun x -> dsnd (tt2 x))
    |)
  end 
  | TUnit -> (| unit, target_lang_unit |)
  | TNat -> (| int, target_lang_int |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 in
    let (| tt2, c_tt2 |) = _elab_typ t2 in
    (| either tt1 tt2, target_lang_sum tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 in
    let (| tt2, c_tt2 |) = _elab_typ t2 in
    (| (tt1 * tt2), target_lang_pair tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef t ->
    let (| tt, c_tt |) = _elab_typ t in
    (| ref tt, target_lang_ref tt #c_tt |)

let elab_typ (t:typ) : Type =
  dfst (_elab_typ t)

let elab_typ_tgt (t:typ) : target_lang (elab_typ t)=
  dsnd (_elab_typ t)



(** ** Examples **) 
let write' (#t:Type) {| c:target_lang t |} (r:ref t) (v:t) 
: IST unit
  (requires (fun h0 -> 
    witnessed (is_low_pred r) /\
    c.witnessed_with_low v))
  (ensures (fun h0 () h1 ->
    write_post r v h0 () h1 /\
    modifies_only_label Low h0 h1 /\
    witnessed_with_low r))
= let h0 = get () in
  gst_recall (is_low_pred r);
  recall r;
  r := v;
  let h1 = get () in
  assume (inv_low_points_to_low h1);
  ()


val alloc' (#a:Type) {| c:target_lang a |} (init:a)
: IST (ref a)
  (requires (fun h0 -> 
    c.witnessed_with_low init))
  (ensures (fun h0 r h1 -> 
    fresh r h0 h1 /\ 
    modifies Set.empty h0 h1 /\
    modifies_classification Set.empty h0 h1 /\
    sel h1 r == init /\ 
    witnessed_with_low r))
let alloc' #_ #c init = 
  let r = alloc init in
  declassify r Low;
  gst_witness (is_low_pred r);
  r

val ctx_update_ref_test : 
  elab_typ (TArr (TRef TNat) TUnit)
let ctx_update_ref_test (y:ref int) =
  write' y (!y + 5);
  ()

val ctx_update_multiple_refs_test : 
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit))
let ctx_update_multiple_refs_test (x:ref (ref int)) (y:ref int) =
  let ix : ref int = !x in
  let h0 = get () in
  eliminate forall (a:Type) (c:target_lang a) (r:ref a). witnessed (is_low_pred r) ==>
    c.witnessed_with_low (sel h0 r) with (ref int) (solve) x;
  write' ix (!ix + 1);
  write' x y;
  write' y (!y + 5);
  ()

val ctx_HO_test1 : 
  elab_typ (TArr (TRef (TPair (TRef TNat) (TRef TNat))) (TArr TUnit TUnit))
let ctx_HO_test1 (xs:ref ((ref int) * ref int)) =
  let (x', x'') = !xs in
  let h0 = get () in
  eliminate forall (a:Type) (c:target_lang a) (r:ref a). witnessed (is_low_pred r) ==>
    c.witnessed_with_low (sel h0 r) with ((ref int) * (ref int)) (solve) xs;
  write' xs (x', x');  // xs := (x', x');
  (fun () -> write' xs (x', x''))
  
val ctx_identity :
  elab_typ (TArr (TRef TNat) (TRef TNat))
let ctx_identity x = x

val ctx_HO_test2 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test2 f =
  let h0 = get () in
  let x:ref int = f () in
  let h1 = get () in
  write' x (!x + 1);
  let h2 = get () in
  assert (modifies_only_label Low h0 h2);
  ()

val ctx_swap_ref_test :
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef (TRef TNat)) TUnit))
let ctx_swap_ref_test (x y: ref (ref int)) =
  let h0 = get () in
  eliminate forall (a:Type) (c:target_lang a) (r:ref a). witnessed (is_low_pred r) ==>
    c.witnessed_with_low (sel h0 r) with (ref int) (solve) x;
  let z = !x in
  let t = !y in
  write' x t;
  write' y z;
  ()

val ctx_dynamic_alloc_test :
   elab_typ (TArr TUnit (TRef TNat))
let ctx_dynamic_alloc_test () = 
  let v = alloc' 0 in 
  v

val ctx_HO_test3 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test3 f =
  let x:ref int = f () in
  let y:ref int = alloc' (!x + 1) in
  ()

val ctx_returns_callback_test :
  elab_typ (TArr TUnit (TArr TUnit TUnit))
let ctx_returns_callback_test () =
  let x: ref int = alloc' 13 in
  let cb : elab_typ (TArr TUnit TUnit) = (fun() ->
    write' x (!x % 5)
  ) in
  cb

val ctx_HO_test4 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test4 f =
  let x:ref int = f () in
  let y:ref (ref int) = alloc' x in
  ()

val progr_sep_test: 
  #rp: ref int -> 
  ctx:(elab_typ (TArr TUnit TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      inv_low_points_to_low h0 /\
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
         
let progr_sep_test #rp f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  recall rp;
  f ()

val progr_sep_test_alloc:
  #rp: ref int -> 
  ctx:(elab_typ (TArr (TRef TNat) TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 -> True))
let progr_sep_test_alloc #rp f =
  f (declassify_low rp)

val progr_sep_test_nested:
  rp: ref (ref int) -> 
  ctx:(elab_typ (TArr (TRef (TRef TNat)) TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 -> True))
let progr_sep_test_nested rp f =
  declassify rp Low; gst_witness (is_low_pred rp);
  let p = !rp in
  declassify p Low; gst_witness (is_low_pred p);
  // let r = alloc' (!rp) in (* <-- needed a copy here! *) 
  f rp

val progr_secret_unchanged_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr TUnit TUnit)) ->
  IST unit 
    (requires (fun h0 -> 
      label_of rp h0 == High /\
      witnessed (is_low_pred rs)))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp))
         
let progr_secret_unchanged_test rp rs ctx = 
  recall rp; (* This has to be very precisely here! *)
  let secret: ref int = alloc 0 in
  ctx ();
  let v = !secret in
  assert (v == 0);
  ()

val progr_passing_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr (TArr TUnit TUnit) TUnit)) ->
  IST unit 
    (requires (fun h0 ->
      label_of rp h0 == High /\
      witnessed (is_low_pred rs)))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context

// TODO: the callback of the program should be able to modify rp
let progr_passing_callback_test rp rs f =
  recall rp;
  let secret: ref int = alloc 0 in
  declassify secret Low; gst_witness (is_low_pred secret);
  let cb: elab_typ (TArr TUnit TUnit) = (fun () -> 
    gst_recall (is_low_pred secret);
    write' secret (!secret + 1)) in
  f cb;
  ()

val progr_getting_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr TUnit (TArr TUnit TUnit))) ->
  IST unit 
    (requires (fun h0 ->
      label_of rp h0 == High /\
      witnessed (is_low_pred rs)))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp))
let progr_getting_callback_test rp rs f =
  recall rp;
  let h0 = get () in
  let cb = f () in
  cb ();
  let h2 = get () in
  assert (modifies_only_label Low h0 h2);
  ()

(** ** Elaboration of expressions to F* *)
val elab_apply_arrow :
  t1:typ ->
  t2:typ ->
  f:elab_typ (TArr t1 t2) ->
  (let tt1 = _elab_typ t1 in
   let tt2 (x:(dfst tt1)) = _elab_typ t2 in
   mk_tgt_arrow (dfst tt1) #(dsnd tt1) (fun x -> dfst (tt2 x)) #(fun x -> dsnd (tt2 x)))
let elab_apply_arrow t1 t2 f x = f x

let cast_TArr #t1 #t2 (f : elab_typ (TArr t1 t2)) (t:typ) (#_:squash (t == TArr t1 t2)) : elab_typ t = f

type vcontext (g:context) = 
  vx:var{Some? (g vx)} -> x:(elab_typ (Some?.v (g vx))){(elab_typ_tgt (Some?.v (g vx))).witnessed_with_low x}

let vempty : vcontext empty = fun _ -> assert false

let vextend #t (x:(elab_typ t){(elab_typ_tgt t).witnessed_with_low x}) (#g:context) (ve:vcontext g) : vcontext (extend t g) =
  fun y -> if y = 0 then x else ve (y-1)

#push-options "--split_queries always"
let rec elab_exp 
  (#g:context)
  (#e:exp) 
  (#t:typ)
  (tyj:typing g e t)
  (ve:vcontext g)
  : IST (elab_typ t) 
     (requires (pre_tgt_arrow () #target_lang_unit))
     (ensures (post_tgt_arrow () #_ #(fun _ -> elab_typ t) #(fun _ -> elab_typ_tgt t))) =
  let h0 = get () in
  match tyj with
  | TyUnit -> ()
  | TyZero -> 0
  | TySucc tyj_s -> 
    1 + (elab_exp tyj_s ve)

  | TyAllocRef #_ #_ #t tyj_e -> begin
    let v : elab_typ t = elab_exp tyj_e ve in
    let r : ref (elab_typ t) = alloc' #_ #(elab_typ_tgt t) v in
    r
  end
  | TyReadRef #_ #_ #t tyj_e -> begin
    let r : ref (elab_typ t) = elab_exp tyj_e ve in
    !r
  end
  | TyWriteRef #_ #_ #_ #t tyj_ref tyj_v -> begin
      let r : ref (elab_typ t) = elab_exp tyj_ref ve in
      let v : elab_typ t = elab_exp tyj_v ve in
      write' #_ #(elab_typ_tgt t) r v
  end

  | TyAbs tx #_ #tres tyj_body ->
    let w : mk_tgt_arrow (elab_typ tx) #(elab_typ_tgt tx) (fun x -> elab_typ tres) #(fun x -> elab_typ_tgt tres) = 
      (fun (x:elab_typ tx) -> 
        elab_exp tyj_body (vextend #tx x ve))
    in
    assert (t == TArr tx tres);
    cast_TArr #tx #tres w t
  | TyVar vx -> 
    let Some tx = g vx in
    let x : elab_typ tx = ve vx in
    x
  | TyApp #_ #_ #_ #tx #tres tyj_f tyj_x ->
    assert ((elab_typ t) == (elab_typ tres));
    let x : elab_typ tx = elab_exp tyj_x ve in
    let f : elab_typ (TArr tx tres) = elab_exp tyj_f ve in
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
      let f : elab_typ (TArr tl tres) = elab_exp tyj_l ve in
      elab_apply_arrow tl tres f x
    | Inr y ->
      let f : elab_typ (TArr tr tres) = elab_exp tyj_r ve in
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
    let vs : elab_typ ts = elab_exp tyj_s ve in
    (vf, vs)
#pop-options
