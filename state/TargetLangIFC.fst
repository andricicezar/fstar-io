module TargetLangIFC

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses

open Monotonic.IFC.Heap
open IFC.Heap.ST

(** target_lang is a shallow embedding of STLC **)
class target_lang (t:Type) = {
  deep_contains : lheap -> t -> Type0;
  deeply_labeled_with_low : t -> lheap -> Type0; (** deep check that the object points to low things **)

  deep_recall : (r:t) -> ST unit 
              (requires (fun h -> True))
              (ensures  (fun h0 _ h1 -> h0 == h1 /\ h1 `deep_contains` r /\ deeply_labeled_with_low r h1));  
}
  
instance target_lang_unit : target_lang unit = {
  deep_contains = (fun _ _ -> True);
  deep_recall = (fun _ -> ());

  deeply_labeled_with_low = (fun _ _ -> True);
}

instance target_lang_int : target_lang int = {
  deep_contains = (fun _ _ -> True);
  deep_recall = (fun _ -> ());

  deeply_labeled_with_low = (fun _ _ -> True);
}

instance target_lang_pair (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (t1 * t2) = {
  deep_contains = (fun h (x1, x2) -> h `deep_contains` x1 /\ h `deep_contains` x2);
  deep_recall = (fun (x1, x2) -> c1.deep_recall x1; c2.deep_recall x2);

  deeply_labeled_with_low = (fun (x1, x2) h -> c1.deeply_labeled_with_low x1 h /\ c2.deeply_labeled_with_low x2 h);
}

instance target_lang_sum (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (either t1 t2) = {
  deep_contains = (fun h x ->
    match x with
    | Inl x1 -> h `deep_contains` x1
    | Inr x2 -> h `deep_contains` x2);
  deep_recall = (fun x ->
    match x with
    | Inl x1 -> c1.deep_recall x1
    | Inr x2 -> c2.deep_recall x2);

  deeply_labeled_with_low = (fun x h ->
    match x with
    | Inl x1 -> c1.deeply_labeled_with_low x1 h
    | Inr x2 -> c2.deeply_labeled_with_low x2 h);
}

instance target_lang_ref (t:Type) {| c:target_lang t |} : target_lang (lref t) = {
  deep_contains = (fun h (x:lref t) -> h `contains` x /\ h `deep_contains` (sel h x));

  deeply_labeled_with_low = (fun (x:lref t) h -> label_of x h == Low /\ c.deeply_labeled_with_low (sel h x) h);  
  deep_recall = (fun (x:lref t) -> 
    recall x; 
    gst_recall (is_low_pred x);
    c.deep_recall !x);
}

open FStar.Preorder

unfold let pre_tgt_arrow
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (h0:lheap) =
  h0 `deep_contains` x /\                                                (* required to instantiate the properties of modifies *)
  deeply_labeled_with_low x h0                                           (* x is Low *)

let post_tgt_arrow
  (#t1:Type) (x:t1) {| tgtx:target_lang t1 |}
  (#t2:t1 -> Type) {| tgtr : (x:t1 -> target_lang (t2 x)) |}
  (h0:lheap) (r:t2 x) (h1:lheap) =
  modifies_only_label Low h0 h1 /\                                       (* allows low references to be modified *)
  modifies_classification Set.empty h0 h1 /\                             (* no modifications of the classification *)

  (h1 `(tgtr x).deep_contains` r) /\
  ((tgtr x).deeply_labeled_with_low r h1)                                (* r is deeply labeled with Low *)

let mk_tgt_arrow 
  (t1:Type)
  {| tgt_t1: target_lang t1 |}
  (t2:t1 -> Type) (* TODO: this dependency is not needed anymore *)
  {| c2 : (x:t1 -> target_lang (t2 x)) |}
= x:t1 -> ST (t2 x) 
    (requires (pre_tgt_arrow x #tgt_t1))
    (ensures (post_tgt_arrow x #tgt_t1 #t2 #c2))

instance target_lang_arrow 
  (t1:Type)
  {| target_lang t1 |}
  (t2:t1 -> Type)
  {| (x:t1 -> target_lang (t2 x)) |}
  : target_lang (mk_tgt_arrow t1 t2) = {
    deep_contains = (fun _ _ -> True);
    deep_recall = (fun _ -> ());

    deeply_labeled_with_low = (fun _ _ -> True);
  }

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
    (| lref tt, target_lang_ref tt #c_tt |)

let elab_typ (t:typ) : Type =
  dfst (_elab_typ t)

let elab_typ_tgt (t:typ) : target_lang (elab_typ t)=
  dsnd (_elab_typ t)



(** ** Examples **) 
let write' (#t:Type) {| c:target_lang t |} (r:lref t) (v:t) 
: ST unit
  (requires (fun h0 -> 
    h0 `deep_contains` r /\ 
    h0 `c.deep_contains` v /\
    label_of r h0 == Low /\ 
    c.deeply_labeled_with_low v h0))
  (ensures (fun h0 () h1 ->
    write_post r v h0 () h1 /\
    modifies_only_label Low h0 h1 /\
    deeply_labeled_with_low r h1))
= let h0 = get () in
  r := v;
  let h1 = get () in
  assume (deeply_labeled_with_low r h1);
  ()


val alloc' (#a:Type) {| c:target_lang a |} (init:a)
: ST (lref a)
  (requires (fun h0 ->
    c.deeply_labeled_with_low init h0
    ))
  (ensures (fun h0 r h1 -> 
    fresh r h0 h1 /\ 
    modifies Set.empty h0 h1 /\
    modifies_classification Set.empty h0 h1 /\
    sel h1 r == init /\ 
    deeply_labeled_with_low r h1
    ))
let alloc' #_ #c init = 
  let r = alloc init in
  let r' = declassify_low r in
  let h1 = get () in
  assume (deeply_labeled_with_low r' h1);
  r'

val ctx_update_ref_test : 
  elab_typ (TArr (TRef TNat) TUnit)
let ctx_update_ref_test (y:lref int) =
  write' y (!y + 5);
  ()

val ctx_update_multiple_refs_test : 
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit))
let ctx_update_multiple_refs_test (x:lref (lref int)) (y:lref int) =
  deep_recall x; (* Fstar forgets that x is contained and low **)
  let ix : lref int = !x in
  write' ix (!ix + 1);
  deep_recall x; (* TODO: why is this one needed? *)
  write' x y;
  write' y (!y + 5);
  ()

val ctx_HO_test1 : 
  elab_typ (TArr (TRef (TPair (TRef TNat) (TRef TNat))) (TArr TUnit TUnit))
let ctx_HO_test1 (xs:lref ((lref int) * lref int)) =
  let (x', x'') = !xs in
  write' xs (x', x');  // xs := (x', x');
  (fun () ->
    deep_recall xs;
    deep_recall x';
    deep_recall x'';
    write' xs (x', x'')
  )
  
val ctx_identity :
  elab_typ (TArr (TRef TNat) (TRef TNat))
let ctx_identity x = x

val ctx_HO_test2 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test2 f =
  let h0 = get () in
  let x:lref int = f () in
  let h1 = get () in
  // assert (lheap_rel h0 h1);
  // assert (modifies_only_label Low h0 h1);
  write' x (!x + 1);
  let h2 = get () in
  // assert (modifies_only_label Low h1 h2);
  // assert (objects_deeply_labeled h2);
  assume (modifies_only_label Low h0 h2);
  ()

val ctx_swap_ref_test :
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef (TRef TNat)) TUnit))
let ctx_swap_ref_test (x y: lref (lref int)) =
  deep_recall x;
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
  let x:lref int = f () in
  let y:lref int = alloc' (!x + 1) in
  ()

val ctx_returns_callback_test :
  elab_typ (TArr TUnit (TArr TUnit TUnit))
let ctx_returns_callback_test () =
  let x: lref int = alloc' 13 in
  let cb : elab_typ (TArr TUnit TUnit) = (fun() ->
    deep_recall x;
    let h0 = get () in
    write' x (!x % 5)
  ) in
  cb

val ctx_HO_test4 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test4 f =
  let x:lref int = f () in
  let y:lref (lref int) = alloc' x in
  ()

val progr_sep_test: 
  #rp: ref int -> 
  ctx:(elab_typ (TArr TUnit TUnit)) ->
  ST unit
    (requires (fun h0 -> 
      h0 `contains` rp /\
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
         
let progr_sep_test #rp f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  f ()

val progr_secret_unchanged_test: 
  #rp: ref int -> 
  #rs: lref (lref int) ->
  ctx:(elab_typ (TArr TUnit TUnit)) ->
  ST unit 
    (requires (fun h0 -> 
      h0 `contains` rp /\
      h0 `deep_contains` rs /\
      label_of rp h0 == High /\
      deeply_labeled_with_low rs h0))
    (ensures (fun h0 _ h1 -> 
      sel h0 rp == sel h1 rp))
         
let progr_secret_unchanged_test #_ #rs ctx = 
  let secret: ref int = alloc 0 in
  ctx ();
  let v = !secret in
  assert (v == 0);
  ()

val progr_passing_callback_test: 
  #rp: ref int -> 
  #rs: lref (lref int) ->
  ctx:(elab_typ (TArr (TArr TUnit TUnit) TUnit)) ->
  ST unit 
    (requires (fun h0 -> 
      h0 `contains` rp /\
      h0 `deep_contains` rs /\
      label_of rp h0 == High /\
      deeply_labeled_with_low rs h0))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context

// TODO: the callback of the program should be able to modify rp
let progr_passing_callback_test #_ #rs f =
  let secret: lref int = alloc' 0 in
  let cb: elab_typ (TArr TUnit TUnit) = (fun () -> deep_recall secret; write' secret (!secret + 1)) in
  f cb;
  ()

val progr_getting_callback_test: 
  #rp: ref int -> 
  #rs: lref (lref int) ->
  ctx:(elab_typ (TArr TUnit (TArr TUnit TUnit))) ->
  ST unit 
    (requires (fun h0 -> 
      h0 `contains` rp /\
      h0 `deep_contains` rs /\
      label_of rp h0 == High /\
      deeply_labeled_with_low rs h0))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp))

let progr_getting_callback_test #_ #rs f =
  let h0 = get () in
  let cb = f () in
  cb ();
  let h2 = get () in
  assume (modifies_only_label Low h0 h2);
  ()