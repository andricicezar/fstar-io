module TargetLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open SharedRefs
open Witnessable

open STLC

let rec to_shareable_typ (t:typ0) : shareable_typ =
  match t with
  | TUnit -> SUnit
  | TNat -> SNat
  | TSum t1 t2 -> SSum (to_shareable_typ t1) (to_shareable_typ t2)
  | TPair t1 t2 -> SPair (to_shareable_typ t1) (to_shareable_typ t2)
  | TRef t -> SRef (to_shareable_typ t)
  | TLList t -> SLList (to_shareable_typ t)

unfold
let elab_typ0 (t:typ0) : Type u#0 = 
  to_Type (to_shareable_typ t)

let rec elab_typ0_tc (t:typ0) : witnessable (elab_typ0 t) = 
  match t with
  | TUnit -> witnessable_unit
  | TNat -> witnessable_int
  | TSum t1 t2 -> witnessable_sum _ _ #(elab_typ0_tc t1) #(elab_typ0_tc t2)
  | TPair t1 t2 -> witnessable_pair _ _ #(elab_typ0_tc t1) #(elab_typ0_tc t2)
  | TRef t -> witnessable_ref _ #(elab_typ0_tc t) 
  | TLList t -> witnessable_llist _ #(elab_typ0_tc t)

unfold let pre_tgt_arrow
  (#t1:Type) {| c1 : witnessable t1 |}
  (x:t1) =
  sst_pre (fun h0 ->
    c1.satisfy x h0 contains_pred /\
    c1.satisfy x h0 is_shared)

unfold let post_tgt_arrow
  (#t1:Type) {| c1 : witnessable t1 |}
  (#t2:Type) {| c2 : witnessable t2 |}
  (x:t1) =
  sst_post t2 (pre_tgt_arrow #t1 #c1 x) (fun h0 r h1 -> 
    modifies_only_shared h0 h1 /\     (* allows shared references to be modified and to alloc new reference and share them *)
    gets_shared Set.empty h0 h1 /\
    c2.satisfy r h1 contains_pred /\
    c2.satisfy r h1 is_shared)

let mk_tgt_arrow
  (t1:Type) {| c1 : witnessable t1 |}
  (t2:Type) {| c2 : witnessable t2 |}
= x:t1 -> ST t2 
    (requires (pre_tgt_arrow #t1 #c1 x ))
    (ensures (post_tgt_arrow #t1 #c1 #t2 #c2 x))

let rec lemma_123 (#t:typ0) (v:elab_typ0 t) h pred :
  Lemma ((elab_typ0_tc t).satisfy v h pred <==> forallRefsHeap pred h #(to_shareable_typ t) v) 
  // [SMTPat ((elab_typ0_tc t).satisfy v h pred); SMTPat (forallRefsHeap pred h #(to_shareable_typ t) v)]
  by (compute ()) =
  match t with
  | TUnit -> ()
  | TNat -> ()
  | TSum t1 t2 -> begin
    let v : either (elab_typ0 t1) (elab_typ0 t2) = v in
    match v with
    | Inl lv -> lemma_123 lv h pred
    | Inr rv -> lemma_123 rv h pred
  end
  | TPair t1 t2 -> begin
     let v : (elab_typ0 t1) * (elab_typ0 t2) = v in
     lemma_123 (fst v) h pred;
     lemma_123 (snd v) h pred;
     assert ((elab_typ0_tc t).satisfy v h pred <==> forallRefsHeap pred h #(to_shareable_typ t) v)
  end
  | TRef t' -> 
    let aux (#t':typ0) (v:elab_typ0 (TRef t')) : ref (elab_typ0 t') = v in
    let v : ref (elab_typ0 t') = aux v in
    assert ((elab_typ0_tc t).satisfy v h pred <==> forallRefsHeap pred h #(to_shareable_typ t) v) by (compute ())
  | TLList t' -> begin
    let aux (#t':typ0) (v:elab_typ0 (TLList t')) : linkedList (elab_typ0 t') = v in
    let v : linkedList (elab_typ0 t') = aux v in
    match v with
    | LLNil -> ()
    | LLCons v' xsref -> (
      lemma_123 v' h pred;
      let xsref : ref (linkedList (elab_typ0 t')) = xsref in
      assert ((elab_typ0_tc t).satisfy v h pred <==> forallRefsHeap pred h #(to_shareable_typ t) v))
  end

open FStar.Universe

let rec _elab_typ (t:typ) : tt:Type u#1 & witnessable tt =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = _elab_typ t1 in
    let tt2 = _elab_typ t2 in
    (| mk_tgt_arrow (dfst tt1) #(dsnd tt1) (dfst tt2) #(dsnd tt2),
       witnessable_arrow (dfst tt1) (dfst tt2) (pre_tgt_arrow) (post_tgt_arrow)
    |)
  end 
  | TUnit -> (| raise_t unit, solve |)
  | TNat -> (| raise_t int, solve |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 in
    let (| tt2, c_tt2 |) = _elab_typ t2 in
    (| either tt1 tt2, witnessable_sum tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 in
    let (| tt2, c_tt2 |) = _elab_typ t2 in
    (| tt1 * tt2, witnessable_pair tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef _ ->
    let tt = elab_typ0 t in
    let c_tt = elab_typ0_tc t in
    (| raise_t tt, witnessable_univ_raise _ #c_tt |)
  | TLList t ->
    let tt = elab_typ0 t in
    let c_tt = elab_typ0_tc t in
    (| raise_t (linkedList tt), witnessable_univ_raise _ #(witnessable_llist tt #c_tt) |)

let elab_typ (t:typ) : Type =
  dfst (_elab_typ t)

let elab_typ_tc (t:typ) : witnessable (elab_typ t) =
  dsnd (_elab_typ t)

(** ** Examples **) 

val ctx_update_ref_test : 
  elab_typ (TArr (TRef TNat) TUnit)
let ctx_update_ref_test y =
  let y : ref int = downgrade_val y in
  sst_write #SNat y (sst_read y + 1);
  raise_val ()

val ctx_update_multiple_refs_test : 
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit))
let ctx_update_multiple_refs_test x =
  let x : ref (ref int) = downgrade_val x in
  witness (contains_pred x);
  witness (is_shared x);
  let cb : elab_typ (TArr (TRef TNat) TUnit) = (fun y ->
    let y : ref int = downgrade_val y in
    recall (contains_pred x);
    let ix : ref int = sst_read #(SRef SNat) x in
    recall (is_shared x);   
    sst_write #SNat ix (sst_read ix + 1);
    sst_write #(SRef SNat) x y;
    sst_write #SNat y (sst_read y + 5);
    raise_val () 
  ) in
  cb

val ctx_HO_test1 : 
  elab_typ (TArr (TRef (TPair (TRef TNat) (TRef TNat))) (TArr TUnit TUnit))
let ctx_HO_test1 xs =
  let h0 = get () in
  let xs : ref ((ref int) * ref int) = downgrade_val xs in
  let (x', x'') : (ref int) * ref int = sst_read #(SPair (SRef SNat) (SRef SNat)) xs in
  sst_write #(SPair (SRef SNat) (SRef SNat)) xs (x', x');
  witness (contains_pred xs); witness (contains_pred x'); witness (contains_pred x'');
  witness (is_shared xs); witness (is_shared x'); witness (is_shared x'');
  (fun _ -> 
    recall (contains_pred xs); recall (contains_pred x'); recall (contains_pred x'');
    recall (is_shared xs); recall (is_shared x'); recall (is_shared x'');
    sst_write #(SPair (SRef SNat) (SRef SNat)) xs (x', x'');
    raise_val ())
  
val ctx_identity :
  elab_typ (TArr (TRef TNat) (TRef TNat))
let ctx_identity x = x

val ctx_HO_test2 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test2 f =
  let x:ref int = downgrade_val (f (raise_val ())) in
  sst_write #SNat x (!x + 1);
  admit ();
  raise_val ()

val ctx_swap_ref_test :
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef (TRef TNat)) TUnit))
let ctx_swap_ref_test x =
  let x : ref (ref int) = downgrade_val x in
  witness (contains_pred x);
  witness (is_shared x);
  let cb : elab_typ (TArr (TRef (TRef TNat)) TUnit) = (fun y ->
    let y : ref (ref int) = downgrade_val y in
    recall (contains_pred x);
    recall (is_shared x);
    
    let z = sst_read x in
    let t = sst_read y in
    sst_write #(SRef SNat) x t;
    sst_write #(SRef SNat) y z;

    raise_val ()) in
  cb

val ctx_dynamic_alloc_test :
   elab_typ (TArr TUnit (TRef TNat))
let ctx_dynamic_alloc_test _ = 
  let v = sst_alloc_shared #SNat 0 in 
  raise_val v

val ctx_HO_test3 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test3 f =
  let x:ref int = downgrade_val (f (raise_val ())) in
  let y:ref int = sst_alloc_shared #SNat (!x + 1) in
  raise_val ()

#push-options "--split_queries always"
val ctx_returns_callback_test :
  elab_typ (TArr TUnit (TArr TUnit TUnit))
let ctx_returns_callback_test _ =
  let x: ref int = sst_alloc_shared #SNat 13 in
  witness (contains_pred x);
  witness (is_shared x);
  let cb : elab_typ (TArr TUnit TUnit) = (fun _ ->
    recall (contains_pred x);
    recall (is_shared x);
    sst_write #SNat x (sst_read x % 5);
    raise_val ()
  ) in
  cb
#pop-options

val ctx_HO_test4 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test4 f =
  let x:ref int = downgrade_val (f (raise_val ())) in
  let y:ref (ref int) = sst_alloc_shared #(SRef SNat) x in
  raise_val ()

val progr_sep_test: 
  #rp: ref int -> 
  ctx:(elab_typ (TArr TUnit TUnit)) ->
  SST unit
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      ~(is_shared rp h0)))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
         
let progr_sep_test #rp f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  downgrade_val (f (raise_val ()))

val progr_declassify :
  rp: ref int -> 
  ctx:(elab_typ (TArr (TRef TNat) TUnit)) ->
  SST unit
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      ~(is_shared rp h0)))
    (ensures (fun h0 _ h1 -> True))
let progr_declassify rp f =
  let h0 = get () in
  sst_share #SNat rp;
  let h1 = get () in
  let r = downgrade_val (f (raise_val rp)) in  
  r

val progr_declassify_nested:
  rp: ref (ref int) -> 
  ctx:(elab_typ (TArr (TRef (TRef TNat)) TUnit)) ->
  SST unit
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      ~(is_shared rp h0)))
    (ensures (fun h0 _ h1 -> True))
let progr_declassify_nested rp f =
  let p : ref int = sst_read #(SRef SNat) rp in
  sst_share #SNat p;
  sst_share #(SRef SNat) rp;
  // let r = elab_alloc (!rp) in (* <-- needed a copy here! *) 
  downgrade_val (f (raise_val rp))

val progr_secret_unchanged_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr TUnit TUnit)) ->
  SST unit 
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      ~(is_shared rp h0) /\
      satisfy rs h0 is_shared))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp))
         
let progr_secret_unchanged_test rp rs ctx = 
  let h0 = get () in
  let secret: ref int = sst_alloc #SNat 0 in
  let h1 = get () in
  downgrade_val (ctx (raise_val ()));
  let v = sst_read #SNat secret in
  ()

val progr_passing_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr (TArr TUnit TUnit) TUnit)) ->
  SST unit 
    (requires (fun h0 ->
      satisfy rp h0 contains_pred /\
      ~(is_shared rp h0) /\
      satisfy rs h0 is_shared))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context

// TODO: the callback of the program should be able to modify rp
let progr_passing_callback_test rp rs f =
  let secret: ref int = sst_alloc #SNat 0 in
  sst_share #SNat secret;
  witness (contains_pred secret);
  witness (is_shared secret);
  let cb: elab_typ (TArr TUnit TUnit) = (fun _ -> 
    recall (contains_pred secret);
    recall (is_shared secret);
    sst_write #SNat secret (!secret + 1);
    raise_val ()) in
  downgrade_val (f cb);
  ()

val progr_getting_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr TUnit (TArr TUnit TUnit))) ->
  SST unit 
    (requires (fun h0 ->
      satisfy rp h0 contains_pred /\
      ~(is_shared rp h0) /\
      satisfy rs h0 is_shared))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp))
let progr_getting_callback_test rp rs f =
  let cb = f (raise_val ()) in
  downgrade_val (cb (raise_val ()));
  ()
