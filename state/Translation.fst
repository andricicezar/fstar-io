module Translation

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Universe 

open Labeled.Monotonic.Heap
open Labeled.MST
open Witnessable
open TargetLang
open STLC

let rec is_base_typ (t:typ) =
  match t with
  | TUnit -> True
  | TNat -> True
  | TSum t1 t2 -> is_base_typ t1 /\ is_base_typ t2
  | TPair t1 t2 -> is_base_typ t1 /\ is_base_typ t2
  | TRef t -> is_base_typ t
  | TLList t -> is_base_typ t
  | TArr _ _ -> False

type base_typ = t:typ{is_base_typ t}

let rec to_inv_typ (t:base_typ) : inv_typ =
  match t with
  | TUnit -> InvT_Unit
  | TNat -> InvT_Nat
  | TSum t1 t2 -> InvT_Sum (to_inv_typ t1) (to_inv_typ t2)
  | TPair t1 t2 -> InvT_Pair (to_inv_typ t1) (to_inv_typ t2)
  | TRef t -> InvT_Ref (to_inv_typ t)
  | TLList t -> InvT_LList (to_inv_typ t)

unfold
let elab_typ_base (t:base_typ) : Type u#0 = 
  to_Type (to_inv_typ t)
  // match t with
  // | TUnit -> unit
  // | TNat -> int
  // | TSum t1 t2 -> either (elab_typ_base t1) (elab_typ_base t2)
  // | TPair t1 t2 -> (elab_typ_base t1) * (elab_typ_base t2)
  // | TRef t -> ref (elab_typ_base t)
  // | TLList t -> linkedList (elab_typ_base t)

unfold
let elab_typ_base_tc (t:base_typ) : witnessable (elab_typ_base t) =
  to_Type_solve (to_inv_typ t)
  // match t with
  // | TUnit -> witnessable_unit
  // | TNat -> witnessable_int
  // | TSum t1 t2 -> witnessable_sum (elab_typ_base t1) (elab_typ_base t2) #(elab_typ_base_tc t1) #(elab_typ_base_tc t2)
  // | TPair t1 t2 -> witnessable_pair (elab_typ_base t1) (elab_typ_base t2) #(elab_typ_base_tc t1) #(elab_typ_base_tc t2)
  // | TRef t -> witnessable_ref (elab_typ_base t) #(elab_typ_base_tc t)
  // | TLList t -> witnessable_llist (elab_typ_base t) #(elab_typ_base_tc t)

let rec is_my_typ (t:typ) =
  match t with
  | TUnit -> True
  | TNat -> True
  | TSum t1 t2 -> is_my_typ t1 /\ is_my_typ t2
  | TPair t1 t2 -> is_my_typ t1 /\ is_my_typ t2
  | TRef t -> is_base_typ t
  | TLList t -> is_base_typ t
  | TArr t1 t2 -> is_my_typ t1 /\ is_my_typ t2

type my_typ = t:typ{is_my_typ t}

unfold let shallowly_contained_low (#a:Type) {| c:witnessable a |} (v:a) (h:lheap) =
  c.satisfy v h contains_pred /\ c.satisfy v h is_low_pred

unfold let pre_tgt_arrow
  (#t1:Type) {| c1 : witnessable t1 |}
  (x:t1) (h0:lheap) =
  inv_low_contains h0 /\
  shallowly_contained_low #t1 #c1 x h0

unfold let post_tgt_arrow
  (#t1:Type) {| c1 : witnessable t1 |}
  (#t2:Type) {| c2 : witnessable t2 |}
  (x:t1) (h0:lheap) (r:t2) (h1:lheap) =
  inv_low_contains h1 /\
  modifies_only_label Low h0 h1 /\                       (* allows low references to be modified *)
  modifies_classification Set.empty h0 h1 /\             (* no modifications of the classification *)
  shallowly_contained_low #t2 #c2 r h1

let mk_tgt_arrow
  (t1:Type) {| c1 : witnessable t1 |}
  (t2:Type) {| c2 : witnessable t2 |}
= x:t1 -> ST t2 
    (requires (pre_tgt_arrow #t1 #c1 x ))
    (ensures (post_tgt_arrow #t1 #c1 #t2 #c2 x))

let rec _elab_typ (t:my_typ) : tt:Type u#1 & witnessable tt =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = _elab_typ t1 in
    let tt2 = _elab_typ t2 in
    (| mk_tgt_arrow (dfst tt1) #(dsnd tt1) (dfst tt2) #(dsnd tt2),
       witnessable_arrow (dfst tt1) (dfst tt2) pre_tgt_arrow post_tgt_arrow
    |)
  end 
  | TUnit -> (| raise_t unit, solve |)
  | TNat -> (| raise_t int, solve |)
  | TSum t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 in
    let (| tt2, c_tt2 |) = _elab_typ t2 in
    (| raise_t (either tt1 tt2), witnessable_univ_raise _ #(witnessable_sum tt1 tt2 #c_tt1 #c_tt2) |)
  | TPair t1 t2 ->
    let (| tt1, c_tt1 |) = _elab_typ t1 in
    let (| tt2, c_tt2 |) = _elab_typ t2 in
    (| raise_t (tt1 * tt2), witnessable_univ_raise _ #(witnessable_pair tt1 tt2 #c_tt1 #c_tt2) |)
  | TRef _ ->
    let tt = elab_typ_base t in
    let c_tt = elab_typ_base_tc t in
    (| raise_t tt, witnessable_univ_raise _ #c_tt |)
  | TLList t ->
    let tt = elab_typ_base t in
    let c_tt = elab_typ_base_tc t in
    (| raise_t (linkedList tt), witnessable_univ_raise _ #(witnessable_llist tt #c_tt) |)

let elab_typ (t:my_typ) : Type =
  dfst (_elab_typ t)

let elab_typ_tc (t:my_typ) : witnessable (elab_typ t) =
  dsnd (_elab_typ t)

let eliminate_inv_low' h (a:base_typ) (r:ref (elab_typ_base a)) :
  Lemma
    (requires (inv_points_to h is_low_pred))
    (ensures (
      (witnessable_ref _ #(elab_typ_base_tc a)).satisfy r h is_low_pred ==> 
        (elab_typ_base_tc a).satisfy (sel h r) h is_low_pred
    )) = eliminate_inv_low h (to_inv_typ a) r

let eliminate_inv_contains' (h:lheap) (a:base_typ) (r:ref (elab_typ_base a)) :
  Lemma
    (requires (inv_points_to h contains_pred))
    (ensures (
      (witnessable_ref _ #(elab_typ_base_tc a)).satisfy r h contains_pred ==> 
        (elab_typ_base_tc a).satisfy (sel h r) h contains_pred
    )) = eliminate_inv_contains h (to_inv_typ a) inv_low_contains r

(** ** Elaboration of the operations **) 

let elab_write (#t:base_typ) (r:ref (elab_typ_base t)) (v:elab_typ_base t) 
: IST unit
  (requires (fun h0 -> 
    shallowly_contained_low #_ #(elab_typ_base_tc (TRef t)) r h0 /\
    shallowly_contained_low #_ #(elab_typ_base_tc t) v h0))
  (ensures (fun h0 () h1 ->
    write_post r v h0 () h1 /\
    modifies_only_label Low h0 h1 /\
    shallowly_contained_low #_ #(elab_typ_base_tc (TRef t)) r h1))
= let h0 = get () in
  write r v;
  let h1 = get () in
  lemma_write_preserves_is_low (to_inv_typ t) r v h0 h1;
  lemma_write_preserves_contains (to_inv_typ t) r v h0 h1;
  ()

let declassify_low' (#t:base_typ) (r:ref (elab_typ_base t)) : ST unit
  (fun h -> (elab_typ_base_tc (TRef t)).satisfy r h contains_pred /\ inv_points_to h contains_pred)
  (fun h0 () h1 -> 
    inv_points_to h1 contains_pred /\
    shallowly_contained_low #_ #(elab_typ_base_tc (TRef t)) r h1 /\
    declassify_post r Low h0 () h1)
=
  let h0 = get () in
  declassify r Low;
  let h1 = get () in
  lemma_declassify_preserves_contains (to_inv_typ t) r h0 h1

val elab_alloc (#t:base_typ) (init:elab_typ_base t)
: IST (ref (elab_typ_base t))
  (requires (fun h0 ->
    shallowly_contained_low #_ #(elab_typ_base_tc t) init h0))
  (ensures (fun h0 r h1 -> 
    fresh r h0 h1 /\ 
    modifies Set.empty h0 h1 /\
    modifies_classification Set.empty h0 h1 /\
    sel h1 r == init /\
    shallowly_contained_low #_ #(elab_typ_base_tc (TRef t)) r h1))
let elab_alloc #t init = 
  let h0 = get () in
  let r : ref (elab_typ_base t) = ist_alloc init in
  let h1 = get () in
  declassify_low' r;
  let h2 = get () in
  (elab_typ_base_tc t).satisfy_monotonic init is_low_pred h0 h1;
  lemma_declassify_preserves_is_low (to_inv_typ t) r h1 h2;
  assert (inv_points_to h2 is_low_pred);
  r

(** ** Examples **) 

val ctx_update_ref_test : 
  elab_typ (TArr (TRef TNat) TUnit)
let ctx_update_ref_test y =
  let y : ref int = downgrade_val y in
  elab_write #TNat y (!y + 5);
  raise_val ()

val ctx_update_multiple_refs_test : 
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit))
let ctx_update_multiple_refs_test x =
  let x : ref (ref int) = downgrade_val x in
  mst_witness (contains_pred x);
  mst_witness (is_low_pred x);
  let cb : elab_typ (TArr (TRef TNat) TUnit) = (fun y ->
    let y : ref int = downgrade_val y in
    let h0 = get () in
    mst_recall (contains_pred x);
    let ix : ref int = !x in
    mst_recall (is_low_pred x);   
    eliminate_inv_contains' h0 (TRef TNat) x;
    elab_write #TNat ix (!ix + 1);
    let h1 = get () in
    elab_write #(TRef TNat) x y;
    let h2 = get () in
    elab_write #TNat y (!y + 5);
    let h3 = get () in
    eliminate_inv_low' h0 (TRef TNat) x;
    lemma_modifies_only_label_trans Low h0 h1 h2;
    lemma_modifies_only_label_trans Low h0 h2 h3;
    assert (modifies_only_label Low h0 h3);
    let r = raise_val () in
    assert (shallowly_contained_low r h3);
    assert (inv_low_contains h3);
    assert (modifies_classification Set.empty h0 h3);
    r
  ) in
  cb

val ctx_HO_test1 : 
  elab_typ (TArr (TRef (TPair (TRef TNat) (TRef TNat))) (TArr TUnit TUnit))
let ctx_HO_test1 xs =
  let xs : ref ((ref int) * ref int) = downgrade_val xs in
  let (x', x'') = !xs in
  let h0 = get () in
  eliminate_inv_contains' h0 (TPair (TRef TNat) (TRef TNat)) xs;
  eliminate_inv_low' h0 (TPair (TRef TNat) (TRef TNat)) xs;
  elab_write #(TPair (TRef TNat) (TRef TNat)) xs (x', x');
  mst_witness (is_low_pred xs);
  mst_witness (is_low_pred x');
  mst_witness (is_low_pred x'');
  (fun _ -> 
    mst_recall (is_low_pred xs);
    mst_recall (is_low_pred x');
    mst_recall (is_low_pred x'');
    elab_write #(TPair (TRef TNat) (TRef TNat)) xs (x', x'');
    raise_val ())
  
val ctx_identity :
  elab_typ (TArr (TRef TNat) (TRef TNat))
let ctx_identity x = x

val ctx_HO_test2 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test2 f =
  let h0 = get () in
  let x:ref int = downgrade_val (f (raise_val ())) in
  let h1 = get () in
  elab_write #TNat x (!x + 1);
  let h2 = get () in
  assert (modifies_only_label Low h0 h2);
  raise_val ()

val ctx_swap_ref_test :
  elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef (TRef TNat)) TUnit))
let ctx_swap_ref_test x =
  let x : ref (ref int) = downgrade_val x in
  mst_witness (contains_pred x);
  mst_witness (is_low_pred x);
  let cb : elab_typ (TArr (TRef (TRef TNat)) TUnit) = (fun y ->
    let y : ref (ref int) = downgrade_val y in
    let h0 = get () in
    mst_recall (contains_pred x);
    mst_recall (is_low_pred x);
    eliminate_inv_contains' h0 (TRef TNat) x;
    eliminate_inv_low' h0 (TRef TNat) x;
    
    let z = !x in
    let t = !y in
    elab_write #(TRef TNat) x t;
  
    let h1 = get () in
    elab_write #(TRef TNat) y z;
    let h2 = get () in

    assert (modifies_classification Set.empty h0 h1);
    lemma_modifies_only_label_trans Low h0 h1 h2;
    assert (modifies_only_label Low h0 h2); // we have an SMT Pat for this, but it does not kick in
    assert (modifies_classification Set.empty h0 h2);
    assert (inv_low_contains h2);
    let r = raise_val () in
    assert (shallowly_contained_low r h2);
    r) in
  cb

val ctx_dynamic_alloc_test :
   elab_typ (TArr TUnit (TRef TNat))
let ctx_dynamic_alloc_test _ = 
  let v = elab_alloc #TNat 0 in 
  raise_val v

val ctx_HO_test3 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test3 f =
  let x:ref int = downgrade_val (f (raise_val ())) in
  let y:ref int = elab_alloc #TNat (!x + 1) in
  raise_val ()

val ctx_returns_callback_test :
  elab_typ (TArr TUnit (TArr TUnit TUnit))
let ctx_returns_callback_test _ =
  let x: ref int = elab_alloc #TNat 13 in
  mst_witness (contains_pred x);
  mst_witness (is_low_pred x);
  let cb : elab_typ (TArr TUnit TUnit) = (fun _ ->
    mst_recall (contains_pred x);
    mst_recall (is_low_pred x);
    elab_write #TNat x (!x % 5);
    raise_val ()
  ) in
  cb

val ctx_HO_test4 :
  elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let ctx_HO_test4 f =
  let x:ref int = downgrade_val (f (raise_val ())) in
  let y:ref (ref int) = elab_alloc #(TRef TNat) x in
  raise_val ()

val progr_sep_test: 
  #rp: ref int -> 
  ctx:(elab_typ (TArr TUnit TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context
         
let progr_sep_test #rp f = (** If this test fails, it means that the spec of f does not give [automatically] separation  **)
  downgrade_val (f (raise_val ()))

val progr_declassify :
  rp: ref int -> 
  ctx:(elab_typ (TArr (TRef TNat) TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 -> True))
let progr_declassify rp f =
  let h0 = get () in
  declassify_low' #TNat rp;
  let h1 = get () in
  lemma_declassify_preserves_is_low InvT_Nat rp h0 h1;
  let r = downgrade_val (f (raise_val rp)) in  
  r

val progr_declassify_nested:
  rp: ref (ref int) -> 
  ctx:(elab_typ (TArr (TRef (TRef TNat)) TUnit)) ->
  IST unit
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High))
    (ensures (fun h0 _ h1 -> True))
let progr_declassify_nested rp f =
  let h0 = get () in
  eliminate_inv_contains' h0 (TRef TNat) rp;

  let p : ref int = !rp in
  declassify_low' #TNat p;
  let h1 = get () in
  lemma_declassify_preserves_is_low InvT_Nat p h0 h1;
  declassify_low' #(TRef TNat) rp;
  let h2 = get () in
  lemma_declassify_preserves_is_low (InvT_Ref InvT_Nat) rp h1 h2;
  // let r = elab_alloc (!rp) in (* <-- needed a copy here! *) 
  downgrade_val (f (raise_val rp))

val progr_secret_unchanged_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr TUnit TUnit)) ->
  IST unit 
    (requires (fun h0 -> 
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High /\
      satisfy rs h0 is_low_pred))
    (ensures (fun h0 _ h1 ->
      sel h0 rp == sel h1 rp))
         
let progr_secret_unchanged_test rp rs ctx = 
  let secret: ref int = ist_alloc #InvT_Nat 0 in
  downgrade_val (ctx (raise_val ()));
  let v = !secret in
  assert (v == 0);
  ()

val progr_passing_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr (TArr TUnit TUnit) TUnit)) ->
  IST unit 
    (requires (fun h0 ->
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High /\
      satisfy rs h0 is_low_pred))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp)) // the content of rp should stay the same before/ after calling the context

// TODO: the callback of the program should be able to modify rp
let progr_passing_callback_test rp rs f =
  let secret: ref int = ist_alloc #InvT_Nat 0 in
  let h0 = get () in
  declassify_low' #TNat secret;
  let h1 = get () in
  lemma_declassify_preserves_is_low InvT_Nat secret h0 h1;
  mst_witness (contains_pred secret);
  mst_witness (is_low_pred secret);
  let cb: elab_typ (TArr TUnit TUnit) = (fun _ -> 
    mst_recall (contains_pred secret);
    mst_recall (is_low_pred secret);
    elab_write #TNat secret (!secret + 1);
    raise_val ()) in
  downgrade_val (f cb);
  ()

val progr_getting_callback_test: 
  rp: ref int -> 
  rs: ref (ref int) ->
  ctx:(elab_typ (TArr TUnit (TArr TUnit TUnit))) ->
  IST unit 
    (requires (fun h0 ->
      satisfy rp h0 contains_pred /\
      label_of rp h0 == High /\
      satisfy rs h0 is_low_pred))
    (ensures (fun h0 _ h1 -> sel h0 rp == sel h1 rp))
let progr_getting_callback_test rp rs f =
  let h0 = get () in
  let cb = f (raise_val ()) in
  let h1 = get () in
  downgrade_val (cb (raise_val ()));
  let h2 = get () in
  lemma_modifies_only_label_trans Low h0 h1 h2;
  assert (modifies_only_label Low h0 h2);
  ()

(** ** Elaboration of expressions to F* *)
val elab_apply_arrow :
  t1:my_typ ->
  t2:my_typ ->
  f:elab_typ (TArr t1 t2) ->
  (let tt1 = _elab_typ t1 in
   let tt2 = _elab_typ t2 in
   mk_tgt_arrow (dfst tt1) #(dsnd tt1) (dfst tt2) #(dsnd tt2))
let elab_apply_arrow t1 t2 f x = f x

let cast_TArr (#t1 #t2:my_typ) (f : elab_typ (TArr t1 t2)) (t:my_typ) (#_:squash (t == TArr t1 t2)) : elab_typ t = f

type vcontext (g:context) = 
  vx:var{Some? (g vx)} -> elab_typ' (Some?.v (g vx))

let vempty : vcontext empty = fun _ -> assert false

let vextend #t (x:elab_typ' t) (#g:context) (ve:vcontext g) : vcontext (extend t g) =
  fun y -> if y = 0 then x else ve (y-1)

let all_refs_contained_and_low (#g:context) (ve:vcontext g) (h:lheap) : Type0 =
  forall vx. Some? (g vx) ==> shallowly_contained_low #_ #(elab_typ_tc' (Some?.v (g vx))) (ve vx) h

let stable_refs_contained_and_low (#g:context) (ve:vcontext g) : Lemma (stable (all_refs_contained_and_low ve)) [SMTPat (all_refs_contained_and_low ve)] = 
  introduce forall h0 h1. (h0 `lheap_rel` h1 /\ all_refs_contained_and_low ve h0) ==> all_refs_contained_and_low ve h1 with begin
    introduce (h0 `lheap_rel` h1 /\ all_refs_contained_and_low ve h0) ==> all_refs_contained_and_low ve h1 with _. begin      
      introduce forall vx. Some? (g vx) ==> shallowly_contained_low #_ #(elab_typ_tc' (Some?.v (g vx))) (ve vx) h1 with begin
        introduce Some? (g vx) ==> shallowly_contained_low #_ #(elab_typ_tc' (Some?.v (g vx))) (ve vx) h1 with hyp0. begin
          eliminate forall vx. Some? (g vx) ==> shallowly_contained_low #_ #(elab_typ_tc' (Some?.v (g vx))) (ve vx) h0 with vx;
          eliminate Some? (g vx) ==> shallowly_contained_low #_ #(elab_typ_tc' (Some?.v (g vx))) (ve vx) h0 with hyp0;
          (elab_typ_tc' (Some?.v (g vx))).satisfy_monotonic (ve vx) contains_pred h0 h1;
          (elab_typ_tc' (Some?.v (g vx))).satisfy_monotonic (ve vx) is_low_pred h0 h1
        end
      end
    end  
  end

#push-options "--split_queries always"
let rec elab_exp 
  (#g:context)
  (#e:exp) 
  (#t:typ)
  (tyj:typing g e t)
  (ve:vcontext g)
  : IST (elab_typ' t) 
      (requires (fun h0 -> 
        all_refs_contained_and_low ve h0 /\
        pre_tgt_arrow #unit #witnessable_unit #inv_low_contains () h0))
      (ensures (fun h0 r h1 ->
        post_tgt_arrow #_ #_ #(elab_typ' t) #(elab_typ_tc' t) #inv_low_contains () h0 r h1)) =
  let h0 = get () in
  mst_witness (all_refs_contained_and_low ve);
  match tyj with
  | TyUnit -> ()
  | TyZero -> 0
  | TySucc tyj_s -> 
    1 + (elab_exp tyj_s ve)

  | TyAllocRef #_ #_ #t tyj_e -> begin
    let v : elab_typ' t = elab_exp tyj_e ve in
    let r : ref (elab_typ' t) = elab_alloc #t v in
    r
  end
  | TyReadRef #_ #_ #t tyj_e -> begin
    let r : ref (elab_typ' t) = elab_exp tyj_e ve in
    !r
  end
  | TyWriteRef #_ #_ #_ #t tyj_ref tyj_v -> begin
      let r : ref (elab_typ' t) = elab_exp tyj_ref ve in
      let v : elab_typ' t = elab_exp tyj_v ve in
      elab_write #t r v
  end

  | TyAbs tx #_ #tres tyj_body ->
    let w : mk_tgt_arrow inv_low_contains (elab_typ' tx) #(elab_typ_tc' tx) (elab_typ' tres) #(elab_typ_tc' tres) = 
      (fun (x:elab_typ' tx) -> 
        mst_recall (all_refs_contained_and_low ve);
        let ve' = vextend #tx x ve in
        elab_exp tyj_body ve')
    in
    assert (t == TArr tx tres);
    cast_TArr #tx #tres w t
  | TyVar vx -> 
    let Some tx = g vx in
    let x : elab_typ' tx = ve vx in
    ()
  | TyApp #_ #_ #_ #tx #tres tyj_f tyj_x ->
    assert ((elab_typ t) == (elab_typ tres));
    let f : elab_typ' (TArr tx tres) = elab_exp tyj_f ve in
    let x : elab_typ' tx = elab_exp tyj_x ve in
    elab_apply_arrow tx tres f x

  | TyInl #_ #_ #t1 #t2 tyj_1 ->
    let v1 : elab_typ' t1 = elab_exp tyj_1 ve in
    Inl #_ #(elab_typ' t2) v1
  | TyInr #_ #_ #t1 #t2 tyj_2 ->
    let v2 : elab_typ' t2 = elab_exp tyj_2 ve in
    Inr #(elab_typ' t1) v2
  | TyCaseSum #_ #_ #_ #_ #tl #tr #tres tyj_c tyj_l tyj_r -> begin
    let vc : either (elab_typ' tl) (elab_typ' tr) = elab_exp tyj_c ve in
    match vc with 
    | Inl x -> 
      let wx1 = (elab_typ_tc' tl).witness x contains_pred in
      let wx2 = (elab_typ_tc' tl).witness x is_low_pred in
      let f : elab_typ' (TArr tl tres) = elab_exp tyj_l ve in
      wx1 (); wx2 ();
      elab_apply_arrow tl tres f x
    | Inr y ->
      let wy1 = (elab_typ_tc' tr).witness y contains_pred in
      let wy2 = (elab_typ_tc' tr).witness y is_low_pred in
      let f : elab_typ' (TArr tr tres) = elab_exp tyj_r ve in
      wy1 (); wy2 ();
      elab_apply_arrow tr tres f y
  end

  | TyFst #_ #_ #tf #ts tyj_e ->
    let v = elab_exp tyj_e ve in
    fst #(elab_typ' tf) #(elab_typ' ts) v
  | TySnd #_ #_ #tf #ts tyj_e ->
    let v = elab_exp tyj_e ve in
    snd #(elab_typ' tf) #(elab_typ' ts) v
  | TyPair #_ #_ #_ #tf #ts tyj_f tyj_s->
    let vf : elab_typ' tf = elab_exp tyj_f ve in
    let wvf1 = (elab_typ_tc' tf).witness vf contains_pred in
    let wvf2 = (elab_typ_tc' tf).witness vf is_low_pred in
    let vs : elab_typ' ts = elab_exp tyj_s ve in
    wvf1 (); wvf2 ();
    (vf, vs)
#pop-options


