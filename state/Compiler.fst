module Compiler

open FStar.FunctionalExtensionality
open FStar.Tactics
open FStar.Ghost

open MST.Repr
open MST.Tot
open SharedRefs
open TargetLang
open BeyondCriteria

open HigherOrderContracts

noeq
type src_interface1 = {
  ct : Type;
  c_ct : safe_importable_to ct;
}

type ctx_src1 (i:src_interface1)  = i.ct
type prog_src1 (i:src_interface1) = i.ct -> SST int (fun h0 -> True) (fun h0 _ h1 -> True)
type whole_src1 = unit -> SST int (fun h0 -> True) (fun h0 _ h1 -> True)

let link_src1 (#i:src_interface1) (p:prog_src1 i) (c:ctx_src1 i) : whole_src1 =
  fun () -> p c

val beh_src1 : whole_src1 ^-> st_mwp_h heap int
let beh_src1 = on_domain whole_src1 (fun ws -> theta (reify (ws ()))) (** what happens with the pre-condition? **)

let src_language1 : language (st_wp int) = {
  interface = src_interface1;
  ctx = ctx_src1; pprog = prog_src1; whole = whole_src1;
  link = link_src1;
  beh = beh_src1;
}

noeq
type tgt_interface1 = {
  ct : fl:_ -> inv : (heap -> Type0) -> prref: mref_pred -> hrel : FStar.Preorder.preorder heap -> Type u#a;
  c_ct : targetlang default_spec (ct AllOps (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec));
}

type ctx_tgt1 (i:tgt_interface1) =
  #fl: erased tflag ->
  inv  : (heap -> Type0) ->
  prref: mref_pred ->
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  hrel : FStar.Preorder.preorder heap ->
  read :  ttl_read fl inv prref hrel ->
  write : ttl_write fl inv prref hrel ->
  alloc : ttl_alloc fl inv prref hrel  ->
  i.ct fl inv prref hrel

type prog_tgt1 (i:tgt_interface1) =
  i.ct AllOps (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec) ->
  SST int (fun _ -> True) (fun _ _ _ -> True)

type whole_tgt1 = (unit -> SST int (fun _ -> True) (fun _ _ _ -> True))

val instantiate_ctx_tgt1 : (#i:tgt_interface1) -> ctx_tgt1 i -> i.ct AllOps (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec)
let instantiate_ctx_tgt1 c =
  c (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec) tl_read tl_write tl_alloc

val link_tgt1 : #i:tgt_interface1 -> prog_tgt1 i -> ctx_tgt1 i -> whole_tgt1
let link_tgt1 p c =
  fun () -> p (instantiate_ctx_tgt1 c)

val beh_tgt1 : whole_tgt1 ^-> st_mwp_h heap int
let beh_tgt1 = on_domain whole_tgt1 (fun wt -> theta (reify (wt ())))

let tgt_language1 : language (st_wp int) = {
  interface = tgt_interface1;
  ctx = ctx_tgt1; pprog = prog_tgt1; whole = whole_tgt1;
  link = link_tgt1;
  beh = beh_tgt1;
}

let comp_int_src_tgt1 (i:src_interface1) : tgt_interface1 = {
  ct = (fun _ _ _ _ -> i.c_ct.ityp);
  c_ct = i.c_ct.c_ityp;
}

val backtranslate_ctx1 : (#i:src_interface1) -> ctx_tgt1 (comp_int_src_tgt1 i) -> src_language1.ctx i
let backtranslate_ctx1 #i ct = i.c_ct.safe_import (instantiate_ctx_tgt1 ct)

let pre' = sst_pre (fun _ -> True)

val compile_pprog1 : (#i:src_interface1) -> prog_src1 i -> prog_tgt1 (comp_int_src_tgt1 i)
let compile_pprog1 #i ps =
 // The program has a stronger post-condition that the context
 //   (safe_exportable_arrow i.ct int #i.c_ct (fun _ -> sst_post _ pre' (fun _ _ _ -> True)) ()).export ps

unfold
let eq_wp wp1 wp2 = wp1 ⊑ wp2 /\ wp2 ⊑ wp1

let comp1 : compiler = {
  src_sem = st_wp int;
  tgt_sem = st_wp int;
  source = src_language1;
  target = tgt_language1;

  comp_int = comp_int_src_tgt1;

  compile_pprog = compile_pprog1;

  rel_sem = eq_wp;
}

val comp1_rrhc : unit -> Lemma (rrhc comp1)
let comp1_rrhc () : Lemma (rrhc comp1) =
  assert (rrhc comp1) by (
    norm [delta_only [`%rrhc]];
    let i = forall_intro () in
    let ct = forall_intro () in
    FStar.Tactics.witness (`(backtranslate_ctx1 #(`#i) (`#ct)));
    compute ())

noeq
type src_interface2 = {
  pt : Type;
  c_pt : exportable_from pt;
}

type ctx_src2 (i:src_interface2) =
  i.pt ->
  SST int (fun h0 -> True) (fun h0 _ h1 -> (Mktuple3?._3 default_spec) h0 h1)

type prog_src2 (i:src_interface2) = i.pt
type whole_src2 = unit -> SST int (fun h0 -> True) (fun h0 _ h1 -> (Mktuple3?._3 default_spec) h0 h1)

let link_src2 (#i:src_interface2) (p:prog_src2 i) (c:ctx_src2 i) : whole_src2 =
  fun () -> c p

val beh_src2 : whole_src2 ^-> st_mwp_h heap int
let beh_src2 = on_domain whole_src2 (fun ws -> theta (reify (ws ()))) (** what happens with the pre-condition? **)

let src_language2 : language (st_wp int) = {
  interface = src_interface2;
  ctx = ctx_src2; pprog = prog_src2; whole = whole_src2;
  link = link_src2;
  beh = beh_src2;
}

noeq
type tgt_interface2 = {
  pt : fl:_ -> inv : (heap -> Type0) -> prref: mref_pred -> hrel : FStar.Preorder.preorder heap -> Type u#a;
  c_pt : targetlang default_spec (pt AllOps (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec));
}

type ctx_tgt2 (i:tgt_interface2) =
  #fl: _ ->
  inv  : (heap -> Type0) ->
  prref: mref_pred ->
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  hrel : FStar.Preorder.preorder heap ->
  read :  ttl_read fl inv prref hrel ->
  write : ttl_write fl inv prref hrel ->
  alloc : ttl_alloc fl inv prref hrel  ->
  p:i.pt fl inv prref hrel ->
  STFlag int fl (fun h0 -> inv h0) (fun h0 _ h1 -> h0 `hrel` h1 /\ inv h1) (** TODO: to check if the program should be an arrow because we don't enforce prref **)

type prog_tgt2 (i:tgt_interface2) =
  i.pt AllOps (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec)

type whole_tgt2 = (unit -> SST int (fun h0 -> True) (fun h0 _ h1 -> (Mktuple3?._3 default_spec) h0 h1))

val link_tgt2 : #i:tgt_interface2 -> prog_tgt2 i -> ctx_tgt2 i -> whole_tgt2
let link_tgt2 p c =
  fun () ->
    c (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec)
      tl_read tl_write tl_alloc
      p

val beh_tgt2 : whole_tgt2 ^-> st_mwp_h heap int
let beh_tgt2 = on_domain whole_tgt2 (fun wt -> theta (reify (wt ())))

let tgt_language2 : language (st_wp int) = {
  interface = tgt_interface2;
  ctx = ctx_tgt2; pprog = prog_tgt2; whole = whole_tgt2;
  link = link_tgt2;
  beh = beh_tgt2;
}

let comp_int_src_tgt2 (i:src_interface2) : tgt_interface2 = {
  pt = (fun _ _ _ _ -> i.c_pt.ityp);
  c_pt = i.c_pt.c_ityp;
}

val backtranslate_ctx2 : (#i:src_interface2) -> ctx_tgt2 (comp_int_src_tgt2 i) -> src_language2.ctx i
let backtranslate_ctx2 #i ct ps =
  ct #AllOps (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec)
      tl_read tl_write tl_alloc (i.c_pt.export ps)

val compile_pprog2 : (#i:src_interface2) -> prog_src2 i -> prog_tgt2 (comp_int_src_tgt2 i)
let compile_pprog2 #i ps = i.c_pt.export ps

let comp2 : compiler = {
  src_sem = st_wp int;
  tgt_sem = st_wp int;
  source = src_language2;
  target = tgt_language2;

  comp_int = comp_int_src_tgt2;

  compile_pprog = compile_pprog2;

  rel_sem = eq_wp;
}

val comp2_rrhc : unit -> Lemma (rrhc comp2)
let comp2_rrhc () : Lemma (rrhc comp2) =
  assert (rrhc comp2) by (
    norm [delta_only [`%rrhc]];
    let i = forall_intro () in
    let ct = forall_intro () in
    FStar.Tactics.witness (`(backtranslate_ctx2 #(`#i) (`#ct)));
    compute ())
