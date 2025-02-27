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

type sem_state = heap -> int -> heap -> Type0

unfold
let subset_of (s1 s2:sem_state) =
  forall h0 r h1. s1 h0 r h1 ==>  s2 h0 r h1

unfold
let eq_sem (s1 s2:sem_state) =
  s1 `subset_of` s2 /\ s2 `subset_of` s1

let beh_sem (m:free int) : sem_state = fun h0 r h1 -> forall p. theta m p h0 ==> p r h1

noeq
type src_interface1 = {
  ct : targetlang_pspec -> Type;
  c_ct : pspec:targetlang_pspec -> safe_importable_to pspec (ct pspec);
  psi : heap -> int -> heap -> Type0;
}

type ctx_src1 (i:src_interface1)  = i.ct concrete_spec
type prog_src1 (i:src_interface1) = i.ct concrete_spec -> SST int (fun h0 -> True) i.psi
type whole_src1 = psi : (heap -> int -> heap -> Type0) & (unit -> SST int (fun h0 -> True) psi)

let link_src1 (#i:src_interface1) (p:prog_src1 i) (c:ctx_src1 i) : whole_src1 =
  (| i.psi, fun () -> p c <: SST int (fun _ -> True) i.psi|)

val beh_src1 : whole_src1 ^-> sem_state
let beh_src1 = on_domain whole_src1 (fun ws -> beh_sem (reify ((dsnd ws) ()))) (** what happens with the pre-condition? **)

let src_language1 : language sem_state = {
  interface = src_interface1;
  ctx = ctx_src1; pprog = prog_src1; whole = whole_src1;
  link = link_src1;
  beh = beh_src1;
}

noeq
type tgt_interface1 = {
  ct : targetlang_pspec -> Type u#a;
  c_ct : pspec:targetlang_pspec -> targetlang pspec (ct pspec);
}

type ctx_tgt1 (i:tgt_interface1) =
  inv  : (heap -> Type0) ->
  prref: mref_pred ->
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  hrel : FStar.Preorder.preorder heap ->
  read :  ttl_read AllOps inv prref hrel ->
  write : ttl_write AllOps inv prref hrel ->
  alloc : ttl_alloc AllOps inv prref hrel  ->
  i.ct (mk_targetlang_pspec inv prref hrel)

type prog_tgt1 (i:tgt_interface1) =
  i.ct concrete_spec ->
  SST int (fun _ -> True) (fun _ _ _ -> True)


type whole_tgt1 = (unit -> SST int (fun _ -> True) (fun _ _ _ -> True))

val instantiate_ctx_tgt1 : (#i:tgt_interface1) -> ctx_tgt1 i -> i.ct concrete_spec
let instantiate_ctx_tgt1 #i c =
  c (inv_c) (prref_c) (hrel_c) tl_read tl_write tl_alloc

val link_tgt1 : #i:tgt_interface1 -> prog_tgt1 i -> ctx_tgt1 i -> whole_tgt1
let link_tgt1 p c =
  fun () -> p (instantiate_ctx_tgt1 c)

val beh_tgt1 : whole_tgt1 ^-> sem_state
let beh_tgt1 = on_domain whole_tgt1 (fun wt -> beh_sem (reify (wt ())))

let tgt_language1 : language sem_state = {
  interface = tgt_interface1;
  ctx = ctx_tgt1; pprog = prog_tgt1; whole = whole_tgt1;
  link = link_tgt1;
  beh = beh_tgt1;
}

let comp_int_src_tgt1 (i:src_interface1) : tgt_interface1 = {
  ct = (fun pspec -> (i.c_ct pspec).ityp);
  c_ct = (fun pspec -> (i.c_ct pspec).c_ityp);
}

val backtranslate_ctx1 : (#i:src_interface1) -> ctx_tgt1 (comp_int_src_tgt1 i) -> ctx_src1 i
let backtranslate_ctx1 #i ct = (i.c_ct concrete_spec).safe_import (instantiate_ctx_tgt1 ct)

let pre' = sst_pre (fun _ -> True)

val compile_pprog1 : (#i:src_interface1) -> prog_src1 i -> prog_tgt1 (comp_int_src_tgt1 i)
let compile_pprog1 #i ps =
    fun c -> ps ((i.c_ct concrete_spec).safe_import c)
 // The program has a stronger post-condition that the context
 //   (safe_exportable_arrow i.ct int #i.c_ct (fun _ -> sst_post _ pre' (fun _ _ _ -> True)) ()).export ps

let comp1 : compiler = {
  src_sem = sem_state;
  tgt_sem = sem_state;
  source = src_language1;
  target = tgt_language1;

  comp_int = comp_int_src_tgt1;

  compile_pprog = compile_pprog1;

  rel_sem = eq_sem;
}

(**
let soundness1 (ws:whole_src1) : Lemma (beh_src1 ws `subset_of` (dfst ws)) by (
  norm [delta_only [`%beh_src1;`%subset_of;`%beh_sem];iota]; explode (); dump "H") = ()

let soundness1 (i:src_interface1) (ct:ctx_tgt1 (comp_int_src_tgt1 i)) (ps:prog_src1 i) : Lemma (
  let it = comp_int_src_tgt1 i in
  let cs : ctx_src1 i = backtranslate_ctx1 #i ct in
  let pt : prog_tgt1 it = (compile_pprog1 #i ps) in
  let wt : whole_tgt1 = (pt `link_tgt1` ct) in
  beh_tgt1 wt `subset_of` i.psi)
by (norm[delta_only [`%link_tgt1;`%link_src1;`%backtranslate_ctx1;`%compile_pprog1;`%beh_src1;`%beh_tgt1];iota]; dump "H") = ()
**)

(**
let syntactic_equality1 (i:src_interface1) (ct:ctx_tgt1 (comp_int_src_tgt1 i)) (ps:prog_src1 i) : Lemma (
  let it = comp_int_src_tgt1 i in
  let cs : ctx_src1 i = backtranslate_ctx1 #i ct in
  let pt : prog_tgt1 it = (compile_pprog1 #i ps) in
  let wt : whole_tgt1 = (pt `link_tgt1` ct) in
  let ws : whole_src1 = (ps `link_src1` cs) in
  dsnd ws == wt
) by (norm[delta_only [`%link_tgt1;`%link_src1;`%backtranslate_ctx1;`%compile_pprog1];iota]) = ()
**)

val comp1_rrhc : unit -> Lemma (rrhc comp1)
let comp1_rrhc () : Lemma (rrhc comp1) =
  assert (rrhc comp1) by (
    norm [delta_only [`%rrhc]];
    let i = forall_intro () in
    let ct = forall_intro () in
    FStar.Tactics.witness (`(backtranslate_ctx1 #(`#i) (`#ct)));
    compute ())

  (**
noeq
type src_interface2 = {
  pt : Type;
  c_pt : exportable_from pt;
}

type ctx_src2 (i:src_interface2) =
  i.pt ->
  SST int (fun h0 -> True) (fun h0 _ h1 -> (hrel_c) h0 h1)

type prog_src2 (i:src_interface2) = i.pt
type whole_src2 = unit -> SST int (fun h0 -> True) (fun h0 _ h1 -> (hrel_c) h0 h1)

let link_src2 (#i:src_interface2) (p:prog_src2 i) (c:ctx_src2 i) : whole_src2 =
  fun () -> c p

val beh_src2 : whole_src2 ^-> sem_state
let beh_src2 = on_domain whole_src2 (fun ws -> beh_sem (reify (ws ()))) (** what happens with the pre-condition? **)

let src_language2 : language sem_state = {
  interface = src_interface2;
  ctx = ctx_src2; pprog = prog_src2; whole = whole_src2;
  link = link_src2;
  beh = beh_src2;
}

noeq
type tgt_interface2 = {
  pt : fl:_ -> inv : (heap -> Type0) -> prref: mref_pred -> hrel : FStar.Preorder.preorder heap -> Type u#a;
  c_pt : targetlang concrete_spec (pt AllOps (inv_c) (prref_c) (hrel_c));
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
  i.pt AllOps (inv_c) (prref_c) (hrel_c)

type whole_tgt2 = (unit -> SST int (fun h0 -> True) (fun h0 _ h1 -> (hrel_c) h0 h1))

val link_tgt2 : #i:tgt_interface2 -> prog_tgt2 i -> ctx_tgt2 i -> whole_tgt2
let link_tgt2 p c =
  fun () ->
    c (inv_c) (prref_c) (hrel_c)
      tl_read tl_write tl_alloc
      p

val beh_tgt2 : whole_tgt2 ^-> sem_state
let beh_tgt2 = on_domain whole_tgt2 (fun wt -> beh_sem (reify (wt ())))

let tgt_language2 : language sem_state = {
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
  ct #AllOps (inv_c) (prref_c) (hrel_c)
      tl_read tl_write tl_alloc (i.c_pt.export ps)

val compile_pprog2 : (#i:src_interface2) -> prog_src2 i -> prog_tgt2 (comp_int_src_tgt2 i)
let compile_pprog2 #i ps = i.c_pt.export ps

let comp2 : compiler = {
  src_sem = sem_state;
  tgt_sem = sem_state;
  source = src_language2;
  target = tgt_language2;

  comp_int = comp_int_src_tgt2;

  compile_pprog = compile_pprog2;

  rel_sem = eq_sem;
}

val comp2_rrhc : unit -> Lemma (rrhc comp2)
let comp2_rrhc () : Lemma (rrhc comp2) =
  assert (rrhc comp2) by (
    norm [delta_only [`%rrhc]];
    let i = forall_intro () in
    let ct = forall_intro () in
    FStar.Tactics.witness (`(backtranslate_ctx2 #(`#i) (`#ct)));
    compute ())
**)
