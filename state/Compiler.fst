module Compiler

open FStar.FunctionalExtensionality
open FStar.Tactics
open FStar.Ghost

open MST.Repr
open MST.Tot
open LabeledRefs
open PolyIface
open BeyondCriteria
open SpecTree
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
  specs : a3p:threep -> spec_tree;
  hocs : hoc_tree c3p (specs c3p);
  ct : threep -> Type;
  c_ct : a3p:threep -> safe_importable_to a3p (ct a3p) (specs a3p);
  psi : heap -> int -> heap -> Type0;
}

type ctx_src1 (i:src_interface1)  = i.ct c3p
type prog_src1 (i:src_interface1) = i.ct c3p -> SST int (fun h0 -> True) i.psi
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
  ct : threep -> Type u#a;
  c_ct : a3p:threep -> poly_iface a3p (ct a3p);
}

type ctx_tgt1 (i:tgt_interface1) =
  #a3p : threep ->
  read :  ttl_read a3p ->
  write : ttl_write a3p ->
  alloc : ttl_alloc a3p  ->
  i.ct a3p

type prog_tgt1 (i:tgt_interface1) =
  i.ct c3p ->
  SST int (fun _ -> True) (fun _ _ _ -> True)


type whole_tgt1 = (unit -> SST int (fun _ -> True) (fun _ _ _ -> True))

val instantiate_ctx_tgt1 : (#i:tgt_interface1) -> ctx_tgt1 i -> i.ct c3p
let instantiate_ctx_tgt1 #i c =
  c tl_read tl_write tl_alloc

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
  ct = (fun a3p -> (i.c_ct a3p).ityp);
  c_ct = (fun a3p -> (i.c_ct a3p).c_ityp);
}

val backtranslate_ctx1 : (#i:src_interface1) -> ctx_tgt1 (comp_int_src_tgt1 i) -> ctx_src1 i
let backtranslate_ctx1 #i ct = (i.c_ct c3p).safe_import i.hocs (instantiate_ctx_tgt1 ct)

let pre' = sst_pre (fun _ -> True)

val compile_pprog1 : (#i:src_interface1) -> prog_src1 i -> prog_tgt1 (comp_int_src_tgt1 i)
let compile_pprog1 #i ps =
    fun c -> ps ((i.c_ct c3p).safe_import i.hocs c)
 // The program has a stronger post-condition that the context
 //   (safe_exportable_arrow i.ct int #i.c_ct (fun _ -> sst_post _ pre' (fun _ _ _ -> True)) ()).export ps

val compile_whole1 : whole_src1 -> whole_tgt1
let compile_whole1 (| _, ws |) = ws

let comp1 : compiler = {
  src_sem = sem_state;
  tgt_sem = sem_state;
  source = src_language1;
  target = tgt_language1;

  comp_int = comp_int_src_tgt1;

  compile_pprog = compile_pprog1;

  rel_sem = (eq_sem);
}

let syntactic_equality1 (i:src_interface1) (ct:ctx_tgt1 (comp_int_src_tgt1 i)) (ps:prog_src1 i) : Lemma (
  let it = comp_int_src_tgt1 i in
  let cs : ctx_src1 i = backtranslate_ctx1 #i ct in
  let pt : prog_tgt1 it = (compile_pprog1 #i ps) in
  let wt : whole_tgt1 = (pt `link_tgt1` ct) in
  let ws : whole_src1 = (ps `link_src1` cs) in
  compile_whole1 ws == wt
) by (norm[delta_only [`%link_tgt1;`%link_src1;`%backtranslate_ctx1;`%compile_pprog1;`%compile_whole1];iota]) = ()

let soundness1 (i:src_interface1) (ct:ctx_tgt1 (comp_int_src_tgt1 i)) (ps:prog_src1 i) : Lemma (
  let it = comp_int_src_tgt1 i in
  let cs : ctx_src1 i = backtranslate_ctx1 #i ct in
  let pt : prog_tgt1 it = (compile_pprog1 #i ps) in
  let wt : whole_tgt1 = (pt `link_tgt1` ct) in
  let ws : whole_src1 = (ps `link_src1` cs) in
  beh_tgt1 (wt) `subset_of` beh_src1 (ws)
) by (norm[delta_only [`%link_tgt1;`%link_src1;`%backtranslate_ctx1;`%compile_pprog1;`%compile_whole1;`%beh_tgt1;`%beh_src1];iota]) = ()

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
  specs: a3p:threep -> spec_tree;
  hocs : hoc_tree c3p (specs c3p);
  pt : threep -> Type;
  c_pt : a3p:threep -> exportable_from a3p (pt a3p) (specs a3p);
}

type ctx_src2 (i:src_interface2) =
  i.pt c3p ->
  SST int (fun h0 -> True) (fun h0 _ h1 -> (hrel_c) h0 h1)

type prog_src2 (i:src_interface2) = i.pt c3p
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
  pt : a3p:threep -> Type u#a;
  c_pt : a3p:threep -> poly_iface a3p (pt a3p);
}

type ctx_tgt2 (i:tgt_interface2) =
  #a3p : threep ->
  read :  ttl_read a3p ->
  write : ttl_write a3p ->
  alloc : ttl_alloc a3p  ->
  p:i.pt a3p ->
  ST int  (fun h0 -> inv a3p h0) (fun h0 _ h1 -> h0 `hrel a3p` h1 /\ inv a3p h1) (** TODO: to check if the program should be an arrow because we don't enforce prref **)

type prog_tgt2 (i:tgt_interface2) =
  i.pt c3p

type whole_tgt2 = (unit -> SST int (fun h0 -> True) (fun h0 _ h1 -> (hrel_c) h0 h1))

val link_tgt2 : #i:tgt_interface2 -> prog_tgt2 i -> ctx_tgt2 i -> whole_tgt2
let link_tgt2 p c =
  fun () ->
    c tl_read tl_write tl_alloc p

val beh_tgt2 : whole_tgt2 ^-> sem_state
let beh_tgt2 = on_domain whole_tgt2 (fun wt -> beh_sem (reify (wt ())))

let tgt_language2 : language sem_state = {
  interface = tgt_interface2;
  ctx = ctx_tgt2; pprog = prog_tgt2; whole = whole_tgt2;
  link = link_tgt2;
  beh = beh_tgt2;
}

let comp_int_src_tgt2 (i:src_interface2) : tgt_interface2 = {
  pt = (fun a3p -> (i.c_pt a3p).ityp);
  c_pt = (fun a3p -> (i.c_pt a3p).c_ityp);
}

val backtranslate_ctx2 : (#i:src_interface2) -> ctx_tgt2 (comp_int_src_tgt2 i) -> src_language2.ctx i
let backtranslate_ctx2 #i ct ps =
  ct tl_read tl_write tl_alloc ((i.c_pt c3p).export i.hocs ps)

val compile_pprog2 : (#i:src_interface2) -> prog_src2 i -> prog_tgt2 (comp_int_src_tgt2 i)
let compile_pprog2 #i ps = (i.c_pt c3p).export i.hocs ps

val compile_whole2 : whole_src2 -> whole_tgt2
let compile_whole2 ws = ws

let comp2 : compiler = {
  src_sem = sem_state;
  tgt_sem = sem_state;
  source = src_language2;
  target = tgt_language2;

  comp_int = comp_int_src_tgt2;

  compile_pprog = compile_pprog2;

  rel_sem = eq_sem;
}

let syntactic_equality2 (i:src_interface2) (ct:ctx_tgt2 (comp_int_src_tgt2 i)) (ps:prog_src2 i) : Lemma (
  let it = comp_int_src_tgt2 i in
  let cs : ctx_src2 i = backtranslate_ctx2 #i ct in
  let pt : prog_tgt2 it = (compile_pprog2 #i ps) in
  let wt : whole_tgt2 = (pt `link_tgt2` ct) in
  let ws : whole_src2 = (ps `link_src2` cs) in
  compile_whole2 ws == wt
) by (norm[delta_only [`%link_tgt2;`%link_src2;`%backtranslate_ctx2;`%compile_pprog2;`%compile_whole2];iota]) = ()

let soundness2 (i:src_interface2) (ct:ctx_tgt2 (comp_int_src_tgt2 i)) (ps:prog_src2 i) : Lemma (
  let it = comp_int_src_tgt2 i in
  let cs : ctx_src2 i = backtranslate_ctx2 #i ct in
  let pt : prog_tgt2 it = (compile_pprog2 #i ps) in
  let wt : whole_tgt2 = (pt `link_tgt2` ct) in
  let ws : whole_src2 = (ps `link_src2` cs) in
  beh_tgt2 (wt) `subset_of` beh_src2 (ws)
) by (norm[delta_only [`%link_tgt2;`%link_src2;`%backtranslate_ctx2;`%compile_pprog2;`%compile_whole2;`%beh_tgt2;`%beh_src2];iota]) = ()


val comp2_rrhc : unit -> Lemma (rrhc comp2)
let comp2_rrhc () : Lemma (rrhc comp2) =
  assert (rrhc comp2) by (
    norm [delta_only [`%rrhc]];
    let i = forall_intro () in
    let ct = forall_intro () in
    FStar.Tactics.witness (`(backtranslate_ctx2 #(`#i) (`#ct)));
    compute ())
