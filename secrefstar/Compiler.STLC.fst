module Compiler.STLC

open FStar.FunctionalExtensionality
open FStar.Tactics

open MST.Repr
open MST.Tot
open LabeledRefs
open PolyIface
open STLC
open Backtranslation.STLCToPolyIface
open SpecTree
open BeyondCriteria
open HigherOrderContracts

noeq
type src_interface1 = {
  specs:spec_tree;
  hocs:hoc_tree c3p specs;
  ct : Type;
  c_ct : safe_importable_to c3p ct specs;

  tct : typ;
  c_tct : unit -> Lemma (elab_typ c3p tct == c_ct.ityp); (** can one even prove this? **)
}

type ctx_src1 (i:src_interface1)  = i.ct
type prog_src1 (i:src_interface1) = i.ct -> LR int (fun h0 -> True) (fun h0 _ h1 -> True)
type whole_src1 = unit -> LR int (fun h0 -> True) (fun h0 _ h1 -> True)

let link_src1 (#i:src_interface1) (p:prog_src1 i) (c:ctx_src1 i) : whole_src1 =
  fun () -> p c

(* Single reify site for the behaviors, so that the behaviors of the source
   and target whole programs are related by congruence (as in sciostar). *)
val beh_whole1 : whole_src1 -> st_mwp_h heap int
let beh_whole1 w = theta (reify (w ()))

val beh_src1 : whole_src1 ^-> st_mwp_h heap int
let beh_src1 = on_domain whole_src1 (fun ws -> beh_whole1 ws) (** what happens with the pre-condition? **)

let src_language1 : language (st_wp int) = {
  interface = src_interface1;
  ctx = ctx_src1; pprog = prog_src1; whole = whole_src1;
  link = link_src1;
  beh = beh_src1;
}

noeq
type tgt_interface1 = {
  ct : typ;
}

type ctx_tgt1 (i:tgt_interface1) =
  e:exp{EAbs? e} & typing empty e i.ct

type prog_tgt1 (i:tgt_interface1) = elab_typ c3p i.ct -> LR int (fun _ -> True) (fun _ _ _ -> True)
type whole_tgt1 = (unit -> LR int (fun _ -> True) (fun _ _ _ -> True))

val instantiate_ctx_tgt1 : (#i:tgt_interface1) -> ctx_tgt1 i -> elab_typ c3p i.ct
let instantiate_ctx_tgt1 c =
  backtranslate_eabs
    bt_read
    bt_write
    bt_alloc
    (dsnd c)
    (vempty c3p)


val link_tgt1 : #i:tgt_interface1 -> prog_tgt1 i -> ctx_tgt1 i -> whole_tgt1
let link_tgt1 #i p c () = p (instantiate_ctx_tgt1 c)

val beh_tgt1 : whole_tgt1 ^-> st_mwp_h heap int
let beh_tgt1 = on_domain whole_tgt1 (fun wt -> beh_whole1 wt)

let tgt_language1 : language (st_wp int) = {
  interface = tgt_interface1;
  ctx = ctx_tgt1; pprog = prog_tgt1; whole = whole_tgt1;
  link = link_tgt1;
  beh = beh_tgt1;
}

let comp_int_src_tgt1 (i:src_interface1) : tgt_interface1 = {
  ct = i.tct;
}

val backtranslate_ctx1 : (#i:src_interface1) -> ctx_tgt1 (comp_int_src_tgt1 i) -> ctx_src1 i
let backtranslate_ctx1 #i ct =
  i.c_tct ();
  i.c_ct.safe_import i.hocs (instantiate_ctx_tgt1 ct)

val compile_pprog1 : (#i:src_interface1) -> prog_src1 i -> prog_tgt1 (comp_int_src_tgt1 i)
let compile_pprog1 #i ps ct =
  (* the c_tct lemma call sits inside the argument, in the same position as
     in backtranslate_ctx1, so that linking the compiled program yields a
     whole program syntactically equal to the source one *)
  ps (i.c_tct (); i.c_ct.safe_import i.hocs ct)

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

(* The source and target whole programs are syntactically equal (cf.
   Compiler.syntactic_equality1; here the two whole-program types coincide,
   so no compile_whole is involved). *)
let syntactic_equality1 (i:src_interface1) (ct:ctx_tgt1 (comp_int_src_tgt1 i)) (ps:prog_src1 i) : Lemma (
  let it = comp_int_src_tgt1 i in
  let cs = backtranslate_ctx1 #i ct in
  let pt : prog_tgt1 it = (compile_pprog1 #i ps) in
  let wt : whole_tgt1 = (pt `link_tgt1` ct) in
  let ws : whole_src1 = (ps `link_src1` cs) in
  ws == wt
) by (norm[delta_only [`%link_tgt1;`%link_src1;`%backtranslate_ctx1;`%compile_pprog1];iota]) = ()

(* Pointwise RrHC statement: the behaviors are equal by congruence, since
   the whole programs are syntactically equal (as in sciostar). *)
let comp1_rrhc_2 (i:src_interface1) (ct:ctx_tgt1 (comp_int_src_tgt1 i)) (ps:prog_src1 i) : Lemma (
  let it = comp_int_src_tgt1 i in
  let cs = backtranslate_ctx1 #i ct in
  let pt : prog_tgt1 it = (compile_pprog1 #i ps) in
  let wt : whole_tgt1 = (pt `link_tgt1` ct) in
  let ws : whole_src1 = (ps `link_src1` cs) in
  beh_src1 ws == beh_tgt1 wt) =
  syntactic_equality1 i ct ps

let comp1_rrhc_1 (i:(comp1 u#a).source.interface) (ct:(comp1 u#a).target.ctx ((comp1 u#a).comp_int i)) (ps:(comp1 u#a).source.pprog i) : Lemma (
  (comp1 u#a).source.beh (ps `(comp1 u#a).source.link #i` (backtranslate_ctx1 #i ct)) `(comp1 u#a).rel_sem`
  (comp1 u#a).target.beh ((comp1 u#a).compile_pprog #i ps `(comp1 u#a).target.link #((comp1 u#a).comp_int i)` ct)) =
  comp1_rrhc_2 i ct ps

(* Note: previously this was discharged with a `compute ()` tactic; with the
   mst representation on lib's two-channel free monad, the fully normalized
   goal is too large for the solver, so the proof goes through the syntactic
   equality of the whole programs instead, as in sciostar (with the universe
   instantiation of comp1 fixed). *)
val comp1_rrhc : unit -> Lemma (rrhc (comp1 u#a))
let comp1_rrhc () : Lemma (rrhc (comp1 u#a)) =
  rrhc_intro (comp1 u#a) backtranslate_ctx1 comp1_rrhc_1
