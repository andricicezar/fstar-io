module Compiler.STLC

open FStar.FunctionalExtensionality
open FStar.Tactics

open MST.Repr
open MST.Tot
open SharedRefs
open TargetLang
open STLC
open Backtranslation.STLCToTargetLang

open BeyondCriteria
open HigherOrderContracts

noeq
type src_interface1 = {
  ct : Type;
  c_ct : safe_importable_to ct;

  tct : typ;
  c_tct : unit -> Lemma (elab_typ concrete_spec tct == c_ct.ityp); (** can one even prove this? **)
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
  ct : typ;
}

type ctx_tgt1 (i:tgt_interface1) =
  e:exp{EAbs? e} & typing empty e i.ct

type prog_tgt1 (i:tgt_interface1) = elab_typ concrete_spec i.ct -> SST int (fun _ -> True) (fun _ _ _ -> True)
type whole_tgt1 = (unit -> SST int (fun _ -> True) (fun _ _ _ -> True))

val instantiate_ctx_tgt1 : (#i:tgt_interface1) -> ctx_tgt1 i -> elab_typ concrete_spec i.ct
let instantiate_ctx_tgt1 c =
  backtranslate_eabs
    #(inv_c)
    #(prref_c)
    #(hrel_c)
    bt_read
    bt_write
    bt_alloc
    (dsnd c)
    (vempty concrete_spec)


val link_tgt1 : #i:tgt_interface1 -> prog_tgt1 i -> ctx_tgt1 i -> whole_tgt1
let link_tgt1 #i p c () = p (instantiate_ctx_tgt1 c)

val beh_tgt1 : whole_tgt1 ^-> st_mwp_h heap int
let beh_tgt1 = on_domain whole_tgt1 (fun wt -> theta (reify (wt ())))

let tgt_language1 : language (st_wp int) = {
  interface = tgt_interface1;
  ctx = ctx_tgt1; pprog = prog_tgt1; whole = whole_tgt1;
  link = link_tgt1;
  beh = beh_tgt1;
}

let comp_int_src_tgt1 (i:src_interface1) : tgt_interface1 = {
  ct = i.tct;
}

val backtranslate_ctx1 : (#i:src_interface1) -> ctx_tgt1 (comp_int_src_tgt1 i) -> src_language1.ctx i
let backtranslate_ctx1 #i ct =
  i.c_tct ();
  i.c_ct.safe_import (instantiate_ctx_tgt1 ct)

val compile_pprog1 : (#i:src_interface1) -> prog_src1 i -> prog_tgt1 (comp_int_src_tgt1 i)
let compile_pprog1 #i ps ct =
  i.c_tct (); 
  ps (i.c_ct.safe_import ct)

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
