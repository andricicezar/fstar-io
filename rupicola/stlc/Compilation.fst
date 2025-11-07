module Compilation

open FStar.Tactics

open STLC
open QTyp
open QExp
open ExpRel

let rec compile #g #a (#s:fs_oexp g a) (qs:exp_quotation g s) : Tot exp (decreases qs) =
  match qs with
  | Qtt -> EUnit
  | QFalse -> EFalse
  | QTrue -> ETrue
  | QVar0 -> EVar 0
  | QVar1 -> EVar 1
  | QVar2 -> EVar 2
  | QApp qf qx -> EApp (compile qf) (compile qx)
  | QIf qc qt qe -> EIf (compile qc) (compile qt) (compile qe)
  | QLambda qbody -> ELam (compile qbody)

let lem_compile_empty_closed #a (#s:fs_oexp empty a) (qs:exp_quotation empty s) : Lemma (is_closed (compile qs)) = admit ()

let compile_closed (#a:qType) (#s:get_Type a) (qs:exp_quotation #a empty (fun _ -> s)) : closed_exp =
  lem_compile_empty_closed qs;
  compile qs

let rec compile_equiv #g #a (#s:fs_oexp g a) (qs:exp_quotation g s)
  : Lemma (ensures (s `equiv a` (compile qs))) (decreases qs)
  = match qs with
  | Qtt -> equiv_unit g
  | QFalse -> equiv_false g
  | QTrue -> equiv_true g
  | QVar0 -> admit () // equiv_var g 0
  | QVar1 -> admit () // equiv_var g 1
  | QVar2 -> admit () //equiv_var g 2
  | QApp #_ #qa #qb #f #x qf qx ->
    compile_equiv qf;
    compile_equiv qx;
    equiv_app f x (compile qf) (compile qx)
  | QIf #_ #_ #c qc #t qt #e qe ->
    compile_equiv qc;
    compile_equiv qt;
    compile_equiv qe;
    equiv_if c t e (compile qc) (compile qt) (compile qe)
  | QLambda #_ #_ #_ #f qbody ->
    compile_equiv qbody;
    equiv_lam _ _ f (compile qbody);
    assert (s `equiv a` (ELam (compile qbody)));
    assert (s `equiv a` (compile qs)) by (
      norm [delta_only [`%compile]; zeta;iota];
      rewrite_eqs_from_context ();
      assumption ())

let compile_closed_equiv (#a:qType) (#s:get_Type a) (qs:exp_quotation #a empty (fun _ -> s))
  : Lemma (ensures (a ⦂ (s, compile_closed qs))) =
  compile_equiv qs;
  equiv_closed_terms #a s (compile_closed qs)

let lemma_compile_closed_arrow_is_elam (#a #b:qType) (#s:get_Type (a ^-> b))
  (qs:exp_quotation #(a ^-> b) empty (fun _ -> s))
  : Lemma (ELam? (compile_closed qs))
  = admit ()
