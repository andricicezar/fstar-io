module Compilation

open FStar.Tactics

open STLC
open QTyp
open QExp
open ExpRel

let rec compile #g #a (#s:fs_oexp g a) (qs:exp_quotation g s) : Tot exp (decreases qs) =
  match qs with
  | Qtt -> EUnit
  | QVar0 -> EVar 0
  | QVar1 -> EVar 1
  | QVar2 -> EVar 2
  | QApp qf qx -> EApp (compile qf) (compile qx)
  | QLambda qbody -> ELam (compile qbody)
  | QFalse -> EFalse
  | QTrue -> ETrue
  | QIf qc qt qe -> EIf (compile qc) (compile qt) (compile qe)
  | QMkpair q1 q2 -> EPair (compile q1) (compile q2)
  | QFst qp -> EFst (compile qp)
  | QSnd qp -> ESnd (compile qp)


let lem_compile_empty_closed #a (#s:fs_oexp empty a) (qs:exp_quotation empty s) : Lemma (is_closed (compile qs)) = admit ()

let compile_closed (#a:qType) (#s:get_Type a) (qs:exp_quotation #a empty (fun _ -> s)) : closed_exp =
  lem_compile_empty_closed qs;
  compile qs

let rec compile_equiv #g (#fs_tr:list fs_event) (#tr:list event) (#a:qType) (#s:fs_oexp g a) (qs:exp_quotation g s)
  : Lemma (ensures (equiv #g #fs_tr #tr a s (compile qs))) (decreases qs)
  = match qs with
  | Qtt -> equiv_unit g #fs_tr #tr
  | QVar0 -> admit () // equiv_var g 0
  | QVar1 -> admit () // equiv_var g 1
  | QVar2 -> admit () //equiv_var g 2
  | QApp #_ #qa #qb #f #x qf qx ->
    compile_equiv #g #fs_tr #tr qf;
    compile_equiv #g #fs_tr #tr qx;
    equiv_app #g #fs_tr #tr f x (compile qf) (compile qx)
  | QLambda #_ #a #b #f qbody -> admit ()
    (*compile_equiv #(extend a g) #fs_tr #tr qbody;
    equiv_lam #g #fs_tr #tr _ _ f (compile qbody);
    //assert (equiv #g #fs_tr #tr a s (ELam (compile qbody)));
    assume (equiv #g #fs_tr #tr a s (compile qs)) (*by (
      norm [delta_only [`%compile]; zeta;iota];
      rewrite_eqs_from_context ();
      assumption ())*)*)
  | QFalse -> equiv_false g #fs_tr #tr
  | QTrue -> equiv_true g #fs_tr #tr
  | QIf #_ #_ #c qc #t qt #e qe ->
    compile_equiv #g #fs_tr #tr qc;
    compile_equiv #g #fs_tr #tr qt;
    compile_equiv #g #fs_tr #tr qe;
    equiv_if #g #fs_tr #tr c t e (compile qc) (compile qt) (compile qe)
  | QMkpair #_ #a1 #a2 #s1 #s2 q1 q2 ->
    compile_equiv #g #fs_tr #tr q1;
    compile_equiv #g #fs_tr #tr q2;
    equiv_pair #g #fs_tr #tr s1 s2 (compile q1) (compile q2)
  | QFst #_ #_ #_ #p qp ->
    compile_equiv #g #fs_tr #tr qp;
    equiv_pair_fst_app #g #fs_tr #tr p (compile qp)
  | QSnd #_ #_ #_ #p qp ->
    compile_equiv #g #fs_tr #tr qp;
    equiv_pair_snd_app #g #fs_tr #tr p (compile qp)

let compile_closed_equiv (#a:qType) (#s:get_Type a) (#fs_tr:list fs_event) (#tr:list event) (qs:exp_quotation #a empty (fun _ -> s))
  : Lemma (ensures (a ⦂ ((s, fs_tr), (compile_closed qs, tr)))) =
  compile_equiv #empty #fs_tr #tr qs;
  equiv_closed_terms #fs_tr #tr #a s (compile_closed qs)

let lemma_compile_closed_arrow_is_elam (#a #b:qType) (#s:get_Type (a ^-> b))
  (qs:exp_quotation #(a ^-> b) empty (fun _ -> s))
  : Lemma (ELam? (compile_closed qs))
  = admit ()
