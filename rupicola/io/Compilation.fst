module Compilation

open FStar.Tactics

open STLC
open QTyp
open QExp
open LogRelSourceTarget
open LogRelTargetSource
module C1 = LogRelSourceTarget.CompatibilityLemmas
module C2 = LogRelTargetSource.CompatibilityLemmas

let rec compile #g #a (#s:fs_oval g a) (qs:g ⊢ s) : Tot exp (decreases qs) =
  match qs with
  | Qtt -> EUnit
  | QVar0 -> EVar 0
  | QVarS #g qx -> subst sub_inc (compile qx)
  | QFd fd -> EFileDescr fd
  | QAppGhost -> EUnit
  | QApp qf qx -> EApp (compile qf) (compile qx)
  | QLambda qbody -> ELam (compile qbody)
  | QFalse -> EFalse
  | QTrue -> ETrue
  | QIf qc qt qe -> EIf (compile qc) (compile qt) (compile qe)
  | QMkpair q1 q2 -> EPair (compile q1) (compile q2)
  | QFst qp -> EFst (compile qp)
  | QSnd qp -> ESnd (compile qp)
  | QInl qp -> EInl (compile qp)
  | QInr qp -> EInr (compile qp)
  | QCase cond inlc inrc -> ECase (compile cond) (compile inlc) (compile inrc)
  | QLambdaProd qbody -> ELam (compile_oprod qbody)
and compile_oprod #g #a (#s:fs_oprod g a) (qs:oprod_quotation g s) : Tot exp (decreases qs) =
  match qs with
  | QOpenfile qfnm -> EOpen (compile qfnm)
  | QRead qfd -> ERead (compile qfd)
  | QWrite qfd qmsg -> EWrite (compile qfd) (compile qmsg)
  | QClose qfd -> EClose (compile qfd)
  | QReturn qx -> compile qx
  | QBindProd qm qk -> EApp (ELam (compile_oprod qk)) (compile_oprod qm)
  | QAppProd qf qx -> EApp (compile qf) (compile qx)
  | QIfProd qc qt qe -> EIf (compile qc) (compile_oprod qt) (compile_oprod qe)
  | QCaseProd qcond qinlc qinrc -> ECase (compile qcond) (compile_oprod qinlc) (compile_oprod qinrc)

let rec lem_compile_equiv #g (#a:qType) (#s:fs_oval g a) (qs:g ⊢ s)
  : Lemma (ensures (s ⊐ (compile qs))) (decreases qs)
  = match qs with
  | Qtt -> C1.equiv_oval_unit g
  | QVar0 #g' #_ -> C1.equiv_oval_var0 g' a
  | QVarS #g' #_ #b #x qx ->
    lem_compile_equiv qx;
    C1.equiv_varS #g' #a #b x (compile qx)
  | QFd fd -> C1.equiv_oval_file_descr g fd
  | QAppGhost -> C1.equiv_oval_unit g
  | QApp #_ #qa #qb #f #x qf qx ->
    lem_compile_equiv qf;
    lem_compile_equiv qx;
    C1.equiv_oval_app f x (compile qf) (compile qx)
  | QLambda #_ #_ #_ #body qbody ->
    lem_compile_equiv qbody;
    C1.equiv_oval_lambda body (compile qbody)
  | QFalse -> C1.equiv_oval_false g
  | QTrue -> C1.equiv_oval_true g
  | QIf #_ #_ #c qc #t qt #e qe ->
    lem_compile_equiv qc;
    lem_compile_equiv qt;
    lem_compile_equiv qe;
    C1.equiv_oval_if c t e (compile qc) (compile qt) (compile qe)
  | QMkpair #_ #a1 #a2 #s1 #s2 q1 q2 ->
    lem_compile_equiv q1;
    lem_compile_equiv q2;
    C1.equiv_oval_pair s1 s2 (compile q1) (compile q2)
  | QFst #_ #_ #_ #p qp ->
    lem_compile_equiv qp;
    C1.equiv_oval_pair_fst p (compile qp)
  | QSnd #_ #_ #_ #p qp ->
    lem_compile_equiv qp;
    C1.equiv_oval_pair_snd p (compile qp)
  | QInl #_ #_ #t2 #p qp ->
    lem_compile_equiv qp;
    C1.equiv_oval_inl t2 p (compile qp)
  | QInr #_ #t1 #_ #p qp ->
    lem_compile_equiv qp;
    C1.equiv_oval_inr t1 p (compile qp)
  | QCase #_ #_ #_ #_ #cond qcond #inlc qinlc #inrc qinrc ->
    lem_compile_equiv qcond;
    lem_compile_equiv qinlc;
    lem_compile_equiv qinrc;
    C1.equiv_oval_case cond inlc inrc (compile qcond) (compile qinlc) (compile qinrc)
  | QLambdaProd #_ #_ #_ #body qbody ->
    lem_compile_equiv_prod qbody;
    C1.equiv_oval_lambda_oprod body (compile_oprod qbody)
and lem_compile_equiv_prod #g (#a:qType) (#s:fs_oprod g a) (qs:oprod_quotation g s)
  : Lemma (ensures (s ⊒ (compile_oprod qs))) (decreases qs)
  =
  match qs with
  | QOpenfile #_ #fnm qfnm ->
    lem_compile_equiv qfnm;
    C1.equiv_oprod_openfile_oval fnm (compile qfnm)
  | QRead #_ #fd qfd ->
    lem_compile_equiv qfd;
    C1.equiv_oprod_read_oval fd (compile qfd)
  | QWrite #_ #fd #msg qfd qmsg ->
    lem_compile_equiv qfd;
    lem_compile_equiv qmsg;
    C1.equiv_oprod_write_oval fd msg (compile qfd) (compile qmsg)
  | QClose #_ #fd qfd ->
    lem_compile_equiv qfd;
    C1.equiv_oprod_close_oval fd (compile qfd)
  | QReturn #_ #_ #x qx ->
    lem_compile_equiv qx;
    C1.equiv_oprod_return x (compile qx)
  | QBindProd #_ #_ #_ #m #k qm qk ->
    lem_compile_equiv_prod qm;
    lem_compile_equiv_prod qk;
    C1.equiv_oprod_bind m k (compile_oprod qm) (compile_oprod qk)
  | QAppProd #_ #_ #_ #f #x qf qx ->
    lem_compile_equiv qf;
    lem_compile_equiv qx;
    C1.equiv_oprod_app_oval_oval f x (compile qf) (compile qx)
  | QIfProd #_ #_ #c qc #t qt #e qe ->
    lem_compile_equiv qc;
    lem_compile_equiv_prod qt;
    lem_compile_equiv_prod qe;
    C1.equiv_oprod_if_oval c t e (compile qc) (compile_oprod qt) (compile_oprod qe)
  | QCaseProd #_ #_ #_ #_ #cond qcond #inlc qinlc #inrc qinrc ->
    lem_compile_equiv qcond;
    lem_compile_equiv_prod qinlc;
    lem_compile_equiv_prod qinrc;
    C1.equiv_oprod_case_oval cond inlc inrc (compile qcond) (compile_oprod qinlc) (compile_oprod qinrc)

let lem_compile_closed_arrow_is_elam (#a #b:qType) (#s:fs_val (a ^->!@ b))
  (qs:(a ^->!@ b) ⊩ s)
  : Lemma (ELam? (compile qs))
  = admit ()

let lem_compile_closed_valid (#a:qType) (#s:fs_val a) (qs:a ⊩ s) =
  assume (is_closed (compile qs));
  assume (is_value (compile qs));
  assume (valid_contains s (compile qs));
  assume (valid_member_of s (compile qs))

(**
val compile_prog_equiv #i (ps:progS i)
  : Lemma (ensures (forall h. (i.ct ^->!@ qBool) ∋ (h, dfst ps, compile_closed (dsnd ps))))
let compile_prog_equiv #i pS =
    let t : qType = i.ct in
    let (| ps, qps |) = pS in
    let pt : progT (comp_int i) = compile_prog pS in
    compile_closed_equiv qps;
    assert (forall h. (t ^->!@ qBool) ⊇ (h, ps, pt));
    lemma_compile_closed_arrow_is_elam qps;
    assert (ELam? pt /\ is_closed pt);
    lem_value_is_irred pt;
    assert (is_value pt);
    lem_value_is_irred pt;
    introduce forall h. (t ^->!@ qBool) ∋ (h, ps, pt) with begin
      eliminate forall (pt':closed_exp) lt.
        steps pt pt' h lt ==> indexed_irred pt' (h++lt) ==>
        ((t ^->!@ qBool) ∋ (h, ps, pt') /\ lt == []) with pt []
    end
**)
