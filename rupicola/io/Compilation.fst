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

let rec lem_compile_superset #g (#a:qType) (#s:fs_oval g a) (qs:g ⊢ s)
  : Lemma (ensures (s ⊐ (compile qs))) (decreases qs)
  = match qs with
  | Qtt -> C1.equiv_oval_unit g
  | QVar0 #g' #_ -> C1.equiv_oval_var0 g' a
  | QVarS #g' #_ #b #x qx ->
    lem_compile_superset qx;
    C1.equiv_varS #g' #a #b x (compile qx)
  | QFd fd -> C1.equiv_oval_file_descr g fd
  | QAppGhost -> C1.equiv_oval_unit g
  | QApp #_ #qa #qb #f #x qf qx ->
    lem_compile_superset qf;
    lem_compile_superset qx;
    C1.equiv_oval_app f x (compile qf) (compile qx)
  | QLambda #_ #_ #_ #body qbody ->
    lem_compile_superset qbody;
    C1.equiv_oval_lambda body (compile qbody)
  | QFalse -> C1.equiv_oval_false g
  | QTrue -> C1.equiv_oval_true g
  | QIf #_ #_ #c qc #t qt #e qe ->
    lem_compile_superset qc;
    lem_compile_superset qt;
    lem_compile_superset qe;
    C1.equiv_oval_if c t e (compile qc) (compile qt) (compile qe)
  | QMkpair #_ #a1 #a2 #s1 #s2 q1 q2 ->
    lem_compile_superset q1;
    lem_compile_superset q2;
    C1.equiv_oval_pair s1 s2 (compile q1) (compile q2)
  | QFst #_ #_ #_ #p qp ->
    lem_compile_superset qp;
    C1.equiv_oval_pair_fst p (compile qp)
  | QSnd #_ #_ #_ #p qp ->
    lem_compile_superset qp;
    C1.equiv_oval_pair_snd p (compile qp)
  | QInl #_ #_ #t2 #p qp ->
    lem_compile_superset qp;
    C1.equiv_oval_inl t2 p (compile qp)
  | QInr #_ #t1 #_ #p qp ->
    lem_compile_superset qp;
    C1.equiv_oval_inr t1 p (compile qp)
  | QCase #_ #_ #_ #_ #cond qcond #inlc qinlc #inrc qinrc ->
    lem_compile_superset qcond;
    lem_compile_superset qinlc;
    lem_compile_superset qinrc;
    C1.equiv_oval_case cond inlc inrc (compile qcond) (compile qinlc) (compile qinrc)
  | QLambdaProd #_ #_ #_ #body qbody ->
    lem_compile_superset_prod qbody;
    C1.equiv_oval_lambda_oprod body (compile_oprod qbody)
and lem_compile_superset_prod #g (#a:qType) (#s:fs_oprod g a) (qs:oprod_quotation g s)
  : Lemma (ensures (s ⊒ (compile_oprod qs))) (decreases qs)
  =
  match qs with
  | QOpenfile #_ #fnm qfnm ->
    lem_compile_superset qfnm;
    C1.equiv_oprod_openfile_oval fnm (compile qfnm)
  | QRead #_ #fd qfd ->
    lem_compile_superset qfd;
    C1.equiv_oprod_read_oval fd (compile qfd)
  | QWrite #_ #fd #msg qfd qmsg ->
    lem_compile_superset qfd;
    lem_compile_superset qmsg;
    C1.equiv_oprod_write_oval fd msg (compile qfd) (compile qmsg)
  | QClose #_ #fd qfd ->
    lem_compile_superset qfd;
    C1.equiv_oprod_close_oval fd (compile qfd)
  | QReturn #_ #_ #x qx ->
    lem_compile_superset qx;
    C1.equiv_oprod_return x (compile qx)
  | QBindProd #_ #_ #_ #m #k qm qk ->
    lem_compile_superset_prod qm;
    lem_compile_superset_prod qk;
    C1.equiv_oprod_bind m k (compile_oprod qm) (compile_oprod qk)
  | QAppProd #_ #_ #_ #f #x qf qx ->
    lem_compile_superset qf;
    lem_compile_superset qx;
    C1.equiv_oprod_app_oval_oval f x (compile qf) (compile qx)
  | QIfProd #_ #_ #c qc #t qt #e qe ->
    lem_compile_superset qc;
    lem_compile_superset_prod qt;
    lem_compile_superset_prod qe;
    C1.equiv_oprod_if_oval c t e (compile qc) (compile_oprod qt) (compile_oprod qe)
  | QCaseProd #_ #_ #_ #_ #cond qcond #inlc qinlc #inrc qinrc ->
    lem_compile_superset qcond;
    lem_compile_superset_prod qinlc;
    lem_compile_superset_prod qinrc;
    C1.equiv_oprod_case_oval cond inlc inrc (compile qcond) (compile_oprod qinlc) (compile_oprod qinrc)

let rec lem_compile_subset #g (#a:qType) (#s:fs_oval g a) (qs:g ⊢ s)
  : Lemma (ensures (s ⊏ (compile qs))) (decreases qs)
  = match qs with
  | Qtt -> C2.equiv_oval_unit g
  | QVar0 #g' #_ -> C2.equiv_oval_var0 g' a
  | QVarS #g' #_ #b #x qx ->
    lem_compile_subset qx;
    C2.equiv_varS #g' #a #b x (compile qx)
  | QFd fd -> C2.equiv_oval_file_descr g fd
  | QAppGhost -> C2.equiv_oval_unit g
  | QApp #_ #qa #qb #f #x qf qx ->
    lem_compile_subset qf;
    lem_compile_subset qx;
    C2.equiv_oval_app f x (compile qf) (compile qx)
  | QLambda #_ #_ #_ #body qbody ->
    lem_compile_subset qbody;
    C2.equiv_oval_lambda body (compile qbody)
  | QFalse -> C2.equiv_oval_false g
  | QTrue -> C2.equiv_oval_true g
  | QIf #_ #_ #c qc #t qt #e qe ->
    lem_compile_subset qc;
    lem_compile_subset qt;
    lem_compile_subset qe;
    C2.equiv_oval_if c t e (compile qc) (compile qt) (compile qe)
  | QMkpair #_ #a1 #a2 #s1 #s2 q1 q2 ->
    lem_compile_subset q1;
    lem_compile_subset q2;
    C2.equiv_oval_pair s1 s2 (compile q1) (compile q2)
  | QFst #_ #_ #_ #p qp ->
    lem_compile_subset qp;
    C2.equiv_oval_pair_fst p (compile qp)
  | QSnd #_ #_ #_ #p qp ->
    lem_compile_subset qp;
    C2.equiv_oval_pair_snd p (compile qp)
  | QInl #_ #_ #t2 #p qp ->
    lem_compile_subset qp;
    C2.equiv_oval_inl t2 p (compile qp)
  | QInr #_ #t1 #_ #p qp ->
    lem_compile_subset qp;
    C2.equiv_oval_inr t1 p (compile qp)
  | QCase #_ #_ #_ #_ #cond qcond #inlc qinlc #inrc qinrc ->
    lem_compile_subset qcond;
    lem_compile_subset qinlc;
    lem_compile_subset qinrc;
    C2.equiv_oval_case cond inlc inrc (compile qcond) (compile qinlc) (compile qinrc)
  | QLambdaProd #_ #_ #_ #body qbody ->
    lem_compile_subset_prod qbody;
    C2.equiv_oval_lambda_oprod body (compile_oprod qbody)
and lem_compile_subset_prod #g (#a:qType) (#s:fs_oprod g a) (qs:oprod_quotation g s)
  : Lemma (ensures (s ⊑ (compile_oprod qs))) (decreases qs)
  =
  match qs with
  | QOpenfile #_ #fnm qfnm ->
    lem_compile_subset qfnm;
    C2.equiv_oprod_openfile_oval fnm (compile qfnm)
  | QRead #_ #fd qfd ->
    lem_compile_subset qfd;
    C2.equiv_oprod_read_oval fd (compile qfd)
  | QWrite #_ #fd #msg qfd qmsg ->
    lem_compile_subset qfd;
    lem_compile_subset qmsg;
    C2.equiv_oprod_write_oval fd msg (compile qfd) (compile qmsg)
  | QClose #_ #fd qfd ->
    lem_compile_subset qfd;
    C2.equiv_oprod_close_oval fd (compile qfd)
  | QReturn #_ #_ #x qx ->
    lem_compile_subset qx;
    C2.equiv_oprod_return x (compile qx)
  | QBindProd #_ #_ #_ #m #k qm qk ->
    lem_compile_subset_prod qm;
    lem_compile_subset_prod qk;
    C2.equiv_oprod_bind m k (compile_oprod qm) (compile_oprod qk)
  | QAppProd #_ #_ #_ #f #x qf qx ->
    lem_compile_subset qf;
    lem_compile_subset qx;
    C2.equiv_oprod_app_oval_oval f x (compile qf) (compile qx)
  | QIfProd #_ #_ #c qc #t qt #e qe ->
    lem_compile_subset qc;
    lem_compile_subset_prod qt;
    lem_compile_subset_prod qe;
    C2.equiv_oprod_if_oval c t e (compile qc) (compile_oprod qt) (compile_oprod qe)
  | QCaseProd #_ #_ #_ #_ #cond qcond #inlc qinlc #inrc qinrc ->
    lem_compile_subset qcond;
    lem_compile_subset_prod qinlc;
    lem_compile_subset_prod qinrc;
    C2.equiv_oprod_case_oval cond inlc inrc (compile qcond) (compile_oprod qinlc) (compile_oprod qinrc)

let lem_compile_closed_arrow_is_elam (#a #b:qType) (#s:fs_val (a ^->!@ b))
  (qs:(a ^->!@ b) ⊩ s)
  : Lemma (ELam? (compile qs))
  = admit ()

let lem_compile_closed_valid (#a:qType) (#s:fs_val a) (qs:a ⊩ s) =
  assume (is_closed (compile qs));
  assume (is_value (compile qs));
  lem_compile_superset qs;
  lem_value_superset_valid_contains a s (compile qs);
  lem_compile_subset qs;
  lem_value_subset_valid_member_of a s (compile qs)
