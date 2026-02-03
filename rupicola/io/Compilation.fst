module Compilation

open FStar.Tactics

open STLC
open QTyp
open QExp
open ExpRel

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

let lem_compile_empty_closed #a (#s:fs_oval empty a) (qs:empty ⊢ s) : Lemma (is_closed (compile qs)) = admit ()

let compile_closed  #a #s (qs:a ⊩ s) : closed_exp =
  lem_compile_empty_closed qs;
  compile qs

let rec compile_equiv #g (#a:qType) (#s:fs_oval g a) (qs:g ⊢ s)
  : Lemma (ensures (s `equiv_oval a` (compile qs)))
  = match qs with
  | Qtt -> equiv_unit g
  | QVar0 #g' #_ -> equiv_var0 g' a
  | QVarS #g' #_ #b #x qx ->
    compile_equiv qx;
    equiv_varS #g' #a #b x (compile qx)
  | QFd fd -> equiv_file_descr g fd
  | QAppGhost -> equiv_unit g
  | QApp #_ #qa #qb #f #x qf qx ->
    compile_equiv qf;
    compile_equiv qx;
    equiv_app f x (compile qf) (compile qx)
  | QLambda #_ #_ #_ #body qbody ->
    compile_equiv qbody;
    equiv_lam body (compile qbody)
  | QFalse -> equiv_false g
  | QTrue -> equiv_true g
  | QIf #_ #_ #c qc #t qt #e qe ->
    compile_equiv qc;
    compile_equiv qt;
    compile_equiv qe;
    equiv_if c t e (compile qc) (compile qt) (compile qe)
  | QMkpair #_ #a1 #a2 #s1 #s2 q1 q2 ->
    compile_equiv q1;
    compile_equiv q2;
    equiv_pair s1 s2 (compile q1) (compile q2)
  | QFst #_ #_ #_ #p qp ->
    compile_equiv qp;
    equiv_pair_fst_app p (compile qp)
  | QSnd #_ #_ #_ #p qp ->
    compile_equiv qp;
    equiv_pair_snd_app p (compile qp)
  | QInl #_ #_ #t2 #p qp ->
    compile_equiv qp;
    equiv_inl t2 p (compile qp)
  | QInr #_ #t1 #_ #p qp ->
    compile_equiv qp;
    equiv_inr t1 p (compile qp)
  | QCase #_ #_ #_ #_ #cond qcond #inlc qinlc #inrc qinrc ->
    compile_equiv qcond;
    compile_equiv qinlc;
    compile_equiv qinrc;
    equiv_case cond inlc inrc (compile qcond) (compile qinlc) (compile qinrc)
  | QLambdaProd #_ #_ #_ #body qbody ->
    compile_equiv_prod qbody;
    equiv_lam_prod body (compile_oprod qbody)
and compile_equiv_prod #g (#a:qType) (#s:fs_oprod g a) (qs:oprod_quotation g s)
  : Lemma (ensures (s `equiv_oprod a` (compile_oprod qs))) (decreases qs)
  =
  match qs with
  | QOpenfile #_ #fnm qfnm ->
    compile_equiv qfnm;
    equiv_oprod_openfile fnm (compile qfnm)
  | QRead #_ #fd qfd ->
    compile_equiv qfd;
    equiv_oprod_read fd (compile qfd)
  | QWrite #_ #fd #msg qfd qmsg ->
    compile_equiv qfd;
    compile_equiv qmsg;
    equiv_oprod_write fd msg (compile qfd) (compile qmsg)
  | QClose #_ #fd qfd ->
    compile_equiv qfd;
    equiv_oprod_close fd (compile qfd)
  | QReturn #_ #_ #x qx ->
    compile_equiv qx;
    equiv_oprod_return x (compile qx)
  | QBindProd #_ #_ #_ #m #k qm qk ->
    compile_equiv_prod qm;
    compile_equiv_prod qk;
    equiv_oprod_bind m k (compile_oprod qm) (compile_oprod qk)
  | QAppProd #_ #_ #_ #f #x qf qx ->
    compile_equiv qf;
    compile_equiv qx;
    equiv_oprod_app_oval_oval f x (compile qf) (compile qx)
  | QIfProd #_ #_ #c qc #t qt #e qe ->
    compile_equiv qc;
    compile_equiv_prod qt;
    compile_equiv_prod qe;
    equiv_oprod_if_oval c t e (compile qc) (compile_oprod qt) (compile_oprod qe)
  | QCaseProd #_ #_ #_ #_ #cond qcond #inlc qinlc #inrc qinrc ->
    compile_equiv qcond;
    compile_equiv_prod qinlc;
    compile_equiv_prod qinrc;
    equiv_oprod_case_oval cond inlc inrc (compile qcond) (compile_oprod qinlc) (compile_oprod qinrc)

let compile_closed_equiv (#a:qType) (#s:get_Type a) (qs: a ⊩ s)
  : Lemma (ensures (forall h. a ⦂ (h, s, compile_closed qs))) =
  compile_equiv qs;
  lem_equiv_val #a s (compile_closed qs)

let lemma_compile_closed_arrow_is_elam (#a #b:qType) (#s:fs_val (a ^->!@ b))
  (qs:(a ^->!@ b) ⊩ s)
  : Lemma (ELam? (compile_closed qs))
  = admit ()
