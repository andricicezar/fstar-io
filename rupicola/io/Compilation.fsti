module Compilation

open FStar.Tactics

open STLC
open QTyp
open QExp
open LogRelSourceTarget
open LogRelTargetSource

let rec _compile #g #a (#s:fs_oval g a) (qs:g ⊢ s) : Tot exp (decreases qs) =
  match qs with
  | Qtt -> EUnit
  | QVar0 -> EVar 0
  | QVarS #g qx -> subst sub_inc (_compile qx)
  | QFd fd -> EFileDescr fd
  | QAppGhost -> EUnit
  | QApp qf qx -> EApp (_compile qf) (_compile qx)
  | QLambda qbody -> ELam (_compile qbody)
  | QFalse -> EFalse
  | QTrue -> ETrue
  | QStringLit s -> EString s
  | QIf qc qt qe -> EIf (_compile qc) (_compile qt) (_compile qe)
  | QMkpair q1 q2 -> EPair (_compile q1) (_compile q2)
  | QFst qp -> EFst (_compile qp)
  | QSnd qp -> ESnd (_compile qp)
  | QInl qp -> EInl (_compile qp)
  | QInr qp -> EInr (_compile qp)
  | QCase cond inlc inrc -> ECase (_compile cond) (_compile inlc) (_compile inrc)
  | QLambdaProd qbody -> ELam (_compile_oprod qbody)
and _compile_oprod #g #a (#s:fs_oprod g a) (qs:oprod_quotation g s) : Tot exp (decreases qs) =
  match qs with
  | QOpenfile qfnm -> EOpen (_compile qfnm)
  | QRead qfd -> ERead (_compile qfd)
  | QWrite qfd qmsg -> EWrite (_compile qfd) (_compile qmsg)
  | QClose qfd -> EClose (_compile qfd)
  | QReturn qx -> _compile qx
  | QBindProd qm qk -> EApp (ELam (_compile_oprod qk)) (_compile_oprod qm)
  | QAppProd qf qx -> EApp (_compile qf) (_compile qx)
  | QIfProd qc qt qe -> EIf (_compile qc) (_compile_oprod qt) (_compile_oprod qe)
  | QCaseProd qcond qinlc qinrc -> ECase (_compile qcond) (_compile_oprod qinlc) (_compile_oprod qinrc)

val compile #g #a (#s:fs_oval g a) (qs:g ⊢ s) : exp

val _compile_eq_compile #g #a (#s:fs_oval g a) (qs:g ⊢ s)
  : Lemma (ensures _compile #g #a #s qs == compile #g #a #s qs)

val lem_compile_superset #g (#a:qType) (#s:fs_oval g a) (qs:g ⊢ s)
  : Lemma (ensures s ⊐ compile qs) (decreases qs)

val lem_compile_subset #g (#a:qType) (#s:fs_oval g a) (qs:g ⊢ s)
  : Lemma (ensures s ⊏ compile qs) (decreases qs)

val lem_compile_closed_arrow_is_elam (#a #b:qType) (#s:fs_val (a ^->!@ b)) (qs: (a ^->!@ b) ⊩ s)
  : Lemma (requires (QLambdaProd? qs))
          (ensures (ELam? (compile qs)))

val lem_compile_closed_valid (#a:qType) (#s:fs_val a) (qs:a ⊩ s)
  : Lemma
    (requires (QLambdaProd? qs))
    (ensures (
        is_closed (compile qs) /\
        is_value (compile qs) /\
        valid_contains s (compile qs) /\
        valid_member_of s (compile qs)
      ))
