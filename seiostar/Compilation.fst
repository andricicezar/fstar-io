module Compilation

open FStar.Tactics

open LambdaIO
open QTypes.OpenValComp
open RQ.TypingRelation
open LogRelSourceTarget
open LogRelTargetSource

module C1 = LogRelTargetSource.CompatibilityLemmas
module C2 = LogRelSourceTarget.CompatibilityLemmas

let rec compile #g #a #pre (#s:fs_oval g a pre) (qs:g ⊢ s) : Tot exp (decreases qs) =
  match qs with
  | Qtt -> EUnit
  | QAxiom -> EVar 0
  | QWeaken #g qx -> subst sub_inc (compile qx)
  | QFd fd -> EFileDescr fd
  | QApp qf qx -> EApp (compile qf) (compile qx)
  | QLambda qbody -> ELam (compile qbody)
  | QFalse -> EFalse
  | QTrue -> ETrue
  | QStringLit s -> EString s
  | QStringEq s1 s2 -> EStringEq (compile s1) (compile s2)
  | QIf qc qt qe -> EIf (compile qc) (compile qt) (compile qe)
  | QMkpair q1 q2 -> EPair (compile q1) (compile q2)
  | QFst qp -> EFst (compile qp)
  | QSnd qp -> ESnd (compile qp)
  | QInl qp -> EInl (compile qp)
  | QInr qp -> EInr (compile qp)
  | QCase cond inlc inrc -> ECase (compile cond) (compile inlc) (compile inrc)
  | QLambdaIO qbody -> ELam (compile_ocomp qbody)
  // | QSeqGhost _ _ qk -> compile qk  -- QSeqGhost is commented out in RQ.TypingRelation
  | QRetype qv -> compile qv
and compile_ocomp #g #a #pre (#s:fs_ocomp g a pre) (qs:typing_io g s) : Tot exp (decreases qs) =
  match qs with
  | QCall o qargs -> ECall o (compile qargs)
  | QReturn qx -> compile qx
  | QBind qm qk -> EApp (ELam (compile_ocomp qk)) (compile_ocomp qm)
  | QAppIO qf qx -> EApp (compile qf) (compile qx)
  | QIfIO qc qt qe -> EIf (compile qc) (compile_ocomp qt) (compile_ocomp qe)
  | QCaseIO qcond qinlc qinrc -> ECase (compile qcond) (compile_ocomp qinlc) (compile_ocomp qinrc)

let rec lem_compile_superset #g #pre (#a:qType) (#s:fs_oval g a pre) (qs:g ⊢ s)
  : Lemma (ensures (s ⊐ (compile qs))) (decreases qs)
  = match qs with
  | Qtt -> C1.compat_oval_unit g
  | QAxiom #g' #_ -> C1.compat_oval_axiom g' a
  | QWeaken #g' #_ #b #pre' #x qx ->
    lem_compile_superset qx;
    C1.compat_weaken #g' #a #b #pre' x (compile qx)
  | QFd fd -> C1.compat_oval_file_descr g fd
  | QApp #_ #qa #qb #preF #_ #f #preX #x qf qx ->
    lem_compile_superset qf;
    lem_compile_superset qx;
    C1.compat_oval_app #_ #preF #preX #qa #qb f x (compile qf) (compile qx)
  | QLambda #_ #_ #_ #_ #body qbody ->
    lem_compile_superset qbody;
    C1.compat_oval_lambda body (compile qbody)
  | QFalse -> C1.compat_oval_false g
  | QTrue -> C1.compat_oval_true g
  | QStringLit #_ str -> C1.compat_oval_string g str
  | QStringEq #_ #_ #s1 qs1 #_ #s2 qs2 ->
    lem_compile_superset qs1;
    lem_compile_superset qs2;
    C1.compat_oval_string_eq s1 s2 (compile qs1) (compile qs2)
  | QIf #_ #_ #_ #c qc #_ #t qt #_ #e qe ->
    lem_compile_superset qc;
    lem_compile_superset qt;
    lem_compile_superset qe;
    C1.compat_oval_if c t e (compile qc) (compile qt) (compile qe)
  | QMkpair #_ #a1 #a2 #_ #s1 #_ #s2 q1 q2 ->
    lem_compile_superset q1;
    lem_compile_superset q2;
    C1.compat_oval_pair s1 s2 (compile q1) (compile q2)
  | QFst #_ #_ #_ #_ #p qp ->
    lem_compile_superset qp;
    C1.compat_oval_pair_fst p (compile qp)
  | QSnd #_ #_ #_ #_ #p qp ->
    lem_compile_superset qp;
    C1.compat_oval_pair_snd p (compile qp)
  | QInl #_ #_ #t2 #_ #p qp ->
    lem_compile_superset qp;
    C1.compat_oval_inl t2 p (compile qp)
  | QInr #_ #t1 #_ #_ #p qp ->
    lem_compile_superset qp;
    C1.compat_oval_inr t1 p (compile qp)
  | QCase #_ #_ #_ #_ #_ #cond qcond #_ #inlc qinlc #_ #inrc qinrc ->
    lem_compile_superset qcond;
    lem_compile_superset qinlc;
    lem_compile_superset qinrc;
    C1.compat_oval_case cond inlc inrc (compile qcond) (compile qinlc) (compile qinrc)
  | QLambdaIO #_ #_ #_ #_ #body qbody ->
    lem_compile_superset_comp qbody;
    C1.compat_oval_lambda_ocomp body (compile_ocomp qbody)
  // | QSeqGhost _ _ #_ #_ #k qk ->
  //   lem_compile_superset qk;
  //   admit ()
  | QRetype #_ #_ #_ #v qv #b ->
    lem_compile_superset qv;
    C1.compat_oval_retype v b (compile qv)
and lem_compile_superset_comp #g #pre (#a:qType) (#s:fs_ocomp g a pre) (qs:typing_io g s)
  : Lemma (ensures (s ⊒ (compile_ocomp qs))) (decreases qs)
  =
  match qs with
  | QCall o #_ #args qargs ->
    lem_compile_superset qargs;
    C1.compat_ocomp_call_oval o args (compile qargs)
  | QReturn #_ #_ #_ #x qx ->
    lem_compile_superset qx;
    C1.compat_ocomp_return x (compile qx)
  | QBind #_ #_ #_ #_ #m #_ #k qm qk ->
    lem_compile_superset_comp qm;
    lem_compile_superset_comp qk;
    C1.compat_ocomp_bind m k (compile_ocomp qm) (compile_ocomp qk)
  | QAppIO #_ #_ #_ #_ #f #_ #x qf qx ->
    lem_compile_superset qf;
    lem_compile_superset qx;
    C1.compat_ocomp_app_oval_oval f x (compile qf) (compile qx)
  | QIfIO #_ #_ #_ #c qc #_ #t qt #_ #e qe ->
    lem_compile_superset qc;
    lem_compile_superset_comp qt;
    lem_compile_superset_comp qe;
    C1.compat_ocomp_if_oval c t e (compile qc) (compile_ocomp qt) (compile_ocomp qe)
  | QCaseIO #_ #_ #_ #_ #_ #cond qcond #_ #inlc qinlc #_ #inrc qinrc ->
    lem_compile_superset qcond;
    lem_compile_superset_comp qinlc;
    lem_compile_superset_comp qinrc;
    C1.compat_ocomp_case_oval cond inlc inrc (compile qcond) (compile_ocomp qinlc) (compile_ocomp qinrc)

let rec lem_compile_subset #g #pre (#a:qType) (#s:fs_oval g a pre) (qs:g ⊢ s)
  : Lemma (ensures (s ⊏ (compile qs))) (decreases qs)
  = match qs with
  | Qtt -> C2.compat_oval_unit g
  | QAxiom #g' #_ -> C2.compat_oval_axiom g' a
  | QWeaken #g' #_ #b #preX #x qx ->
    lem_compile_subset qx;
    C2.compat_weaken #g' #a #b #preX x (compile qx)
  | QFd fd -> C2.compat_oval_file_descr g fd
  | QApp #_ #qa #qb #preF #_ #f #preX #x qf qx ->
    lem_compile_subset qf;
    lem_compile_subset qx;
    C2.compat_oval_app #_ #preF #preX #qa #qb f x (compile qf) (compile qx)
  | QLambda #_ #_ #_ #_ #body qbody ->
    lem_compile_subset qbody;
    C2.compat_oval_lambda body (compile qbody)
  | QFalse -> C2.compat_oval_false g
  | QTrue -> C2.compat_oval_true g
  | QStringLit #_ str -> C2.compat_oval_string g str
  | QStringEq #_ #_ #s1 qs1 #_ #s2 qs2 ->
    lem_compile_subset qs1;
    lem_compile_subset qs2;
    C2.compat_oval_string_eq s1 s2 (compile qs1) (compile qs2)
  | QIf #_ #_ #_ #c qc #_ #t qt #_ #e qe ->
    lem_compile_subset qc;
    lem_compile_subset qt;
    lem_compile_subset qe;
    C2.compat_oval_if c t e (compile qc) (compile qt) (compile qe)
  | QMkpair #_ #a1 #a2 #_ #s1 #_ #s2 q1 q2 ->
    lem_compile_subset q1;
    lem_compile_subset q2;
    C2.compat_oval_pair s1 s2 (compile q1) (compile q2)
  | QFst #_ #_ #_ #_ #p qp ->
    lem_compile_subset qp;
    C2.compat_oval_pair_fst p (compile qp)
  | QSnd #_ #_ #_ #_ #p qp ->
    lem_compile_subset qp;
    C2.compat_oval_pair_snd p (compile qp)
  | QInl #_ #_ #t2 #_ #p qp ->
    lem_compile_subset qp;
    C2.compat_oval_inl t2 p (compile qp)
  | QInr #_ #t1 #_ #_ #p qp ->
    lem_compile_subset qp;
    C2.compat_oval_inr t1 p (compile qp)
  | QCase #_ #_ #_ #_ #_ #cond qcond #_ #inlc qinlc #_ #inrc qinrc ->
    lem_compile_subset qcond;
    lem_compile_subset qinlc;
    lem_compile_subset qinrc;
    C2.compat_oval_case cond inlc inrc (compile qcond) (compile qinlc) (compile qinrc)
  | QLambdaIO #_ #_ #_ #_ #body qbody ->
    lem_compile_subset_comp qbody;
    C2.compat_oval_lambda_ocomp body (compile_ocomp qbody)
//  | QSeqGhost _ _ #_ #_ #k qk ->
//    lem_compile_subset qk;
//    admit ()
  | QRetype #_ #_ #_ #v qv #b ->
    lem_compile_subset qv;
    C2.compat_oval_retype v b (compile qv)
and lem_compile_subset_comp #g #pre (#a:qType) (#s:fs_ocomp g a pre) (qs:typing_io g s)
  : Lemma (ensures (s ⊑ (compile_ocomp qs))) (decreases qs)
  =
  match qs with
  | QCall o #_ #args qargs ->
    lem_compile_subset qargs;
    C2.compat_ocomp_call_oval o args (compile qargs)
  | QReturn #_ #_ #_ #x qx ->
    lem_compile_subset qx;
    C2.compat_ocomp_return x (compile qx)
  | QBind #_ #_ #_ #_ #m #_ #k qm qk ->
    lem_compile_subset_comp qm;
    lem_compile_subset_comp qk;
    C2.compat_ocomp_bind m k (compile_ocomp qm) (compile_ocomp qk)
  | QAppIO #_ #_ #_ #_ #f #_ #x qf qx ->
    lem_compile_subset qf;
    lem_compile_subset qx;
    C2.compat_ocomp_app_oval_oval f x (compile qf) (compile qx)
  | QIfIO #_ #_ #_ #c qc #_ #t qt #_ #e qe ->
    lem_compile_subset qc;
    lem_compile_subset_comp qt;
    lem_compile_subset_comp qe;
    C2.compat_ocomp_if_oval c t e (compile qc) (compile_ocomp qt) (compile_ocomp qe)
  | QCaseIO #_ #_ #_ #_ #_ #cond qcond #_ #inlc qinlc #_ #inrc qinrc ->
    lem_compile_subset qcond;
    lem_compile_subset_comp qinlc;
    lem_compile_subset_comp qinrc;
    C2.compat_ocomp_case_oval cond inlc inrc (compile qcond) (compile_ocomp qinlc) (compile_ocomp qinrc)

let rec lem_compile_fv_in_env #g #pre (#a:qType) (#s:fs_oval g a pre) (qs:g ⊢ s)
  : Lemma (ensures fv_in_env g (compile qs)) (decreases qs)
  = match qs with
  | Qtt -> ()
  | QAxiom -> ()
  | QWeaken #g' #_ #b #x qx ->
    lem_compile_fv_in_env qx;
    lem_fv_in_env_weaken g' b (compile qx)
  | QFd _ -> ()
  | QApp qf qx ->
    lem_compile_fv_in_env qf;
    lem_compile_fv_in_env qx;
    lem_fv_in_env_app g (compile qf) (compile qx)
  | QLambda #qa #_ #_ #body qbody ->
    lem_compile_fv_in_env qbody;
    lem_fv_in_env_lam g qa (compile qbody)
  | QFalse -> ()
  | QTrue -> ()
  | QStringLit _ -> ()
  | QStringEq qs1 qs2 ->
    lem_compile_fv_in_env qs1;
    lem_compile_fv_in_env qs2;
    lem_fv_in_env_string_eq g (compile qs1) (compile qs2)
  | QIf qc qt qe ->
    lem_compile_fv_in_env qc;
    lem_compile_fv_in_env qt;
    lem_compile_fv_in_env qe;
    lem_fv_in_env_if g (compile qc) (compile qt) (compile qe)
  | QMkpair q1 q2 ->
    lem_compile_fv_in_env q1;
    lem_compile_fv_in_env q2;
    lem_fv_in_env_pair g (compile q1) (compile q2)
  | QFst qp ->
    lem_compile_fv_in_env qp;
    lem_fv_in_env_fst g (compile qp)
  | QSnd qp ->
    lem_compile_fv_in_env qp;
    lem_fv_in_env_snd g (compile qp)
  | QInl qp ->
    lem_compile_fv_in_env qp;
    lem_fv_in_env_inl g (compile qp)
  | QInr qp ->
    lem_compile_fv_in_env qp;
    lem_fv_in_env_inr g (compile qp)
  | QCase #_ #ta #tb #_ #cond qcond #inlc qinlc #inrc qinrc ->
    lem_compile_fv_in_env qcond;
    lem_compile_fv_in_env qinlc;
    lem_compile_fv_in_env qinrc;
    lem_fv_in_env_case g ta tb (compile qcond) (compile qinlc) (compile qinrc)
  | QLambdaIO #_ #qa #_ #body qbody ->
    lem_compile_fv_in_env_prod qbody;
    lem_fv_in_env_lam g qa (compile_ocomp qbody)
//  | QSeqGhost _ _ #_ #_ #k qk ->
//    lem_compile_fv_in_env qk
  | QRetype qv ->
    lem_compile_fv_in_env qv
and lem_compile_fv_in_env_prod #g #pre (#a:qType) (#s:fs_ocomp g a pre) (qs:typing_io g s)
  : Lemma (ensures fv_in_env g (compile_ocomp qs)) (decreases qs)
  = match qs with
  | QCall o qargs ->
    lem_compile_fv_in_env qargs;
    lem_fv_in_env_call g o (compile qargs)
  | QReturn qx ->
    lem_compile_fv_in_env qx
  | QBind #_ #ta #_ #m #k qm qk ->
    lem_compile_fv_in_env_prod qm;
    lem_compile_fv_in_env_prod qk;
    lem_fv_in_env_lam g ta (compile_ocomp qk);
    lem_fv_in_env_app g (ELam (compile_ocomp qk)) (compile_ocomp qm)
  | QAppIO qf qx ->
    lem_compile_fv_in_env qf;
    lem_compile_fv_in_env qx;
    lem_fv_in_env_app g (compile qf) (compile qx)
  | QIfIO qc qt qe ->
    lem_compile_fv_in_env qc;
    lem_compile_fv_in_env_prod qt;
    lem_compile_fv_in_env_prod qe;
    lem_fv_in_env_if g (compile qc) (compile_ocomp qt) (compile_ocomp qe)
  | QCaseIO #_ #ta #tb #_ #cond qcond #inlc qinlc #inrc qinrc ->
    lem_compile_fv_in_env qcond;
    lem_compile_fv_in_env_prod qinlc;
    lem_compile_fv_in_env_prod qinrc;
    lem_fv_in_env_case g ta tb (compile qcond) (compile_ocomp qinlc) (compile_ocomp qinrc)

let lem_compile_closed_arrow_is_elam (#a #b:qType) (#s:fs_val (a ^->!@ b))
  (qs:(a ^->!@ b) ⊫ s)
  : Lemma (requires (QLambdaIO? qs._3))
          (ensures (ELam? (compile qs._3)))
  =
  match qs._3 with
  | QLambdaIO qbody ->
    assert (ELam? (compile qs._3)) by (norm [delta_once [`%compile];zeta;iota])

let lem_compile_is_closed (#a:qType) (#s:fs_val a) (qs:a ⊫ s)
  : Lemma (is_closed (compile qs._3))
  = lem_compile_fv_in_env qs._3

let lem_compile_closed_valid (#a:qType) (#s:fs_val a) (qs:a ⊫ s)
  : Lemma
    (requires (QLambdaIO? qs._3))
    (ensures (
        is_closed (compile qs._3) /\
        is_value (compile qs._3) /\
        valid_contains s (compile qs._3) /\
        valid_member_of s (compile qs._3)
      )) =
  match qs._3 with
  | QLambdaIO #_ #b #c qbody ->
    lem_compile_is_closed qs;
    lem_compile_closed_arrow_is_elam #b #c #s qs;
    assert (is_value (compile qs._3));
    lem_compile_superset qs._3;
    lem_value_superset_valid_contains a #qs._1 (fun _ -> s) (compile qs._3);
    lem_compile_subset qs._3;
    lem_value_subset_valid_member_of a (fun _ -> s) (compile qs._3)
