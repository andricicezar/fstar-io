(* Encoding of PURE *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util structures.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Definition pure_wp' A := (A → Prop) → Prop.

Definition pure_mono [A] (w : pure_wp' A) : Prop :=
  ∀ (P Q : A → Prop), (∀ x, P x → Q x) → w P → w Q.

Definition pure_wp A :=
  { w : pure_wp' A | pure_mono w }.

Definition PURE A (w : pure_wp A) :=
  val w (λ _, True) → { x : A | ∀ P, val w P → P x }.

(* ReqMonad instance for pure_wp *)

Definition pure_wp_struct : ReqMonad.
Proof.
  exists pure_wp.
  - intros A x.
    exists (λ post, post x).
    cbv. auto.
  - intros A B w wf.
    exists (λ post, val w (λ x, val (wf x) post)).
    destruct w as [w mw].
    cbv. intros P Q hPQ h.
    eapply mw. 2: exact h.
    simpl. intros x hx. destruct (wf x) as [wf' h'].
    eapply h'. 2: exact hx.
    auto.
  - intro p.
    exists (λ post, ∃ (h : p), post h).
    cbv. intros P Q hPQ h.
    destruct h as [hp h]. exists hp.
    auto.
Defined.

Definition spec_lift_pure (W : ReqMonad) :=
  ∀ A (w : pure_wp A), W A.

Class PureSpec (W : ReqMonad) (Word : Order W) (liftᵂ : spec_lift_pure W) := {
  req_lift :
    ∀ A w (f : PURE A w),
      W.(bind) (W.(req) (val w (λ _, True))) (λ h, W.(ret) (val (f h))) ≤ᵂ
      liftᵂ _ w
}.