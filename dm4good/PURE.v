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

#[export] Instance pure_wp_monad : Monad pure_wp.
Proof.
  constructor.
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
Defined.

#[export] Instance pure_wp_reqmon : ReqMonad pure_wp.
Proof.
  constructor.
  intro p.
  exists (λ post, ∃ (h : p), post h).
  cbv. intros P Q hPQ h.
  destruct h as [hp h]. exists hp.
  auto.
Defined.

#[export] Instance pure_wp_ord : Order pure_wp.
Proof.
  unshelve eexists.
  - intros A w₀ w₁. exact (∀ post, val w₁ post → val w₀ post).
  - intros A. intros w₀ w₁ w₂ h₀₁ h₁₂. intros post h.
    apply h₀₁. apply h₁₂. assumption.
Defined.

#[export] Instance pure_wp_refl [A] : Reflexive (wle (A := A)).
Proof.
  intro w. intros p h. assumption.
Qed.

#[export] Instance MonoSpec_pure : MonoSpec pure_wp.
Proof.
  constructor.
  intros A B w w' wf wf' hw hwf.
  intros post h.
  simpl. simpl in h.
  eapply hw. destruct w' as [w' hw'].
  eapply hw'. 2: exact h.
  simpl. intro x. apply hwf.
Qed.

Definition spec_lift_pure (W : Type → Type) :=
  ∀ A (w : pure_wp A), W A.

Class PureSpec W `{ReqMonad W} (Word : Order W) (liftᵂ : spec_lift_pure W) := {
  req_lift :
    ∀ A w (f : PURE A w),
      bind (req (val w (λ _, True))) (λ h, ret (val (f h))) ≤ᵂ
      liftᵂ _ w
}.

(* We can lift PURE to itself *)
#[export] Instance PureSpec_pure : PureSpec pure_wp _ (λ A w, w).
Proof.
  constructor.
  intros A w f. intros post h.
  simpl.
  assert (hpre : val w (λ _, True)).
  { destruct w as [w hw].
    eapply hw. 2: exact h.
    auto.
  }
  exists hpre. destruct (f hpre) as [a ha].
  apply ha. apply h.
Qed.

(* Laws *)

#[export] Instance pure_wp_laws : MonadLaws pure_wp.
Proof.
  constructor.
  - intros A B x w.
    apply sig_ext. reflexivity.
  - intros A w.
    apply sig_ext. reflexivity.
  - intros A B C w wf wg.
    apply sig_ext. reflexivity.
Qed.