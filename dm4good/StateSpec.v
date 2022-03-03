(* Specification monad for state *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util structures guarded PURE PDM.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Section State.

  Context {state : Type}.

  Definition preᵂ := state → Prop.
  Definition postᵂ A := state → A → Prop.

  Definition W' A := postᵂ A → preᵂ.

  Class Monotonous [A] (w : W' A) :=
    ismono : ∀ (P Q : postᵂ A) s₀, (∀ s₁ x, P s₁ x → Q s₁ x) → w P s₀ → w Q s₀.

  Definition W A := { w : W' A | Monotonous w }.

  Definition as_wp [A] (w : W' A) `{h : Monotonous _ w} : W A :=
    exist _ w h.

  Definition retᵂ' [A] (x : A) : W' A :=
    λ P s₀, P s₀ x.

  Instance retᵂ_ismono [A] (x : A) : Monotonous (retᵂ' x).
  Proof.
    intros P Q s₀ hPQ h.
    apply hPQ. apply h.
  Qed.

  Definition retᵂ [A] (x : A) : W A :=
    as_wp (retᵂ' x).

  Definition bindᵂ' [A B] (w : W A) (wf : A → W B) : W' B :=
    λ P, val w (λ s₁ x, val (wf x) P s₁).

  Instance bindᵂ_ismono [A B] (w : W A) (wf : A → W B) :
    Monotonous (bindᵂ' w wf).
  Proof.
    destruct w as [w mw].
    intros P Q s₀ hPQ h.
    eapply mw. 2: exact h.
    simpl. intros s₁ x hf.
    destruct (wf x) as [wf' mwf].
    eapply mwf. 2: exact hf.
    assumption.
  Qed.

  Definition bindᵂ [A B] (w : W A) (wf : A → W B) : W B :=
    as_wp (bindᵂ' w wf).

  Definition reqᵂ' (p : Prop) : W' p :=
    λ P s₀, ∃ (h : p), P s₀ h.

  Instance reqᵂ_ismono : ∀ p, Monotonous (reqᵂ' p).
  Proof.
    intros p. intros P Q s₀ hPQ h.
    destruct h as [hp h].
    exists hp. apply hPQ. assumption.
  Qed.

  Definition reqᵂ (p : Prop) : W p :=
    as_wp (reqᵂ' p).

  Definition getᵂ' : W' state :=
    λ P s, P s s.

  Instance getᵂ_ismono : Monotonous getᵂ'.
  Proof.
    intros P Q s₀ hPQ h.
    red. red in h.
    apply hPQ. assumption.
  Qed.

  Definition getᵂ : W state :=
    as_wp getᵂ'.

  Definition putᵂ' (s : state) : W' unit :=
    λ P s₀, P s tt.

  Instance putᵂ_ismono : ∀ s, Monotonous (putᵂ' s).
  Proof.
    intros s. intros P Q s₀ hPQ h.
    apply hPQ. assumption.
  Qed.

  Definition putᵂ (s : state) : W unit :=
    as_wp (putᵂ' s).

  Instance Monad_W : Monad W := {|
    ret := retᵂ ;
    bind := bindᵂ
  |}.

  Instance ReqMonad_W : ReqMonad W := {|
    req := reqᵂ
  |}.

  Definition wle [A] (w₀ w₁ : W A) : Prop :=
    ∀ P s, val w₁ P s → val w₀ P s.

  Instance WStOrder : Order W.
  Proof.
    exists wle.
    intros A x y z h₁ h₂. intros P s₀ h.
    apply h₁. apply h₂.
    assumption.
  Defined.

  #[export] Instance pure_wp_refl [A] : Reflexive (wle (A := A)).
  Proof.
    intro w. intros p s₀ h. assumption.
  Qed.

  Instance WStMono : MonoSpec W.
  Proof.
    constructor.
    intros A B w w' wf wf' hw hwf.
    intros P s₀ h.
    do 3 red. do 3 red in h.
    apply hw. destruct w' as [w' mw']. eapply mw'. 2: exact h.
    simpl. intros s₁ x hf. apply hwf. assumption.
  Qed.

  Definition liftᵂ [A] (w : pure_wp A) : W A.
  Proof.
    exists (λ P s₀, val w (λ x, P s₀ x)).
    intros P Q s₀ hPQ h.
    destruct w as [w mw].
    eapply mw. 2: exact h.
    apply hPQ.
  Defined.

  Instance hlift : PureSpec W WStOrder liftᵂ.
  Proof.
    constructor.
    intros A w f.
    intros P s h.
    assert (hpre : val w (λ _, True)).
    { unfold liftᵂ in h.
      destruct w as [w hw].
      eapply hw. 2: exact h.
      auto.
    }
    cbv. exists hpre.
    pose proof (prf (f hpre)) as hf. simpl in hf.
    apply hf in h. assumption.
  Qed.

  (* Laws *)

  #[export] Instance WSt_laws : MonadLaws W.
  Proof.
    constructor.
    - intros A B x w.
      apply sig_ext. reflexivity.
    - intros A w.
      apply sig_ext. reflexivity.
    - intros A B C w wf wg.
      apply sig_ext. reflexivity.
  Qed.

End State.