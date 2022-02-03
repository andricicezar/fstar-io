From Coq Require Import Utf8 RelationClasses.

Set Default Goal Selector "!".
Set Printing Projections.

Ltac forward_gen H tac :=
  match type of H with
  | ?X → _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

Notation val x := (let 'exist _ t _ := x in t).
Notation "⟨ u ⟩" := (exist _ u _).

Section State.

  Context (state : Type) (empty_state : state).

  (* Computation monad with input *)

  Definition I := state.
  Definition C A : Type := state * A.

  Definition M A := I → C A.

  Definition retᴹ [A] (x : A) : M A :=
    λ s₀, (s₀, x).

  Definition bindᴹ [A B] (c : M A) (f : A → M B) : M B :=
    λ s₀, let '(s₁, x) := c s₀ in f x s₁.

  Definition getᴹ : M state :=
    λ s, (s, s).

  Definition putᴹ (s : state) : M unit :=
    λ s₀, (s, tt).

  (* Specification monad *)

  Definition preᵂ := Prop.
  Definition postᵂ A := state → A → Prop.

  Definition Wᶜ A := postᵂ A → preᵂ.
  Definition W A := I → Wᶜ A.

  Definition wle [A] (w₀ w₁ : W A) : Prop :=
    ∀ s P, w₁ s P → w₀ s P.

  Notation "x ≤ᵂ y" := (wle x y) (at level 80).

  Definition retᵂ [A] (x : A) : W A :=
    λ s₀ P, P s₀ x.

  Definition bindᵂ [A B] (w : W A) (wf : A → W B) : W B :=
    λ s₀ P, w s₀ (λ s₁ x, wf x s₁ P).

  Definition getᵂ : W state :=
    λ s P, P s s.

  Definition putᵂ (s : state) : W unit :=
    λ s₀ P, P s tt.

  Instance trans [A] : Transitive (@wle A).
  Proof.
    intros x y z h₁ h₂. intros s₀ P h.
    apply h₁. apply h₂.
    assumption.
  Qed.

  (* Monotonicity *)

  Class Monotonous [A] (w : W A) :=
    ismono : ∀ (P Q : postᵂ A) s₀, (∀ s₁ x, P s₁ x → Q s₁ x) → w s₀ P → w s₀ Q.

  Instance retᵂ_ismono [A] (x : A) : Monotonous (retᵂ x).
  Proof.
    intros P Q s₀ hPQ h.
    apply hPQ. apply h.
  Qed.

  Instance bindᵂ_ismono [A B] (w : W A) (wf : A → W B) :
    Monotonous w →
    (∀ x, Monotonous (wf x)) →
    Monotonous (bindᵂ w wf).
  Proof.
    intros mw mwf.
    intros P Q s₀ hPQ h.
    eapply mw. 2: exact h.
    simpl. intros s₁ x hf.
    eapply mwf. 2: exact hf.
    assumption.
  Qed.

  Instance getᵂ_ismono : Monotonous (getᵂ).
  Proof.
    intros P Q s₀ hPQ h.
    red. red in h.
    apply hPQ. assumption.
  Qed.

  Instance putᵂ_ismono : ∀ s, Monotonous (putᵂ s).
  Proof.
    intros s. intros P Q s₀ hPQ h.
    apply hPQ. assumption.
  Qed.

  Lemma bindᵂ_mono :
    ∀ [A B] (w w' : W A) (wf wf' : A → W B),
      Monotonous w' →
      w ≤ᵂ w' →
      (∀ x, wf x ≤ᵂ wf' x) →
      bindᵂ w wf ≤ᵂ bindᵂ w' wf'.
  Proof.
    intros A B w w' wf wf' mw' hw hwf.
    intros P s₀ h.
    red. red in h.
    apply hw. eapply mw'. 2: exact h.
    simpl. intros s₁ x hf. apply hwf. assumption.
  Qed.

  (* Effect observation *)

  Definition θᶜ [A] (c : C A) : Wᶜ A :=
    λ post, let '(s₁, x) := c in post s₁ x.

  Definition θ [A] (c : M A) : W A :=
    λ s₀, θᶜ (c s₀).

  Lemma θ_ret :
    ∀ A (x : A),
      θ (retᴹ x) ≤ᵂ retᵂ x.
  Proof.
    intros A x. intros s₀ P h.
    cbn. red in h. assumption.
  Qed.

  Lemma θ_bind :
    ∀ A B c f,
      θ (@bindᴹ A B c f) ≤ᵂ bindᵂ (θ c) (λ x, θ (f x)).
  Proof.
    intros A B c f. intros s₀ P h.
    repeat red. repeat red in h.
    destruct (c s₀) as [s₁ x].
    assumption.
  Qed.

  (* Partial computation monad *)

  Definition Mᴾ A (pre : I → Prop) :=
    ∀ (s₀ : I), pre s₀ → C A.

  (* Partial effect observation *)

  Definition θᴾ [A pre] (c : Mᴾ A pre) : W A :=
    λ s₀ post, ∀ (h : pre s₀), θᶜ (c s₀ h) post.

  (* Partial Dijkstra monad *)

  Record D A (w : W A) := {
    Dpre : I → Prop ;
    Dhpre : ∀ s₀ post, w s₀ post → Dpre s₀ ;
    Dfun : Mᴾ A Dpre ;
    Dθ : θᴾ Dfun ≤ᵂ w
  }.

  (* Lift from PURE (somehow) *)

  Definition pure_wp' A := (A → Prop) → Prop.

  Definition pure_mono [A] (w : pure_wp' A) : Prop :=
    ∀ (P Q : A → Prop), (∀ x, P x → Q x) → w P → w Q.

  Definition pure_wp A :=
    { w : pure_wp' A | pure_mono w }.

  Definition PURE A (w : pure_wp A) :=
    val w (λ _, True) → { x : A | ∀ P, val w P → P x }.

  Definition liftᵂ [A] (w : pure_wp A) : W A :=
    λ s₀ P, val w (λ x, P s₀ x).

  Definition liftᴰ [A w] (f : PURE A w) : D A (liftᵂ w).
  Proof.
    unshelve econstructor.
    - exact (λ _, val w (λ _, True)).
    - intros s₀ hpre.
      (* Missing retᶜ and then we would express retᴹ canonically from it *)
      admit.
    - intros s₀ post h.
      simpl. unfold liftᵂ in h.
      destruct w as [w hw].
      eapply hw. 2: exact h.
      intuition auto.
    - admit.
  Abort.

End State.