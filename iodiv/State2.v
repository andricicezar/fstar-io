From Coq Require Import Utf8 RelationClasses.

Set Default Goal Selector "!".
Set Printing Projections.

Ltac forward_gen H tac :=
  match type of H with
  | ?X → _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

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

  Definition W A := I → postᵂ A → preᵂ.

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

  Definition θ [A] (c : M A) : W A :=
    λ s₀ P, let '(s₁, x) := c s₀ in P s₁ x.

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

  (* Partial Dijkstra monad *)

  (* Record D'' A (w : W A) (s : I) := {
    d_pre : Prop ;
    d_hpre : ∀ P, w s P → d_pre ;
    d_body : d_pre → C A
  }.

  Definition D' A (w : W A) :=
    ∀ (s : I), D'' A w s. *)

  (* Getting a function in M A for a specific s doesn't really make sense. *)
  (* Definition D A w :=
    { f : D' A w | ∀ (s : I) P (h : w s P), θ _ s P }. *)

  (* In DM for free we would get something like this: *)
  Definition D A (w : W A) :=
    ∀ (s : I),
      w s (λ _ _, True) → (* We could also choose the pre *)
      { '(s', y) : state * A | ∀ P, w s P → P s' y }.

  Definition retᴰ [A] (x : A) : D A (retᵂ x).
  Proof.
    intros s h.
    exists (retᴹ x s).
    (* Also works using θ_ret *)
    (* apply θ_ret. unfold retᵂ. auto. *)
    simpl. auto.
  Defined.

  Definition bindᴰ [A B w wf] (c : D A w) (f : ∀ x, D B (wf x)) :
    D B (bindᵂ w wf).
  Proof.
    intros s₀ h.
    (* Is it even possible to reuse bindᴹ? *)
  Abort.

End State.