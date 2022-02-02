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

  Context (state : Type).

  (* Computation monad *)

  Inductive M A :=
  | retᴹ (x : A)
  | act_getᴹ (k : state → M A)
  | act_putᴹ (s : state) (k : M A).

  Arguments retᴹ [_].
  Arguments act_getᴹ [_].
  Arguments act_putᴹ [_].

  Fixpoint bindᴹ [A B] (c : M A) (f : A → M B) : M B :=
    match c with
    | retᴹ x => f x
    | act_getᴹ k => act_getᴹ (λ s, bindᴹ (k s) f)
    | act_putᴹ s k => act_putᴹ s (bindᴹ k f)
    end.

  Definition getᴹ : M state :=
    act_getᴹ (λ x, retᴹ x).

  Definition putᴹ (s : state) : M unit :=
    act_putᴹ s (retᴹ tt).

  (* Specification monad *)

  Definition preᵂ := state → Prop.
  Definition postᵂ A := state → A → Prop.

  Definition wp A := postᵂ A → preᵂ.

  Definition wle [A] (w₀ w₁ : wp A) : Prop :=
    ∀ P s, w₁ P s → w₀ P s.

  Notation "x ≤ᵂ y" := (wle x y) (at level 80).

  Definition retᵂ [A] (x : A) : wp A :=
    λ P s₀, P s₀ x.

  Definition bindᵂ [A B] (w : wp A) (wf : A → wp B) : wp B :=
    λ P, w (λ s₁ x, wf x P s₁).

  Definition getᵂ : wp state :=
    λ P s, P s s.

  Definition putᵂ (s : state) : wp unit :=
    λ P s₀, P s tt.

  Instance trans [A] : Transitive (@wle A).
  Proof.
    intros x y z h₁ h₂. intros P s₀ h.
    apply h₁. apply h₂.
    assumption.
  Qed.

  (* Monotonicity *)

  Class Monotonous [A] (w : wp A) :=
    ismono : ∀ (P Q : postᵂ A) s₀, (∀ s₁ x, P s₁ x → Q s₁ x) → w P s₀ → w Q s₀.

  Instance retᵂ_ismono [A] (x : A) : Monotonous (retᵂ x).
  Proof.
    intros P Q s₀ hPQ h.
    apply hPQ. apply h.
  Qed.

  Instance bindᵂ_ismono [A B] (w : wp A) (wf : A → wp B) :
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
    ∀ [A B] (w w' : wp A) (wf wf' : A → wp B),
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

  (* Effect observation (in two passes) *)

  Fixpoint θ₀ [A] (c : M A) (s₀ : state) : state * A :=
    match c with
    | retᴹ x => (s₀, x)
    | act_getᴹ k => θ₀ (k s₀) s₀
    | act_putᴹ s k => θ₀ k s
    end.

  Definition θ [A] (c : M A) : wp A :=
    λ P s₀, let '(s₁, x) := θ₀ c s₀ in P s₁ x.

  Lemma θ_ret :
    ∀ A (x : A),
      θ (retᴹ x) ≤ᵂ retᵂ x.
  Proof.
    intros A x. intros P s₀ h.
    cbn. red in h. assumption.
  Qed.

  Lemma θ_bind :
    ∀ A B c f,
      θ (@bindᴹ A B c f) ≤ᵂ bindᵂ (θ c) (λ x, θ (f x)).
  Proof.
    intros A B c f.
    induction c as [| ? ih | ?? ih] in B, f |- *.
    - cbn. intros P s₀ h.
      assumption.
    - cbn. intros P s₀ h.
      apply ih. assumption.
    - cbn. intros P s₀ h.
      apply ih. assumption.
  Qed.

  (* Dijkstra monad *)

  Definition DM A w :=
    { c : M A | θ c ≤ᵂ w }.

  Notation val x := (let 'exist _ t _ := x in t).

  Definition retᴰ [A] (x : A) : DM A (retᵂ x).
  Proof.
    exists (retᴹ x).
    apply θ_ret.
  Defined.

  Definition bindᴰ [A B w wf] (c : DM A w) (f : ∀ x, DM B (wf x))
    `{Monotonous _ w} :
    DM B (bindᵂ w wf).
  Proof.
    exists (bindᴹ (val c) (λ x, val (f x))).
    etransitivity. 1: apply θ_bind.
    apply bindᵂ_mono.
    - assumption.
    - destruct c. simpl. assumption.
    - intro x. destruct (f x). simpl. assumption.
  Qed.

  Definition subcompᴰ [A w w'] (c : DM A w) {h : w ≤ᵂ w'} : DM A w'.
  Proof.
    exists (val c).
    etransitivity. 2: exact h.
    destruct c. assumption.
  Defined.

  Definition getᴰ : DM state getᵂ.
  Proof.
    exists getᴹ.
    cbv. auto.
  Defined.

  Definition putᴰ s : DM unit (putᵂ s).
  Proof.
    exists (putᴹ s).
    cbv. auto.
  Defined.

  (* Partial Dijkstra monad *)

  Definition lift_pre [A] (pre : Prop) : wp A :=
    λ P s₀, pre.

  Definition pure_pre [A] (w : wp A) (P : Prop) :=
    (* ∀ Q s₀, w Q s₀ → P. *)
    lift_pre P ≤ᵂ w.

  Notation "⟨ u ⟩" := (exist _ u _).

  Definition refineᵂ [A] (P : A → Prop) (w : wp A) : wp (sig P) :=
    λ Q s₀, w (λ s₁ x, ∀ (h : P x), Q s₁ (exist _ x h)) s₀.

  Instance refineᵂ_ismono [A] (P : A → Prop) (w : wp A) {mw : Monotonous w} :
    Monotonous (refineᵂ P w).
  Proof.
    intros Q R s₀ hQR h.
    red. red in h.
    eapply mw. 2: exact h.
    simpl. intros s₁ x hQ hP.
    apply hQR. apply hQ.
  Qed.

  Axiom PIR : ∀ (P : Prop) (h1 h2 : P), h1 = h2.

  Definition respects [A] (x : A) (w : wp A) :=
    ∀ s₀, ∃ s₁, ∀ P, w P s₀ → P s₁ x.

  Notation "x ∈ w" := (respects x w) (at level 50).

  Definition refᴰ [A w] (c : DM A w) : DM { x : A | x ∈ w } (refineᵂ _ w).
  Proof.
    destruct c as [c hc].
    unshelve eexists.
    - induction c as [x | k ih | ?] in w, hc |- *.
      + apply retᴹ. exists x.
        intros s₀. exists s₀.
        intros P h. apply hc. assumption.
      + apply act_getᴹ. intros s₀. apply (ih s₀).
        intros P s h.
        unfold θ in hc. unfold "≤ᵂ" in hc.
        cbn in hc. unfold θ.
        (* Once again, a problem with state *)
        give_up.
  Abort.

End State.