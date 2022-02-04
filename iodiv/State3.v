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

  (* Could equivalently have retᶜ *)
  Definition retᴹ [A] (x : A) : M A :=
    λ s₀, (s₀, x).

  Definition bindᶜ [A B] (c : C A) (f : A → M B) : C B :=
    let '(s₁, x) := c in f x s₁.

  Definition bindᴹ [A B] (c : M A) (f : A → M B) : M B :=
    λ s₀, bindᶜ (c s₀) f.

  Definition getᴹ : M state :=
    λ s, (s, s).

  Definition putᴹ (s : state) : M unit :=
    λ s₀, (s, tt).

  (* Specification monad *)

  Definition preᵂ := Prop.
  Definition postᵂ A := state → A → Prop.

  Definition Wᶜ A := postᵂ A → preᵂ.
  Definition W A := I → Wᶜ A.

  Definition Wᶜle [A] (w₀ w₁ : Wᶜ A) : Prop :=
    ∀ P, w₁ P → w₀ P.

  Notation "x ≤ᶜ y" := (Wᶜle x y) (at level 80).

  Definition Wle [A] (w₀ w₁ : W A) : Prop :=
    ∀ s, w₀ s ≤ᶜ w₁ s.

  Notation "x ≤ᵂ y" := (Wle x y) (at level 80).

  Definition retᵂ [A] (x : A) : W A :=
    λ s₀ P, P s₀ x.

  Definition bindᵂ [A B] (w : W A) (wf : A → W B) : W B :=
    λ s₀ P, w s₀ (λ s₁ x, wf x s₁ P).

  Definition getᵂ : W state :=
    λ s P, P s s.

  Definition putᵂ (s : state) : W unit :=
    λ s₀ P, P s tt.

  Instance trans [A] : Transitive (@Wle A).
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

  Lemma θᶜ_ret :
    ∀ A (x : A) (s : I),
      θᶜ (retᴹ x s) ≤ᶜ retᵂ x s.
  Proof.
    intros A x s. intros P h.
    assumption.
  Qed.

  Lemma θ_ret :
    ∀ A (x : A),
      θ (retᴹ x) ≤ᵂ retᵂ x.
  Proof.
    intros A x. intros s₀.
    apply θᶜ_ret.
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

  Definition retᴾ [A pre] (x : A) : Mᴾ A pre :=
    λ s₀ _, retᴹ x s₀.

  (* Partial effect observation *)

  Definition θᴾ [A pre] (c : Mᴾ A pre) : W A :=
    λ s₀ post, ∀ (h : pre s₀), θᶜ (c s₀ h) post.

  Lemma θᴾ_ret :
    ∀ A (x : A) pre,
      θᴾ (@retᴾ _ pre x) ≤ᵂ retᵂ x.
  Proof.
    intros A x pre.
    intros s P h.
    intro hpre.
    apply θᶜ_ret. assumption.
  Qed.

  (* Refinement on outputs *)

  Definition respects [A] (x : A) (w : Wᶜ A) :=
    ∀ P, w P → ∃ s₁, P s₁ x.

  Notation "x ∈ w" := (respects x w) (at level 50).

  Definition refineᶜ [A] w (c : C A) {h : θᶜ c ≤ᶜ w} :
    C { x : A | x ∈ w }.
  Proof.
    refine (fst c, ⟨ snd c ⟩).
    destruct c as [s x]. simpl.
    intros P hw.
    apply h in hw. simpl in hw.
    exists s. apply hw.
  Defined.

  (* Partial Dijkstra monad *)

  Record D A (w : W A) := makeD {
    Dpre : I → Prop ;
    Dhpre : ∀ s₀ post, w s₀ post → Dpre s₀ ;
    Dfun : Mᴾ A Dpre ;
    Dθ : θᴾ Dfun ≤ᵂ w
  }.

  Arguments Dpre [_ _].
  Arguments Dhpre [_ _].
  Arguments Dfun [_ _].
  Arguments Dθ [_ _].

  Definition retᴰ [A] (x : A) : D A (retᵂ x).
  Proof.
    refine {|
      Dpre := λ _, True ;
      Dfun := retᴾ x
    |}.
    - auto.
    - apply θᴾ_ret.
  Defined.

  Definition bindᴰ [A B w wf] (c : D A w) (f : ∀ x, D B (wf x)) :
    D B (bindᵂ w wf).
  Proof.
    simple refine {|
      Dpre := λ s, c.(Dpre) s ∧ ∀ x, x ∈ w s → ∃ s₁, (f x).(Dpre) s₁ ;
      Dfun := λ s h,
        bindᶜ (refineᶜ (w s) (c.(Dfun) s _)) (λ x s₁, (f (val x)).(Dfun) s₁ _)
    |}.
    - intros s post h. simpl. split.
      + eapply Dhpre. exact h.
      + intros x hx.
        apply hx in h. destruct h as [s₁ h].
        exists s₁. eapply Dhpre. exact h.
    - apply h.
    - simpl. intros P hw.
      eapply Dθ. assumption.
    - destruct x as [x hx]. simpl in h. destruct h as [? h].
      apply h in hx.
      (* The exists s₁ is not enough, should we know exactly which s₁? *)
      admit.
    - admit. (* Printing is hideous *)
  Abort.

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
    refine {|
      Dpre := λ _, val w (λ _, True) ;
      Dfun := λ s₀ hpre, retᴹ (val (f hpre)) s₀
    |}.
    - intros s₀ post h.
      simpl. unfold liftᵂ in h.
      destruct w as [w hw].
      eapply hw. 2: exact h.
      intuition auto.
    - intros s P h.
      unfold liftᵂ in h. unfold θᴾ.
      (* Here h and hpre are redundant, maybe it's not a problem
        but it suggests we could optimise D?
      *)
      intro hpre.
      set (f' := f hpre). clearbody f'. clear f hpre.
      destruct f' as [f hf].
      cbv. apply hf. apply h.
  Defined.

End State.