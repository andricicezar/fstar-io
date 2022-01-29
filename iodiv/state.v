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

  (* Computation monad *)

  Definition M A :=
    state → state * A.

  Definition retᴹ [A] (x : A) : M A :=
    λ s₀, (s₀, x).

  Definition bindᴹ [A B] (c : M A) (f : A → M B) : M B :=
    λ s₀, let '(s₁, x) := c s₀ in f x s₁.

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

  (* Effect observation *)

  Definition θ [A] (c : M A) : wp A :=
    λ P s₀, let '(s₁, x) := c s₀ in P s₁ x.

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
    intros A B c f. intros P s₀ h.
    repeat red. repeat red in h.
    destruct (c s₀) as [s₁ x].
    assumption.
  Qed.

  (* Dijkstra monad *)

  Definition DM A w :=
    { c : M A | θ c ≤ᵂ w }.

  (* Definition val [A w] (c : DM A w) : M A :=
    let 'exist _ t p := c in t. *)

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

  (* Partial Dijkstra monad *)

  (* Is it really needed? *)
  Definition pw [A] (P : A → Prop) (w : wp A) : wp (sig P) :=
    λ Q s₀, w (λ s₁ x, ∃ (h : P x), Q s₁ (exist _ x h)) s₀.

  Instance pw_ismono [A] (P : A → Prop) (w : wp A) {mw : Monotonous w} :
    Monotonous (pw P w).
  Proof.
    intros Q R s₀ hQR h.
    red. red in h.
    eapply mw. 2: exact h.
    simpl. intros s₁ x [hP hQ].
    exists hP. apply hQR. assumption.
  Qed.

  Definition lift_pre [A] (pre : Prop) : wp A :=
    λ P s₀, pre.

  (* Not sure about how to treat state *)
  Definition lift_post [A] (post : A → Prop) : wp A :=
    λ P s₀, ∀ x s₁, post x → P s₁ x.

  Definition pure_pre [A] (w : wp A) (P : Prop) :=
    (* ∀ Q s₀, w Q s₀ → P. *)
    lift_pre P ≤ᵂ w.

  (* Unsure about this too  *)
  Definition pure_post [A] (w : wp A) (post : A → Prop) :=
    (* ∀ s₀, w (λ s₁ x, post x) s₀. *)
    w ≤ᵂ lift_post post.

  Record PDM A (w : wp A) := {
    pdm_pre : Prop ;
    pdm_pure_pre : pure_pre w pdm_pre ;
    pdm_fun : ∀ post, pdm_pre → pure_post w post → DM (sig post) (pw post w)
  }.

  Arguments pdm_pre [_ _].
  Arguments pdm_pure_pre [_ _].
  Arguments pdm_fun [_ _].

  Axiom PIR : ∀ (P : Prop) (h1 h2 : P), h1 = h2.

  Definition retᴾ [A] (x : A) : PDM A (retᵂ x).
  Proof.
    exists True.
    - intros P s₀ h. constructor.
    - intros P _ hP.
      simple refine (subcompᴰ (retᴰ _)).
      + exists x. cbv in hP.
        specialize (hP (λ _, P)). simpl in hP.
        apply hP. 1: exact empty_state.
        auto.
      + cbv. intros Q s₀ [h hQ].
        lazymatch goal with
        | |- Q _ (exist _ _ ?hh) => replace hh with h by apply PIR
        end.
        assumption.
  Defined.

  Definition bindᴾ [A B w wf] (c : PDM A w) (f : ∀ x, PDM B (wf x)) :
    Monotonous w →
    (∀ x, Monotonous (wf x)) →
    PDM B (bindᵂ w wf).
  Proof.
    intros mw mwf.
    exists c.(pdm_pre).
    - intros P s₀ h. eapply pdm_pure_pre. exact h.
    - intros P hpre pP.
      simple refine (subcompᴰ (bindᴰ (pdm_fun c (λ x, pdm_pre (f x)) _ _) (λ x, pdm_fun (f (val x)) P _ _))).
      + assumption.
      + intros Q s h. unfold lift_post in h.
        unfold pure_post in pP.
        specialize (pP (λ _, P)). unfold lift_post in pP.
        eapply mw. 2: eapply pP. 2:auto.
        simpl. intros s₁ x hf.
        apply h.
        eapply pdm_pure_pre. exact hf.
      + destruct x as [x hx]. assumption.
      + (* Here the only assumption we have on x is pre (f x) which might
          not be enoug.
          Assuming pure_post is correct, we have to show every value of f x
          verifies a property verified by every value of bind c f.
          Could the post always be the same and be something like
          { x | ∀ P, pure_post w P → P x }
          Maybe this is enough?
          *)
        destruct x as [x hx].
        intros Q s h. unfold lift_post in h.
        unfold pure_post in pP.
        specialize (pP (λ _, P)) as hP. unfold lift_post in hP.
        destruct c as [cpre hcpre c]. simpl in hpre.
        assert (post : A → Prop) by admit.
        pose proof (c post) as c'.
        forward c'.
        { assumption. }
        forward c'.
        { admit. }
        destruct c' as [c' h'].
        (* pose proof (c (λ y, y = x)) as c'.
        forward c' by assumption.
        forward c'.
        { intros s₁.
          eapply mw. 2: eapply pP.
          simpl. intros s₂ y h.
          (* No way it works *)
          give_up.
        }
        destruct c' as [c' h'].
        specialize (pP s₀). red in pP.
        eapply mw in pP as h. 1: eapply h' in h.
        2:{ simpl. intros s₁ y h. exact h. }
        * eapply h' in h.
        * *)
        admit.
      + intros Q s₀ h. red in h. red in h.
        red. red. eapply mw. 2: exact h.
        simpl. intros s₁ x hf. split.
        * eapply pdm_pure_pre. eassumption.
        * assumption.
  Admitted.

End State.