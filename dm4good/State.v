(* Using the construction to derive state

  We do it both in the case of the usual representation, and in the case of a
  free monad. We have to adapt both to support partiality.
*)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util guarded PDM.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.

Section State.

  Context (state : Type).

  (* Specification monad *)

  Definition preᵂ := state → Prop.
  Definition postᵂ A := state → A → Prop.

  Definition W' A := postᵂ A → preᵂ.

  Class Monotonous [A] (w : W' A) :=
    ismono : ∀ (P Q : postᵂ A) s₀, (∀ s₁ x, P s₁ x → Q s₁ x) → w P s₀ → w Q s₀.

  Definition W A := { w : W' A | Monotonous w }.

  Definition as_wp [A] (w : W' A) `{h : Monotonous _ w} : W A :=
    exist _ w h.

  Definition wle [A] (w₀ w₁ : W A) : Prop :=
    ∀ P s, val w₁ P s → val w₀ P s.

  Notation "x ≤ᵂ y" := (wle x y) (at level 80).

  Instance trans [A] : Transitive (@wle A).
  Proof.
    intros x y z h₁ h₂. intros P s₀ h.
    apply h₁. apply h₂.
    assumption.
  Qed.

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

  Lemma bindᵂ_mono :
    ∀ [A B] (w w' : W A) (wf wf' : A → W B),
      w ≤ᵂ w' →
      (∀ x, wf x ≤ᵂ wf' x) →
      bindᵂ w wf ≤ᵂ bindᵂ w' wf'.
  Proof.
    intros A B w w' wf wf' hw hwf.
    intros P s₀ h.
    do 3 red. do 3 red in h.
    apply hw. destruct w' as [w' mw']. eapply mw'. 2: exact h.
    simpl. intros s₁ x hf. apply hwf. assumption.
  Qed.

  (* State transformer version *)
  Section Passing.

    (* Computation monad *)

    Definition M : ReqMonad := {|
      M A := state → G (state * A) ;
      ret A x := λ s₀, retᴳ (s₀, x) ;
      bind A B c f := λ s₀, bindᴳ (c s₀) (λ '(s₁, x), f x s₁) ;
      req p := λ s₀, reqᴳ p (λ h, (s₀, h))
    |}.

    Definition getᴹ : M state :=
      λ s, retᴳ (s, s).

    Definition putᴹ (s : state) : M unit :=
      λ s₀, retᴳ (s, tt).

    (* Effect observation *)

    Definition θ' [A] (c : M A) : W' A :=
      λ post s₀,
        let '(p ; f) := c s₀ in
        ∃ (h : p), let '(s₁, x) := f h in post s₁ x.

    Instance θ_ismono : ∀ A (c : M A), Monotonous (θ' c).
    Proof.
      intros A c. intros P Q s₀ hPQ h.
      red. red in h. destruct (c s₀) as [p f].
      destruct h as [hp h]. exists hp.
      destruct (f hp) as [s₁ x]. apply hPQ. assumption.
    Qed.

    Definition θ [A] (c : M A) : W A :=
      as_wp (θ' c).

    Lemma θ_ret :
      ∀ A (x : A),
        θ (retᴹ x) ≤ᵂ retᵂ x.
    Proof.
      intros A x. intros post s₀ h.
      cbn. exists I. red in h. assumption.
    Qed.

    Lemma θ_bind :
      ∀ A B c f,
        θ (@bindᴹ A B c f) ≤ᵂ bindᵂ (θ c) (λ x, θ (f x)).
    Proof.
      intros A B c f. intros post s₀ h.
      do 4 red. do 6 red in h.
      destruct (c s₀) as [p c']. clear c.
      destruct h as [hp h].
      simpl.
      unshelve eexists.
      { exists hp. destruct (c' hp) as [s₁ x]. do 3 red in h. destruct (f x s₁).
        simpl. destruct h. assumption.
      }
      simpl. destruct (c' hp) as [s₁ x]. do 3 red in h. destruct (f x s₁).
      simpl. destruct h. assumption.
    Qed.

  (* Partial Dijkstra monad *)

  (* Should package things up using records *)
  Definition D A w : Type :=
    PDM.D A w.

  Definition retᴰ [A] (x : A) : D A (retᵂ x).
  Proof.
    exists (retᴹ x).
    apply θ_ret.
  Defined.

  Definition bindᴰ [A B w wf] (c : D A w) (f : ∀ x, D B (wf x))
    `{Monotonous _ w} :
    D B (bindᵂ w wf).
  Proof.
    exists (bindᴹ (val c) (λ x, val (f x))).
    etransitivity. 1: apply θ_bind.
    apply bindᵂ_mono.
    - assumption.
    - destruct c. assumption.
    - intro x. destruct (f x). assumption.
  Qed.

  Definition subcompᴰ [A w w'] (c : D A w) {h : w ≤ᵂ w'} : D A w'.
  Proof.
    exists (val c).
    etransitivity. 2: exact h.
    destruct c. assumption.
  Defined.

  Definition getᴰ : D state getᵂ.
  Proof.
    exists getᴹ.
    cbv. intros post s h. exists I. assumption.
  Defined.

  Definition putᴰ s : D unit (putᵂ s).
  Proof.
    exists (putᴹ s).
    cbv. intros post s₀ h. exists I. assumption.
  Defined.

  Definition reqᴰ (p : Prop) : D p (reqᵂ p).
  Proof.
    exists (reqᴹ p).
    cbv. auto.
  Defined.

  (* Lift from PURE *)

  Definition liftᵂ [A] (w : pure_wp A) : W A :=
    λ P s₀, val w (λ x, P s₀ x).

  Definition liftᴾ [A w] (f : PURE A w) : D A (liftᵂ w).
  Proof.
    refine (subcompᴰ (bindᴰ (reqᴰ (val w (λ _, True))) (λ h, retᴰ (val (f h))))).
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
  Defined.

End State.