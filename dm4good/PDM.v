(* General construction of a partial DM *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util PURE.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.

Section PDM.

  (* Computational monad with assert/req *)

  Context (M : Type → Type).
  Context (retᴹ : ∀ A (x : A), M A).
  Context (bindᴹ : ∀ A B (c : M A) (f : A → M B), M B).
  Context (reqᴹ : ∀ (p : Prop), M p).

  Arguments retᴹ [_].
  Arguments bindᴹ [_ _].

  (* Specification monad *)

  Context (W : Type → Type).
  Context (wle : ∀ [A], W A → W A → Prop).

  Arguments wle [_].

  Notation "x ≤ᵂ y" := (wle x y) (at level 80).

  Context (trans : ∀ A, Transitive (@wle A)).

  Context (retᵂ : ∀ A (x : A), W A).
  Context (bindᵂ : ∀ A B (w : W A) (wf : A → W B), W B).
  Context (reqᵂ : ∀ (p : Prop), W p).

  Arguments retᵂ [_].
  Arguments bindᵂ [_ _].

  (* Monotonicity *)

  Context (
    bindᵂ_mono :
      ∀ A B (w w' : W A) (wf wf' : A → W B),
        w ≤ᵂ w' →
        (∀ x, wf x ≤ᵂ wf' x) →
        bindᵂ w wf ≤ᵂ bindᵂ w' wf'
  ).

  (* Effect observation *)

  Context (θ : ∀ A (c : M A), W A).

  Arguments θ [_].

  Context (
    θ_ret :
      ∀ A (x : A),
        θ (retᴹ x) ≤ᵂ retᵂ x
  ).

  Context (
    θ_bind :
      ∀ A B c f,
        θ (@bindᴹ A B c f) ≤ᵂ bindᵂ (θ c) (λ x, θ (f x))
  ).

  Context (
    θ_req :
      ∀ p, θ (reqᴹ p) ≤ᵂ reqᵂ p
  ).

  (* Partial Dijkstra monad *)

  Definition D A w :=
    { c : M A | θ c ≤ᵂ w }.

  Definition retᴰ [A] (x : A) : D A (retᵂ x).
  Proof.
    exists (retᴹ x).
    apply θ_ret.
  Defined.

  Definition bindᴰ [A B w wf] (c : D A w) (f : ∀ x, D B (wf x)) :
    D B (bindᵂ w wf).
  Proof.
    exists (bindᴹ (val c) (λ x, val (f x))).
    etransitivity. 1: apply θ_bind.
    apply bindᵂ_mono.
    - destruct c. assumption.
    - intro x. destruct (f x). assumption.
  Qed.

  Definition subcompᴰ [A w w'] (c : D A w) {h : w ≤ᵂ w'} : D A w'.
  Proof.
    exists (val c).
    etransitivity. 2: exact h.
    destruct c. assumption.
  Defined.

  Definition reqᴰ (p : Prop) : D p (reqᵂ p).
  Proof.
    exists (reqᴹ p).
    apply θ_req.
  Defined.

  (* Lift from PURE *)

  Context (liftᵂ : ∀ A (w : pure_wp A), W A).

  Arguments liftᵂ [_].

  Context (
    req_lift :
      ∀ A w (f : PURE A w),
        bindᵂ (reqᵂ (val w (λ _, True))) (λ h, retᵂ (val (f h))) ≤ᵂ liftᵂ w
  ).

  Definition liftᴾ [A w] (f : PURE A w) : D A (liftᵂ w).
  Proof.
    refine (subcompᴰ (bindᴰ (reqᴰ (val w (λ _, True))) (λ h, retᴰ (val (f h))))).
    apply req_lift.
  Defined.

End PDM.