(* General construction of a partial DM *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util PURE.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.

(* Monad with a require operator (not checking laws) *)
Record ReqMonad := {
  M :> Type → Type ;
  ret : ∀ A (x : A), M A ;
  bind : ∀ A B (c : M A) (f : A → M B), M B ;
  req : ∀ (p : Prop), M p
}.

Arguments ret _ [_].
Arguments bind _ [_ _].

(* Relevant so should be Order *)
Class Ordered (W : ReqMonad) := {
  wle : ∀ A, W A → W A → Prop ;
  trans : ∀ A, Transitive (@wle A)
}.

Arguments wle {_ _ _}.

Notation "x ≤ᵂ y" := (wle x y) (at level 80).

Class MonoSpec (W : ReqMonad) (Word : Ordered W) := {
  bind_mono :
    ∀ A B (w w' : W A) (wf wf' : A → W B),
      w ≤ᵂ w' →
      (∀ x, wf x ≤ᵂ wf' x) →
      W.(bind) w wf ≤ᵂ W.(bind) w' wf'
}.

Definition observation (M W : ReqMonad) :=
  ∀ A (c : M A), W A.

Class LaxMorphism {M W} (Word : Ordered W) (θ : observation M W) := {
  θ_ret :
    ∀ A (x : A),
      θ _ (M.(ret) x) ≤ᵂ W.(ret) x ;
  θ_bind :
    ∀ A B c f,
      θ _ (M.(@bind) A B c f) ≤ᵂ W.(bind) (θ _ c) (λ x, θ _ (f x)) ;
  θ_req :
    ∀ p, θ _ (M.(req) p) ≤ᵂ W.(req) p
}.

Definition spec_lift_pure (W : ReqMonad) :=
  ∀ A (w : pure_wp A), W A.

Class PureSpec (W : ReqMonad) (Word : Ordered W) (liftᵂ : spec_lift_pure W) := {
  req_lift :
    ∀ A w (f : PURE A w),
      W.(bind) (W.(req) (val w (λ _, True))) (λ h, W.(ret) (val (f h))) ≤ᵂ
      liftᵂ _ w
}.

Section PDM.

  (* Computational monad with assert/req *)

  Context (M : ReqMonad).

  (* Specification monad *)

  Context (W : ReqMonad) (Word : Ordered W) (hmono : MonoSpec W Word).

  Existing Instance trans.

  (* Effect observation *)

  Context (θ : observation M W) (hlax : LaxMorphism Word θ).

  Arguments θ [_].

  (* Partial Dijkstra monad *)

  Definition D A w :=
    { c : M A | θ c ≤ᵂ w }.

  Definition retᴰ [A] (x : A) : D A (W.(ret) x).
  Proof.
    exists (M.(ret) x).
    apply θ_ret.
  Defined.

  Definition bindᴰ [A B w wf] (c : D A w) (f : ∀ x, D B (wf x)) :
    D B (W.(bind) w wf).
  Proof.
    exists (M.(bind) (val c) (λ x, val (f x))).
    etransitivity. 1: apply θ_bind.
    apply bind_mono.
    - destruct c. assumption.
    - intro x. destruct (f x). assumption.
  Qed.

  Definition subcompᴰ [A w w'] (c : D A w) {h : w ≤ᵂ w'} : D A w'.
  Proof.
    exists (val c).
    etransitivity. 2: exact h.
    destruct c. assumption.
  Defined.

  Definition reqᴰ (p : Prop) : D p (W.(req) p).
  Proof.
    exists (M.(req) p).
    apply θ_req.
  Defined.

  (* Lift from PURE *)

  Context (liftᵂ : spec_lift_pure W) (hlift : PureSpec W Word liftᵂ).

  Arguments liftᵂ [_].

  Definition liftᴾ [A w] (f : PURE A w) : D A (liftᵂ w).
  Proof.
    refine (subcompᴰ (bindᴰ (reqᴰ (val w (λ _, True))) (λ h, retᴰ (val (f h))))).
    apply req_lift.
  Defined.

End PDM.