(* General construction of a partial DM *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util PURE.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(* Monad with a require operator (not checking laws) *)
Record ReqMonad := {
  M :> Type → Type ;
  ret : ∀ A (x : A), M A ;
  bind : ∀ A B (c : M A) (f : A → M B), M B ;
  req : ∀ (p : Prop), M p
}.

Arguments ret _ [_].
Arguments bind _ [_ _].

Class Order (W : ReqMonad) := {
  wle : ∀ A, W A → W A → Prop ;
  trans : ∀ A, Transitive (@wle A)
}.

Arguments wle {_ _ _}.

Notation "x ≤ᵂ y" := (wle x y) (at level 80).

Class MonoSpec (W : ReqMonad) (Word : Order W) := {
  bind_mono :
    ∀ A B (w w' : W A) (wf wf' : A → W B),
      w ≤ᵂ w' →
      (∀ x, wf x ≤ᵂ wf' x) →
      W.(bind) w wf ≤ᵂ W.(bind) w' wf'
}.

Definition observation (M W : ReqMonad) :=
  ∀ A (c : M A), W A.

Class LaxMorphism {M W} (Word : Order W) (θ : observation M W) := {
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

Class PureSpec (W : ReqMonad) (Word : Order W) (liftᵂ : spec_lift_pure W) := {
  req_lift :
    ∀ A w (f : PURE A w),
      W.(bind) (W.(req) (val w (λ _, True))) (λ h, W.(ret) (val (f h))) ≤ᵂ
      liftᵂ _ w
}.

Record DijkstraMonad {W} (WOrd : Order W) := {
  DM :> ∀ A (w : W A), Type ;
  retᴰ : ∀ A (x : A), DM A (W.(ret) x) ;
  bindᴰ : ∀ A B w wf (c : DM A w) (f : ∀ x, DM B (wf x)), DM B (W.(bind) w wf) ;
  subcompᴰ : ∀ A w w' (c : DM A w) (h : w ≤ᵂ w'), DM A w'
}.

Arguments retᴰ {_ _} _ [_].
Arguments bindᴰ {_ _} _ [_ _ _ _].
Arguments subcompᴰ {_ _} _ [_ _ _] _ {_}.

Section PDM.

  (* Computational monad with assert/req *)

  Context {M : ReqMonad}.

  (* Specification monad *)

  Context {W : ReqMonad} {Word : Order W} (hmono : MonoSpec W Word).

  Existing Instance trans.

  (* Effect observation *)

  Context {θ : observation M W} (hlax : LaxMorphism Word θ).

  Arguments θ [_].

  (* Partial Dijkstra monad *)

  Definition D : DijkstraMonad Word.
  Proof.
    simple refine {|
      DM A w := { c : M A | θ c ≤ᵂ w }
    |}.
    - intros A x.
      exists (M.(ret) x).
      apply θ_ret.
    - intros A B w wf c f.
      exists (M.(bind) (val c) (λ x, val (f x))).
      etransitivity. 1: apply θ_bind.
      apply bind_mono.
      + destruct c. assumption.
      + intro x. destruct (f x). assumption.
    - intros A w w' c h.
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

  (* Would be nice to have a special case when W comes from pre and post + mono *)
  Context {liftᵂ : spec_lift_pure W} (hlift : PureSpec W Word liftᵂ).

  Arguments liftᵂ [_].

  Definition liftᴾ [A w] (f : PURE A w) : D A (liftᵂ w).
  Proof.
    refine (D.(subcompᴰ) (D.(bindᴰ) (reqᴰ (val w (λ _, True))) (λ h, D.(retᴰ) (val (f h))))).
    apply req_lift.
  Defined.

End PDM.