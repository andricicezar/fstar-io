(* Encoding of PURE *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(* Monad structure (no laws) *)
Record Monad := {
  Mo :> Type → Type ;
  ret : ∀ A (x : A), Mo A ;
  bind : ∀ A B (c : Mo A) (f : A → Mo B), Mo B
}.

(* Monad with a require operator *)
Record ReqMonad := {
  Mq :> Monad ;
  req : ∀ (p : Prop), Mq p
}.

Arguments ret _ [_].
Arguments bind _ [_ _].

Class Order (W : Monad) := {
  wle : ∀ A, W A → W A → Prop ;
  trans : ∀ A, Transitive (@wle A)
}.

Arguments wle {_ _ _}.

Notation "x ≤ᵂ y" := (wle x y) (at level 80).

Class MonoSpec (W : Monad) (Word : Order W) := {
  bind_mono :
    ∀ A B (w w' : W A) (wf wf' : A → W B),
      w ≤ᵂ w' →
      (∀ x, wf x ≤ᵂ wf' x) →
      W.(bind) w wf ≤ᵂ W.(bind) w' wf'
}.

Definition observation (M W : Monad) :=
  ∀ A (c : M A), W A.

Class LaxMorphism {M W} (Word : Order W) (θ : observation M W) := {
  θ_ret :
    ∀ A (x : A),
      θ _ (M.(ret) x) ≤ᵂ W.(ret) x ;
  θ_bind :
    ∀ A B c f,
      θ _ (M.(@bind) A B c f) ≤ᵂ W.(bind) (θ _ c) (λ x, θ _ (f x))
}.

Class ReqLaxMorphism {M W : ReqMonad} (Word : Order W) (θ : observation M W) := {
  θ_lax :> LaxMorphism Word θ ;
  θ_req :
    ∀ p, θ _ (M.(req) p) ≤ᵂ W.(req) p
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