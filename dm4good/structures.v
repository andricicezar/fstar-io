(* Encoding of PURE *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(* Monad structure (no laws) *)
Class Monad (M : Type → Type) := {
  ret : ∀ A (x : A), M A ;
  bind : ∀ A B (c : M A) (f : A → M B), M B
}.

(* Monad with a require operator *)
Class ReqMonad M `{Monad M} := {
  req : ∀ (p : Prop), M p
}.

Arguments ret {_ _} [_].
Arguments bind {_ _} [_ _].

Class Order W `{Monad W} := {
  wle : ∀ A, W A → W A → Prop ;
  trans :> ∀ A, Transitive (@wle A)
}.

Arguments wle {_ _ _} {_}.

Notation "x ≤ᵂ y" := (wle x y) (at level 80).

Class MonoSpec W `{Order W} := {
  bind_mono :
    ∀ A B (w w' : W A) (wf wf' : A → W B),
      w ≤ᵂ w' →
      (∀ x, wf x ≤ᵂ wf' x) →
      bind w wf ≤ᵂ bind w' wf'
}.

Definition observation (M W : Type → Type) :=
  ∀ A (c : M A), W A.

Class LaxMorphism {M W} `{Monad M} `{Order W} (θ : observation M W) := {
  θ_ret :
    ∀ A (x : A),
      θ _ (ret x) ≤ᵂ ret x ;
  θ_bind :
    ∀ A B c f,
      θ _ (bind (A:=A) (B:=B) c f) ≤ᵂ bind (θ _ c) (λ x, θ _ (f x))
}.

Class ReqLaxMorphism
  {M W} `{ReqMonad M} `{ReqMonad W} (Word : Order W)
  (θ : observation M W) {θ_lax : LaxMorphism θ} := {
  θ_req : ∀ p, θ _ (req p) ≤ᵂ req p
}.

Class DijkstraMonad {W} `{Word : Order W} (D : ∀ A (w : W A), Type) := {
  retᴰ : ∀ A (x : A), D A (ret x) ;
  bindᴰ : ∀ A B w wf (c : D A w) (f : ∀ x, D B (wf x)), D B (bind w wf) ;
  subcompᴰ : ∀ A w w' (c : D A w) (h : w ≤ᵂ w'), D A w'
}.

Arguments retᴰ {_ _ _ _ _} [_].
Arguments bindᴰ {_ _ _ _ _} [_ _ _ _].
Arguments subcompᴰ {_ _ _ _ _} [_ _ _] _ {_}.

(* Laws *)

Class MonadLaws M `{Monad M} := {
  left_id : ∀ A B (x : A) (f : A → M B), bind (ret x) f = f x ;
  right_id : ∀ A (c : M A), bind c (λ x, ret x) = c ;
  assoc :
    ∀ A B C (c : M A) (f : A → M B) (g : B → M C),
      bind (bind c f) g = bind c (λ x, bind (f x) g)
}.

(* Monad morphism *)

Class Morphism M N {hM : Monad M} {hN : Monad N} (f : ∀ A, M A → N A) := {
  morph_ret : ∀ A (x : A), f A (ret x) = ret x ;
  morph_bind :
    ∀ A B (c : M A) (k : A → M B),
      f _ (bind c k) = bind (f _ c) (λ x, f _ (k x))
}.

(* Monad transformers *)

Class MonadTransformer T := {
  liftᵀ : ∀ M {hM : Monad M} (A : Type), M A → T M A ;
  mapᵀ : ∀ M N f `{Morphism M N f} (A : Type), T M A → T N A
}.

Arguments liftᵀ {_ _} [_ _ _].
Arguments mapᵀ {_ _} [_ _] _ {_ _ _} [_].

Class MonadTransformerLaws T `{MonadTransformer T} := {
  transf_monad :> ∀ M `{Monad M}, Monad (T M) ;
  liftᵀ_ret : ∀ M `{MonadLaws M} A (x : A), liftᵀ (ret x) = ret x ;
  liftᵀ_bind :
    ∀ M `{MonadLaws M} A B (c : M A) (f : A → M B),
      liftᵀ (bind c f) = bind (liftᵀ c) (λ x, liftᵀ (f x)) ;
  mapᵀ_morph : ∀ M N f `{Morphism M N f}, Morphism _ _ (mapᵀ f) ;
  mapᵀ_liftᵀ :
    ∀ M N f `{Morphism M N f} A (c : M A),
      mapᵀ f (liftᵀ c) = liftᵀ (f _ c)
}.