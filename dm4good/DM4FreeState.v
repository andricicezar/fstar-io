(* Using the construction to derive state *)

From Coq Require Import Utf8 RelationClasses FunctionalExtensionality.
From PDM Require Import util structures guarded PURE PDM DM4Free.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Section State.

  Context (state : Type).

  Definition StT (M : Type → Type) (A : Type) :=
    state → M (state * A)%type.

  Instance MonadTransformer_StT : MonadTransformer StT := {|
    liftᵀ M hM A c := λ s₀, bind c (λ x, ret (s₀, x)) ;
    mapᵀ M N f hM hN hf A c := λ s₀, f _ (c s₀)
  |}.

  Instance MonadTransformerLaws_StT : MonadTransformerLaws StT.
  Proof.
    unshelve econstructor.
    - intros M hM.
      refine {|
        ret A x := λ s₀, ret (s₀, x) ;
        bind A B c f := λ s₀, bind (c s₀) (λ '(s₁, x), f x s₁)
      |}.
    - intros M hM A x.
      simpl. extensionality s₀.
      (* Missing monadic laws *)
      admit.
    - intros M hM A B c f.
      simpl. extensionality s₀.
      admit.
    - intros M N f hM hN hf.
      constructor.
      + intros A x. simpl.
        extensionality s₀.
        apply morph_ret.
      + intros A B c k.
        simpl. extensionality s₀.
        rewrite morph_bind. apply (f_equal (bind _)).
        apply functional_extensionality. intros [s₁ x].
        reflexivity.
    - intros M N f hM hN hf A c.
      simpl. extensionality s₀.
      rewrite morph_bind. apply (f_equal (bind _)).
      extensionality x. apply morph_ret.
  Admitted.

  #[refine] Instance Order_W : Order (W StT) := {|
    wle A (w w' : W StT A) := ∀ post s, val (w' s) post → val (w s) post
  |}.
  Proof.
    intros A x y z h1 h2.
    intros post s h.
    apply h1. apply h2. assumption.
  Defined.

  Instance MonoSpec_W : MonoSpec (W StT).
  Proof.
    constructor.
    intros A B w w' wf wf' hw hwf.
    intros post s h.
    simpl.
    (* Need the laws to compute because it builds a monad! *)
  Abort.

End State.