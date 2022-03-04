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
    - intros M hM lM A x.
      simpl. extensionality s₀.
      rewrite structures.left_id. reflexivity.
    - intros M hM lM A B c f.
      simpl. extensionality s₀.
      rewrite !structures.assoc. f_equal.
      extensionality x. rewrite structures.left_id. reflexivity.
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
  Defined.

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
    simpl. apply hw.
    simpl in h.
    destruct w' as [w'' hm].
    eapply hm. 2: exact h.
    intros [s₁ x]. apply hwf.
  Qed.

  Lemma wle_liftᵀ :
    ∀ A (w w' : pure_wp A), w ≤ᵂ w' → liftᵀ w ≤ᵂ liftᵀ w'.
  Proof.
    intros A w w' hw.
    simpl. intros post s h.
    apply hw. assumption.
  Qed.

  Instance Reflexive_wle : ∀ A, Reflexive (wle (W := W StT) (A := A)).
  Proof.
    intros A x. intros post s. auto.
  Qed.

  Definition D A w : Type :=
    DM4Free.D StT Order_W A w.

  Instance DijkstraMonad_D : DijkstraMonad (Word := Order_W) D := _.

  Definition liftᴾ [A w] (f : PURE A w) : D A (liftᵂ StT _ w) :=
    DM4Free.liftᴾ StT _ _ wle_liftᵀ _ w f.

End State.