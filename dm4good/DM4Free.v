(* Dijkstra monad for free construction *)

From Coq Require Import Utf8 RelationClasses FunctionalExtensionality
  PropExtensionality.
From PDM Require Import util structures guarded PURE PDM.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Section DM4Free.

  Context T `{hT : MonadTransformerLaws T}.

  (* Syntactic monad *)

  Definition M A :=
    T G A.

  #[export] Instance Monad_M : Monad M.
  Proof.
    unfold M. apply transf_monad. exact _.
  Defined.

  (* Instead I could show that a monad transformer preserves ReqMonad *)
  #[export] Instance ReqMonad_M : ReqMonad M := {|
    req p := liftᵀ (req p)
  |}.

  (* Specification monad *)

  Definition W A :=
    T pure_wp A.

  #[export] Instance Monad_W : Monad W.
  Proof.
    apply transf_monad. exact _.
  Defined.

  #[export] Instance ReqMonad_W : ReqMonad W := {|
    req p := liftᵀ (req p)
  |}.

  (* Not just a transform, but order-enriched transformer.
    Here only stated for G.
  *)
  Context (Order_W : Order W) (MonoSpec_W : MonoSpec W).
  Context (wle_liftᵀ : ∀ A (w w' : pure_wp A), w ≤ᵂ w' → liftᵀ w ≤ᵂ liftᵀ w').

  Context {hr : ∀ A, Reflexive (wle (A := A))}.

  (* Effect observation *)

  Definition θ : observation M W.
  Proof.
    unshelve refine (mapᵀ (λ A (c : G A), bind (req c.π1) (λ h, ret (c.π2 h)))).
    1-6: exact _.
    constructor.
    - intros A x.
      apply sig_ext. simpl.
      extensionality p. apply propositional_extensionality.
      split.
      + intros []. assumption.
      + intro. exists I. assumption.
    - intros A B c k.
      apply sig_ext. simpl.
      extensionality post. apply propositional_extensionality.
      split.
      + intros [[h1 h2] h3].
        exists h1. exists h2. assumption.
      + intros [h1 [h2 h3]].
        exists (ex_intro _ h1 h2). assumption.
  Defined.

  Instance θ_lax : LaxMorphism θ.
  Proof.
    constructor.
    - intros A x.
      unfold θ. unshelve erewrite morph_ret. 1: exact _.
      1: apply mapᵀ_morph.
      reflexivity.
    - intros A B c f.
      unfold θ. unshelve erewrite morph_bind. 1: exact _.
      1: apply mapᵀ_morph.
      reflexivity.
  Qed.

  Instance θ_reqlax : ReqLaxMorphism Order_W θ.
  Proof.
    constructor.
    intros p.
    unfold θ. simpl.
    rewrite mapᵀ_liftᵀ. reflexivity.
  Qed.

  (* Partial Dijkstra monad *)

  Definition D A w :=
    PDM.D (θ := θ) (Word := Order_W) A w.

  #[export] Instance DijkstraMonad_D : DijkstraMonad (Word := Order_W) D := _.

  (* Lift from PURE *)

  Definition liftᵂ : spec_lift_pure W :=
    λ A w, liftᵀ w.

  Arguments liftᵂ [_].

  Instance hlift : PureSpec W Order_W liftᵂ.
  Proof.
    constructor.
    intros A w f. simpl. unfold liftᵂ.
    lazymatch goal with
    | |- ?lhs ≤ᵂ _ =>
      let T := type of lhs in
      evar (e : T) ;
      replace lhs with e
    end.
    2:{
      subst e. apply (f_equal (bind _)).
      extensionality h. apply liftᵀ_ret. exact _.
    }
    subst e.
    lazymatch goal with
    | |- ?lhs ≤ᵂ _ =>
      let T := type of lhs in
      evar (e : T) ;
      replace lhs with e
    end.
    2:{ subst e. apply liftᵀ_bind. exact _. }
    subst e.
    apply wle_liftᵀ.
    destruct w as [w hw]. simpl.
    intros post h.
    unshelve eexists.
    { eapply hw. 2:exact h.
      auto.
    }
    destruct f as [a ha]. apply ha. apply h.
  Qed.

  Definition liftᴾ :=
    liftᴾ MonoSpec_W θ_lax θ_reqlax _.

End DM4Free.