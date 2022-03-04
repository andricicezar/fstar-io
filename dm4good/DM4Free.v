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

  (* Specification monad *)

  Definition W A :=
    T pure_wp A.

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

End DM4Free.