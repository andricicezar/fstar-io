(* Construction of a PDM using the monad G *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util structures guarded PURE PDM.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Section Guarded.

  (* Computation monad *)

  Context {M : Monad}.

  (* Specification monad *)

  Context {W : Monad} {Word : Order W} (hmono : MonoSpec W Word).

  Existing Instance trans.

  (* Effect observation *)

  Context {θ : observation M W} (hlax : LaxMorphism Word θ).

  Arguments θ [_].

  (* We first build a new computation monad with req *)
  Definition Mᴳ : ReqMonad.
  Proof.
    simple refine {|
      Mq := {|
        Mo A := G (M A) ;
        ret A x := G.(ret) (M.(ret) x)
      |} ;
      req p := G.(bind) (G.(req) p) (λ h, G.(ret) (M.(ret) h))
    |}.
    (* bind *)
    hnf. intros A B c f.
    exists (c.π1 ∧ ∀ x, (f x).π1). intro h.
    simple refine (M.(bind) (c.π2 _) (λ x, (f x).π2 _)).
    - apply h.
    - apply h.
  Defined.

  (* Now we extend the spec monad with req, we do this using a liftᵂ *)

  (* Context (liftᵂ : spec_lift_pure W).

  Definition Wᴳ *)

End Guarded.