(* General construction of a partial DM *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util structures PURE.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Section PDM.

  (* Computational monad with assert/req *)

  Context {M : ReqMonad}.

  (* Specification monad *)

  Context {W : ReqMonad} {Word : Order W} (hmono : MonoSpec W Word).

  Existing Instance trans.

  (* Effect observation *)

  Context {θ : observation M W} (hlax : ReqLaxMorphism Word θ).

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

  (* Laws preservation *)

  Context {hMl : MonadLaws M} {hWl : MonadLaws W}.

  Lemma left_id :
    ∀ A w (x : A) (f : ∀ (x : A), D A (w x)),
      D.(bindᴰ) (D.(retᴰ) x) f ≅ f x.
  Proof.
    intros A w x f.
    unshelve eexists.
    { rewrite left_id. reflexivity. }
    (* Should use subcomp instead *)
  Abort.

End PDM.