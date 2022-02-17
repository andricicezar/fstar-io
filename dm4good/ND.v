(* Non-determinism *)

From Coq Require Import Utf8 RelationClasses List.
From PDM Require Import util structures guarded PURE GuardedPDM.

Import ListNotations.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(* Computation monad *)

Definition M : Monad := {|
  Mo A := list A ;
  ret A x := [ x ] ;
  bind A B c f := concat (map f c)
|}.

(* Effect observation *)

Definition θ : observation M pure_wp_monad.
Proof.
  intros A c.
  exists (λ post, ∀ x, In x c → post x).
  intros P Q hPQ h. intros x hx.
  apply hPQ. apply h. apply hx.
Defined.

(* Partial DM *)

Definition D : DijkstraMonad pure_wp_ord.
Proof.
  simple refine (GuardedPDM.D (M := M) MonoSpec_pure (θ := θ) (λ A w, w) _).
  (* Proving we still have a lax morphism *)
  constructor. 1: constructor.
  - intros A x. intros post h.
    cbv - [In] in *.
    exists I. intros y hy. destruct hy. 2: contradiction.
    subst. apply h.
  - intros A B c f. intros post h.
    destruct c as [p c].
    hnf. hnf in h.
    destruct h as [hp h]. simpl in hp, h.
    unshelve eexists.
    + simpl. split. 1: apply hp.
      intro x.
      (* Of course I actually need the return_of if I do not go deep.
        Hence, the unsuccessful general attempt.
        But we don't need to put the refinement inside the bind, so maybe it's
        not so bad. Maybe there only needs to exist a return_of like predicate
        to use in the Mᴳ.(bind) construction.
      *)
      give_up.
    + admit.
  - intro p. intros post h.
    cbv - [In]. cbv - [In] in h. destruct h as [hp h].
    unshelve eexists.
    { exists hp. auto. }
    simpl. intros ? [? | bot]. 2: contradiction.
    subst. assumption.
Abort.