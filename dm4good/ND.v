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

(* LeafPred *)

#[local] Instance leafpred : LeafPred M :=
  λ A x c, In x c.

Fixpoint leafine [A] (c : M A) : M { x : A | x ∈ c }.
Proof.
  destruct c as [| x c].
  - exact [].
  - refine (⟨ x ⟩ :: map (λ x, ⟨ val x ⟩) (leafine _ c)).
    + left. reflexivity.
    + destruct x. right. assumption.
Defined.

#[local] Instance hleaf : Leafine M leafpred :=
  leafine.

(* Partial DM *)

Definition D : DijkstraMonad pure_wp_ord.
Proof.
  simple refine (GuardedPDM.D (M := M) MonoSpec_pure (θ := θ) leafpred hleaf (λ A w, w) _).
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
    + simpl. exists hp.
      intros x hx. apply h. apply hx.
    + hnf. simpl. intros y hy.
      apply in_concat in hy. destruct hy as [l [hl hy]].
      apply in_map_iff in hl. destruct hl as [x [e hxc]].
      destruct x as [x hx].
      set (h' := h x hx) in *. clearbody h'. clear h.
      destruct h' as [hf h]. subst l.
      apply h. assumption.
  - intro p. intros post h.
    cbv - [In]. cbv - [In] in h. destruct h as [hp h].
    unshelve eexists.
    { exists hp. auto. }
    simpl. intros ? [? | bot]. 2: contradiction.
    subst. assumption.
Defined.

(* Lift from PURE *)

Definition liftᴾ [A w] (f : PURE A w) : D A w :=
  liftᴾ MonoSpec_pure leafpred hleaf (λ A w, w) _ _ A w f.