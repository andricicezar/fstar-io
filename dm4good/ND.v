(* Non-determinism *)

From Coq Require Import Utf8 RelationClasses List.
From PDM Require Import util structures guarded PURE GuardedPDM.

Import ListNotations.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(* Computation monad *)

Definition M A :=
  list A.

#[export] Instance Monad_M : Monad M := {|
  ret A x := [ x ] ;
  bind A B c f := concat (map f c)
|}.

(* Effect observation *)

Definition θ : observation M pure_wp.
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

Definition D A (w : pure_wp A) : Type :=
  GuardedPDM.D (M := M) (θ := θ) (λ A w, w) A w.

Definition liftᵂ : spec_lift_pure pure_wp :=
  λ A w, w.

#[local] Instance LaxMorphism_θᴳ :
  @LaxMorphism _ _ (Monad_Mᴳ _ _) _ _ (θᴳ (θ := θ) liftᵂ).
Proof.
  constructor.
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
Qed.

#[export] Instance DijkstraMonad_D : DijkstraMonad D :=
  GuardedPDM.DijkstraMonad_D _ _ _ _ _.

(* Lift from PURE *)

#[local] Instance ReqLaxMorphism_θᴳ :
  @ReqLaxMorphism _ _ _ (ReqMonad_Mᴳ _ _) _ _ pure_wp_ord (θᴳ (θ := θ) liftᵂ) LaxMorphism_θᴳ.
Proof.
  constructor.
  intro p. intros post h.
  cbv - [In]. cbv - [In] in h. destruct h as [hp h].
  unshelve eexists.
  { exists hp. auto. }
  simpl. intros ? [? | bot]. 2: contradiction.
  subst. assumption.
Qed.

Definition liftᴾ [A w] (f : PURE A w) : D A w :=
  liftᴾ MonoSpec_pure leafpred hleaf (λ A w, w) _ _ _ A w f.