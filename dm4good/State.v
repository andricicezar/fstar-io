(* Using the construction to derive state *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util structures guarded PURE PDM StateSpec.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Section State.

  Context (state : Type).

  (* Computation monad *)

  Definition M A :=
    state → G (state * A).

  Instance Monad_M : Monad M := {|
    ret A x := λ s₀, ret (s₀, x) ;
    bind A B c f := λ s₀, bind (c s₀) (λ '(s₁, x), f x s₁)
  |}.

  Instance ReqMonad_M : ReqMonad M := {|
    req p := λ s₀, bind (req p) (λ h, ret (s₀, h))
  |}.

  Definition getᴹ : M state :=
    λ s, ret (s, s).

  Definition putᴹ (s : state) : M unit :=
    λ s₀, ret (s, tt).

  (* Effect observation *)

  Definition θ' [A] (c : M A) : W' A :=
    λ post s₀,
      let '(p ; f) := c s₀ in
      ∃ (h : p), let '(s₁, x) := f h in post s₁ x.

  Instance θ_ismono : ∀ A (c : M A), Monotonous (θ' c).
  Proof.
    intros A c. intros P Q s₀ hPQ h.
    red. red in h. destruct (c s₀) as [p f].
    destruct h as [hp h]. exists hp.
    destruct (f hp) as [s₁ x]. apply hPQ. assumption.
  Qed.

  Definition θ [A] (c : M A) : W A :=
    as_wp (θ' c).

  Instance θ_lax : @LaxMorphism _ _ _ _ WStOrder θ.
  Proof.
    constructor.
    - intros A x. intros post s₀ h.
      cbn. exists I. red in h. assumption.
    - intros A B c f. intros post s₀ h.
      unfold bind. simpl. unfold θ'.
      unfold bind in h. simpl in h. unfold θ' in h.
      destruct (c s₀) as [p c']. clear c.
      destruct h as [hp h].
      simpl.
      unshelve eexists.
      { exists hp. destruct (c' hp) as [s₁ x]. destruct (f x s₁).
        simpl. destruct h. assumption.
      }
      simpl. destruct (c' hp) as [s₁ x]. destruct (f x s₁).
      simpl. destruct h. assumption.
  Qed.

  Instance θ_morph : @ReqLaxMorphism _ _ _ _ _ ReqMonad_W WStOrder θ _.
  Proof.
    constructor.
    intro p. intros post s₀ h.
    cbv. cbv in h.
    destruct h as [hp h].
    unshelve eexists.
    { exists hp. auto. }
    simpl. assumption.
  Qed.

  (* Partial Dijkstra monad *)

  Definition D A w :=
    PDM.D (θ := θ) (Word := WStOrder) A w.

  Instance DijkstraMonad_D : DijkstraMonad (Word := WStOrder) D :=
    PDM.DijkstraMonad_D WStMono θ_lax.

  Definition getᴰ : D state getᵂ.
  Proof.
    exists getᴹ.
    cbv. intros post s h. exists I. assumption.
  Defined.

  Definition putᴰ s : D unit (putᵂ s).
  Proof.
    exists (putᴹ s).
    cbv. intros post s₀ h. exists I. assumption.
  Defined.

  (* Lift from PURE *)

  Definition liftᴾ :=
    liftᴾ WStMono θ_lax θ_morph hlift.

  (* Laws *)

  Instance M_laws : MonadLaws M.
  Proof.
    constructor.
    - intros A B x f.
      simpl. (* Need funext *)
  Abort.

End State.