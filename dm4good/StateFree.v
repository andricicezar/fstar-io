(* Define a partial Dijkstra monad from a free monad for state *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util structures guarded PURE PDM StateSpec.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Section State.

  Context (state : Type).

  (* Computation monad with an extra require constructor *)

  Inductive M A :=
  | retᴹ (x : A)
  | act_getᴹ (k : state → M A)
  | act_putᴹ (s : state) (k : M A)
  | act_reqᴹ (p : Prop) (k : p → M A).

  Arguments retᴹ [_].
  Arguments act_getᴹ [_].
  Arguments act_putᴹ [_].
  Arguments act_reqᴹ [_].

  Fixpoint bindᴹ [A B] (c : M A) (f : A → M B) : M B :=
    match c with
    | retᴹ x => f x
    | act_getᴹ k => act_getᴹ (λ s, bindᴹ (k s) f)
    | act_putᴹ s k => act_putᴹ s (bindᴹ k f)
    | act_reqᴹ p k => act_reqᴹ p (λ h, bindᴹ (k h) f)
    end.

  Definition getᴹ : M state :=
    act_getᴹ (λ x, retᴹ x).

  Definition putᴹ (s : state) : M unit :=
    act_putᴹ s (retᴹ tt).

  Definition reqᴹ (p : Prop) : M p :=
    act_reqᴹ p (λ h, retᴹ h).

  Instance Monad_M : Monad M := {|
    ret := retᴹ ;
    bind := bindᴹ
  |}.

  Instance ReqMonad_M : ReqMonad M := {|
    req := reqᴹ
  |}.

  (* Effect observation *)

  Fixpoint θ [A] (c : M A) : W A :=
    match c with
    | retᴹ x => retᵂ x
    | act_getᴹ k => bindᵂ getᵂ (λ x, θ (k x))
    | act_putᴹ s k => bindᵂ (putᵂ s) (λ _, θ k)
    | act_reqᴹ p k => bindᵂ (reqᵂ p) (λ x, θ (k x))
    end.

  Instance θ_lax : @LaxMorphism _ _ _ _ WStOrder θ.
  Proof.
    constructor.
    - intros A x. intros P s₀ h.
      cbn. red in h. assumption.
    - intros A B c f.
      induction c as [| ? ih | ?? ih | ?? ih] in B, f |- *.
      + cbn. intros P s₀ h.
        assumption.
      + cbn. intros P s₀ h.
        apply ih. assumption.
      + cbn. intros P s₀ h.
        apply ih. assumption.
      + cbn. intros P s₀ h.
        red. red. destruct h as [hp h].
        exists hp. apply ih. assumption.
  Qed.

  Instance θ_morph : @ReqLaxMorphism _ _ _ _ _ ReqMonad_W WStOrder θ _.
  Proof.
    constructor.
    intros p. intros post s₀ h.
    assumption.
  Qed.

  (* Partial Dijkstra monad *)

  Definition D A w :=
    PDM.D (θ := θ) (Word := WStOrder) A w.

  Instance DijkstraMonad_D : DijkstraMonad (Word := WStOrder) D :=
    PDM.DijkstraMonad_D WStMono θ_lax.

  Definition getᴰ : D state getᵂ.
  Proof.
    exists getᴹ.
    cbv. auto.
  Defined.

  Definition putᴰ s : D unit (putᵂ s).
  Proof.
    exists (putᴹ s).
    cbv. auto.
  Defined.

  (* Lift from PURE *)

  Definition liftᴾ :=
    liftᴾ WStMono θ_lax θ_morph hlift.

  (* Laws *)

  Instance MSt_laws : MonadLaws M.
  Proof.
    constructor.
    - intros A B x f.
      reflexivity.
    - intros A c.
      induction c as [| ? ih | ?? ih | ?? ih].
      + reflexivity.
      + simpl. (* Only try up to funext *)
  Abort.

End State.