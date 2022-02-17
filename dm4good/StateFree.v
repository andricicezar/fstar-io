(* Define a partial Dijkstra monad from a free monad for state *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util guarded PURE PDM StateSpec.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.

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

  Definition MSt : ReqMonad := {|
    PDM.M := M ;
    ret := retᴹ ;
    bind := bindᴹ ;
    req := reqᴹ
  |}.

  (* Effect observation *)

  Fixpoint θ [A] (c : MSt A) : WSt A :=
    match c with
    | retᴹ x => retᵂ x
    | act_getᴹ k => bindᵂ getᵂ (λ x, θ (k x))
    | act_putᴹ s k => bindᵂ (putᵂ s) (λ _, θ k)
    | act_reqᴹ p k => bindᵂ (reqᵂ p) (λ x, θ (k x))
    end.

  Instance θ_morph : LaxMorphism WStOrder θ.
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
    - intros p. intros post s₀ h.
      assumption.
  Qed.

  (* Partial Dijkstra monad *)

  Definition D : DijkstraMonad WStOrder :=
    PDM.D MSt WSt _ WStMono θ θ_morph.

  (* Definition getᴰ : D state getᵂ.
  Proof.
    exists getᴹ.
    cbv. auto.
  Defined. *)

  Definition putᴰ s : D unit (putᵂ s).
  Proof.
    exists (putᴹ s).
    cbv. auto.
  Defined.

  (* Lift from PURE *)

  (* Definition liftᵂ [A] (w : pure_wp A) : WSt A.
    λ P s₀, val w (λ x, P s₀ x).

  Definition liftᴾ [A w] (f : PURE A w) : D A (liftᵂ w).
  Proof.
    refine (subcompᴰ (bindᴰ (reqᴰ (val w (λ _, True))) (λ h, retᴰ (val (f h))))).
    intros P s h.
    assert (hpre : val w (λ _, True)).
    { unfold liftᵂ in h.
      destruct w as [w hw].
      eapply hw. 2: exact h.
      auto.
    }
    cbv. exists hpre.
    pose proof (prf (f hpre)) as hf. simpl in hf.
    apply hf in h. assumption.
  Defined. *)

End State.