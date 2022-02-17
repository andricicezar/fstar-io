(* Using the construction to derive state *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util guarded PURE PDM StateSpec.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.

Section State.

  Context (state : Type).

  (* Computation monad *)

  Definition M : ReqMonad := {|
    M A := state → G (state * A) ;
    ret A x := λ s₀, retᴳ (s₀, x) ;
    bind A B c f := λ s₀, bindᴳ (c s₀) (λ '(s₁, x), f x s₁) ;
    req p := λ s₀, reqᴳ p (λ h, (s₀, h))
  |}.

  Definition getᴹ : M state :=
    λ s, retᴳ (s, s).

  Definition putᴹ (s : state) : M unit :=
    λ s₀, retᴳ (s, tt).

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

  Instance θ_morph : LaxMorphism WStOrder θ.
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
    - intro p. intros post s₀ h.
      assumption.
  Qed.

  (* Partial Dijkstra monad *)

  Definition D : DijkstraMonad WStOrder :=
    PDM.D WStMono θ_morph.

  (* Universe inconsistency *)
  (* Definition getᴰ : D state getᵂ.
  Proof.
    exists getᴹ.
    cbv. intros post s h. exists I. assumption.
  Defined. *)

  Definition putᴰ s : D unit (putᵂ s).
  Proof.
    exists (putᴹ s).
    cbv. intros post s₀ h. exists I. assumption.
  Defined.

  (* Lift from PURE *)

  (* Universe problem again *)
  (* Definition liftᵂ [A] (w : pure_wp A) : WSt A.
  Proof.
    exists (λ P s₀, val w (λ x, P s₀ x)).
    intros P Q s₀ hPQ h.
    destruct w as [w mw].
    eapply mw. 2: exact h.
    apply hPQ.
  Defined.

  Instance hlift : PureSpec WSt WOrder liftᵂ.
  Proof.
    constructor.
    intros A w f.
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
  Qed.

  Check liftᴾ M WSt WOrder hmono θ θ_morph liftᵂ hlift. *)

End State.