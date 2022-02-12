(* Notes are in StateFree3.v *)

From Coq Require Import Utf8 RelationClasses.

Set Default Goal Selector "!".
Set Printing Projections.

Ltac forward_gen H tac :=
  match type of H with
  | ?X → _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

Notation val x := (let 'exist _ t _ := x in t).
Notation "⟨ u ⟩" := (exist _ u _).

Definition prf [A P] (p : { x : A | P x }) : P (val p).
Proof.
  destruct p. assumption.
Qed.

Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "( x ; y )" := (@existT _ _ x y).
Notation "( x ; y ; z )" := (x ; ( y ; z)).
Notation "( x ; y ; z ; t )" := (x ; ( y ; (z ; t))).
Notation "( x ; y ; z ; t ; u )" := (x ; ( y ; (z ; (t ; u)))).
Notation "( x ; y ; z ; t ; u ; v )" := (x ; ( y ; (z ; (t ; (u ; v))))).
Notation "x .π1" := (@projT1 _ _ x) (at level 3, format "x '.π1'").
Notation "x .π2" := (@projT2 _ _ x) (at level 3, format "x '.π2'").

Section State.

  Context (state : Type).

  (* Computation monad *)

  Inductive M A :=
  | retᴹ (x : A)
  | act_getᴹ (k : state → M A)
  | act_putᴹ (s : state) (k : M A).

  Arguments retᴹ [_].
  Arguments act_getᴹ [_].
  Arguments act_putᴹ [_].

  Fixpoint bindᴹ [A B] (c : M A) (f : A → M B) : M B :=
    match c with
    | retᴹ x => f x
    | act_getᴹ k => act_getᴹ (λ s, bindᴹ (k s) f)
    | act_putᴹ s k => act_putᴹ s (bindᴹ k f)
    end.

  Definition getᴹ : M state :=
    act_getᴹ (λ x, retᴹ x).

  Definition putᴹ (s : state) : M unit :=
    act_putᴹ s (retᴹ tt).

  Definition mapᴹ [A B] (f : A → B) (c : M A) : M B :=
    bindᴹ c (λ x, retᴹ (f x)).

  (* Specification monad *)

  Definition preᵂ := state → Prop.
  Definition postᵂ A := state → A → Prop.

  Definition W A := postᵂ A → preᵂ.

  Definition wle [A] (w₀ w₁ : W A) : Prop :=
    ∀ P s, w₁ P s → w₀ P s.

  Notation "x ≤ᵂ y" := (wle x y) (at level 80).

  Definition retᵂ [A] (x : A) : W A :=
    λ P s₀, P s₀ x.

  Definition bindᵂ [A B] (w : W A) (wf : A → W B) : W B :=
    λ P, w (λ s₁ x, wf x P s₁).

  Definition getᵂ : W state :=
    λ P s, P s s.

  Definition putᵂ (s : state) : W unit :=
    λ P s₀, P s tt.

  Instance trans [A] : Transitive (@wle A).
  Proof.
    intros x y z h₁ h₂. intros P s₀ h.
    apply h₁. apply h₂.
    assumption.
  Qed.

  (* Monotonicity *)

  Class Monotonous [A] (w : W A) :=
    ismono : ∀ (P Q : postᵂ A) s₀, (∀ s₁ x, P s₁ x → Q s₁ x) → w P s₀ → w Q s₀.

  Instance retᵂ_ismono [A] (x : A) : Monotonous (retᵂ x).
  Proof.
    intros P Q s₀ hPQ h.
    apply hPQ. apply h.
  Qed.

  Instance bindᵂ_ismono [A B] (w : W A) (wf : A → W B) :
    Monotonous w →
    (∀ x, Monotonous (wf x)) →
    Monotonous (bindᵂ w wf).
  Proof.
    intros mw mwf.
    intros P Q s₀ hPQ h.
    eapply mw. 2: exact h.
    simpl. intros s₁ x hf.
    eapply mwf. 2: exact hf.
    assumption.
  Qed.

  Instance getᵂ_ismono : Monotonous (getᵂ).
  Proof.
    intros P Q s₀ hPQ h.
    red. red in h.
    apply hPQ. assumption.
  Qed.

  Instance putᵂ_ismono : ∀ s, Monotonous (putᵂ s).
  Proof.
    intros s. intros P Q s₀ hPQ h.
    apply hPQ. assumption.
  Qed.

  Lemma bindᵂ_mono :
    ∀ [A B] (w w' : W A) (wf wf' : A → W B),
      Monotonous w' →
      w ≤ᵂ w' →
      (∀ x, wf x ≤ᵂ wf' x) →
      bindᵂ w wf ≤ᵂ bindᵂ w' wf'.
  Proof.
    intros A B w w' wf wf' mw' hw hwf.
    intros P s₀ h.
    red. red in h.
    apply hw. eapply mw'. 2: exact h.
    simpl. intros s₁ x hf. apply hwf. assumption.
  Qed.

  (* Effect observation (in two passes) *)

  Fixpoint θ₀ [A] (c : M A) (s₀ : state) : state * A :=
    match c with
    | retᴹ x => (s₀, x)
    | act_getᴹ k => θ₀ (k s₀) s₀
    | act_putᴹ s k => θ₀ k s
    end.

  Definition θ [A] (c : M A) : W A :=
    λ P s₀, let '(s₁, x) := θ₀ c s₀ in P s₁ x.

  Lemma θ_ret :
    ∀ A (x : A),
      θ (retᴹ x) ≤ᵂ retᵂ x.
  Proof.
    intros A x. intros P s₀ h.
    cbn. red in h. assumption.
  Qed.

  Lemma θ_bind :
    ∀ A B c f,
      θ (@bindᴹ A B c f) ≤ᵂ bindᵂ (θ c) (λ x, θ (f x)).
  Proof.
    intros A B c f.
    induction c as [| ? ih | ?? ih] in B, f |- *.
    - cbn. intros P s₀ h.
      assumption.
    - cbn. intros P s₀ h.
      apply ih. assumption.
    - cbn. intros P s₀ h.
      apply ih. assumption.
  Qed.

  (* Computational monad with guards *)

  Definition G A :=
    ∑ (P : Prop), P → A.

  Definition retᵍ [A] (x : A) : G A :=
    (True ; λ _, x).

  Definition bindᵍ [A B] (x : G A) (f : A → G B) : G B.
  Proof.
    exists (∃ (h : x.π1), (f (x.π2 h)).π1).
    simple refine (λ h, (f (x.π2 _)).π2 _).
    - destruct h. assumption.
    - destruct h as [h hf]. assumption.
  Defined.

  (* We sandwich the computational monad to be able to add precondtions
    anywhere.
  *)
  Definition Mᴳ A :=
    G (M (G A)).

  Definition retᴳ [A] (x : A) : Mᴳ A :=
    retᵍ (retᴹ (retᵍ x)).

  Definition bindᴳ [A B] (c : Mᴳ A) (f : A → Mᴳ B) : Mᴳ B.
  Proof.
    destruct c as [p c].
    exists p. intro hp.
    simple refine (bindᴹ (c hp) (λ x, _)).
    destruct x as [q x].
    (* Wait: here I have no surrounding G. So maybe the sandwich isn't the
      rigth approach after all? Or maybe I need a swap operation?
      Here from x and f I can build a new Mᴳ B but that's not what I need.

      So the sandwich doesn't have what is necessary to add requires at any
      point. In a sense GMG doesn't allow one to interleave
      requires and get/put. Should I try by adding another constructor to M?
      How would it work for S → S × A?

      Should I use a weird inductive construction taking the bind-closure?
      Then it'd be hard to get the monadic laws probably.
    *)
  Abort.

  Inductive g A :=
  | ret (x : M A)
  | require (p : Prop) (k : p → g A)
  | bind {B} (c : g B) (k : B → g A).

  (* Is something like the above desirable? *)

End State.