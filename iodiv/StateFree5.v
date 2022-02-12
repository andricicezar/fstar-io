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

  (* Dijkstra monad *)

  Definition D A w :=
    { c : M A | θ c ≤ᵂ w }.

  Definition retᴰ [A] (x : A) : D A (retᵂ x).
  Proof.
    exists (retᴹ x).
    apply θ_ret.
  Defined.

  Definition bindᴰ [A B w wf] (c : D A w) (f : ∀ x, D B (wf x))
    `{Monotonous _ w} :
    D B (bindᵂ w wf).
  Proof.
    exists (bindᴹ (val c) (λ x, val (f x))).
    etransitivity. 1: apply θ_bind.
    apply bindᵂ_mono.
    - assumption.
    - destruct c. simpl. assumption.
    - intro x. destruct (f x). simpl. assumption.
  Defined.

  Definition subcompᴰ [A w w'] (c : D A w) {h : w ≤ᵂ w'} : D A w'.
  Proof.
    exists (val c).
    etransitivity. 2: exact h.
    destruct c. assumption.
  Defined.

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

  Definition mapᴰ [A B w] (f : A → B) (c : D A w) `{Monotonous _ w} :
    D B (λ post s₀, w (λ s₁ x, post s₁ (f x)) s₀)
  := bindᴰ c (λ x, retᴰ (f x)).

  (* Partial Dijkstra monad *)

  Definition pre_ofᵂ [A] (w : W A) : Prop :=
    ∀ (pre : Prop), (∀ post s, w post s → pre) → pre.

  Definition P A (w : W A) :=
    pre_ofᵂ w → D A w.

  Definition retᴾ [A] (x : A) : P A (retᵂ x) :=
    λ _, retᴰ x.

  Definition refineᵂ [A] (P : A → Prop) (w : W A) : W (sig P) :=
    λ Q s₀, w (λ s₁ x, ∀ (h : P x), Q s₁ (exist _ x h)) s₀.

  Instance refineᵂ_ismono [A] (P : A → Prop) (w : W A) {mw : Monotonous w} :
    Monotonous (refineᵂ P w).
  Proof.
    intros Q R s₀ hQR h.
    red. red in h.
    eapply mw. 2: exact h.
    simpl. intros s₁ x hQ hP.
    apply hQR. apply hQ.
  Qed.

  Definition inv_getᵂ [A] (w : W A) : state → W A :=
    λ s post s₀, s = s₀ ∧ w post s.

  Lemma θ_get_inv :
    ∀ A (k : state → M A) (w : W A),
      θ (act_getᴹ k) ≤ᵂ w →
      bindᵂ getᵂ (inv_getᵂ w) ≤ᵂ w ∧ ∀ s, θ (k s) ≤ᵂ inv_getᵂ w s.
  Proof.
    intros A k w h.
    unfold "≤ᵂ" in h. unfold θ in h. simpl in h.
    unfold θ. split.
    - intros q s hw. red. red. red. intuition auto.
    - intros s q s' [e hw]. subst s'.
      apply h in hw. apply hw.
  Qed.

  (* Definition inv_putᵂ [A] (s : state) (w : W A) : W A :=
    λ post s₀,  *)

  Lemma θ_put_inv :
    ∀ A s (k : M A) (w : W A),
      θ (act_putᴹ s k) ≤ᵂ w →
      ∃ wk, θ k ≤ᵂ wk ∧ bindᵂ (putᵂ s) (λ _, wk) ≤ᵂ w.
  Proof.
    intros A s k w h.
    unfold "≤ᵂ" in h. unfold θ in h. simpl in h.
    unfold θ.
    exists (λ post s₀, s₀ = s ∧ w post s).
    split.
    - intros q s₀ [e hw]. subst s₀.
      apply h in hw. apply hw.
    - intros q s₀ hw.
      red. red. intuition auto.
      (* Here we lost the true initial state for w *)
  Abort.

  (* Maybe induction isn't the best way to go.
    We can also traverse c to add to each leaf the information of all
    previous reads and writes, information that we would need then to combine
    with the spec to obtain like intial and final state associated to a value
    / to a branch.
    Maybe we can take advantage of the fact that get ; c and c should have the
    same specification? And then do a get, traverse c with the intial state
    "in mind" and then doing a final get on the leaf?
    Like s₀ ← get ; map (λ x, s₁ ← get ; ret (s₀, s₁, x)) c

    Maybe we can take this guy and combine it with refineᴰ from before
    (either with w directly, or with any post that is good enough).
    What we'd like for a refinement is (s₀, s₁, x) | ∀ p, w p s₀ → p s₁ x
    is it easy to get, is it enough to give us enforce below?
  *)

  Definition annotateᴰ [A w] (c : D A w) `{Monotonous _ w} :=
    bindᴰ getᴰ (λ s₀, bindᴰ c (λ x, bindᴰ getᴰ (λ s₁, retᴰ (s₀, s₁, x)))).

  (* Trying to get it through leaf *)

  Fixpoint leaf [A] (x : A) (c : M A) :=
    match c with
    | retᴹ y => x = y
    | act_getᴹ k => ∃ s, leaf x (k s)
    | act_putᴹ s k => leaf x k
    end.

  Definition respects [A] (x : A) (w : W A) :=
    ∃ s₀ s₁, ∀ P, w P s₀ → P s₁ x.

  Notation "x ∈ w" := (respects x w) (at level 50).

  Fixpoint refᴹ [A] (c : M A) : M { x : A | leaf x c }.
  Proof.
    destruct c as [x | k | s k].
    - refine (retᴹ ⟨ x ⟩).
      reflexivity.
    - simpl. apply act_getᴹ.
      intro s₀.
      pose (c' := refᴹ _ (k s₀)).
      eapply mapᴹ. 2: eapply c'.
      intros [x h]. exists x.
      exists s₀. assumption.
    - simpl. apply (act_putᴹ s).
      apply refᴹ.
  Defined.

  Definition refᴰ [A w] (c : D A w) :
    D { x : A | leaf x (val c) } (refineᵂ _ w).
  Proof.
    exists (refᴹ (val c)).
    destruct c as [c hc].
    intros p s₀ hp. apply hc in hp.
    induction c as [x | k ih | s k ih] in s₀, p, hp |- *.
    - unfold θ in *. simpl in *. apply hp.
    - unfold θ in *. simpl in *.
      (* Cezar doesn't need map, so maybe I shouldn't either
        Cannot do it really, so maybe should do as he did with a forall q?
        Before, it might be a good idea to check whether leaf x c is enough
        to imply what we want about annotate
      *)
      admit.
    - admit.
  Abort.

  Definition annotateᴹ [A] (c : M A) :=
    bindᴹ getᴹ (λ s₀, bindᴹ c (λ x, bindᴹ getᴹ (λ s₁, retᴹ (s₀, s₁, x)))).

  Lemma val_annotateᴰ :
    ∀ A w (c : D A w) `{Monotonous _ w},
      val (annotateᴰ c) = annotateᴹ (val c).
  Proof.
    intros A w c mw. reflexivity.
  Qed.

  Lemma annotate_spec :
    ∀ A w (c : D A w) `{Monotonous _ w},
      θ (annotateᴹ (val c)) ≤ᵂ
      bindᵂ getᵂ (λ s₀, bindᵂ w (λ x, bindᵂ getᵂ (λ s₁, retᵂ (s₀, s₁, x)))).
  Proof.
    intros A w c mw.
    erewrite <- val_annotateᴰ.
    apply (prf (annotateᴰ c)).
  Qed.

  Lemma annotate_leaf :
    ∀ A w (c : D A w) s₀ s₁ x `{Monotonous _ w},
      leaf (s₀, s₁, x) (val (annotateᴰ c)) →
      ∀ p, w p s₀ → p s₁ x.
  Proof.
    intros A w c s₀ s₁ x mw h. intros p hw.
    pose proof (annotate_spec A w c) as ha.
    destruct c as [c hc].
    (* apply hc in hw. *)
    red in ha. unfold bindᵂ, getᵂ, retᵂ in ha.
    specialize ha with (s := s₀).
    specialize ha with (P := λ s '(u, v, y), p v y). simpl in ha.
    apply ha in hw.
    (* Does it help in any way? Or is the spec superfluous and we'll get
      everything we want from leaf we haven't used yet?
      It seems right now, it's just a more complicated way of using hc direclty.
    *)
  Abort.

  Definition enforceᴰ [A B w wf] (c : D A w) {h : pre_ofᵂ (@bindᵂ A B w wf)} :
    D { x : A | pre_ofᵂ (wf x) } (refineᵂ _ w).
  Proof.
    destruct c as [c hc].
    induction c as [ x | k ih | s k ih] in B, w, wf, hc, h |- *.
    - simple refine (subcompᴰ (retᴰ ⟨ x ⟩)).
      + simpl. intros p hp.
        apply h. intros post s hps.
        apply hc in hps.
        eapply hp. apply hps.
      + intros q s hq. red. red in hq.
        apply hc in hq. apply hq.
    - simple refine ⟨ act_getᴹ (λ s, _) ⟩.
      + apply θ_get_inv in hc as hk. destruct hk as [hwk hk].
        specialize (hk s).
        specialize ih with (1 := hk).
        specialize (ih B wf).
        forward ih.
        { intros pre hpre.
          apply h. intros post s₀ hw.
          eapply hpre.
          eapply bindᵂ_mono. 4: eapply hw.
          2:{
            intros q s₁ hq.
            red.
            (* We probably should not keep the same wf I guess
              maybe something which talks about s is necessary.
              Also not clear we need the bind≤ part in the lemma then.
            *)
            admit.
          }
          all: admit.
        }
        admit.
      + admit.
    - simple refine ⟨ act_putᴹ s _ ⟩.
  Admitted.

  Definition bindᴾ [A B w wf] (c : P A w) (f : ∀ x, P B (wf x)) :
    Monotonous w →
    P B (bindᵂ w wf).
  Proof.
    intro mw.
    refine (λ h, subcompᴰ (bindᴰ (enforceᴰ (c _)) (λ x, f (val x) (prf x)))).
    - intros p hp. apply h.
      intros post s₀ hpost.
      eapply hp. eapply hpost.
    - assumption.
    - intros Q s₀ hQ. red in hQ.
      red. red. eapply mw. 2: exact hQ.
      simpl. intros s₁ x hf hw.
      assumption.
  Defined.

End State.