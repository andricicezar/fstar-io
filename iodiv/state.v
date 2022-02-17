From Coq Require Import Utf8 RelationClasses.

Set Default Goal Selector "!".
Set Printing Projections.

Ltac forward_gen H tac :=
  match type of H with
  | ?X → _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

Section State.

  Context (state : Type) (empty_state : state).

  (* Computation monad *)

  Definition M A :=
    state → state * A.

  Definition retᴹ [A] (x : A) : M A :=
    λ s₀, (s₀, x).

  Definition bindᴹ [A B] (c : M A) (f : A → M B) : M B :=
    λ s₀, let '(s₁, x) := c s₀ in f x s₁.

  Definition getᴹ : M state :=
    λ s, (s, s).

  Definition putᴹ (s : state) : M unit :=
    λ s₀, (s, tt).

  (* Specification monad *)

  Definition preᵂ := state → Prop.
  Definition postᵂ A := state → A → Prop.

  Definition wp A := postᵂ A → preᵂ.

  Definition wle [A] (w₀ w₁ : wp A) : Prop :=
    ∀ P s, w₁ P s → w₀ P s.

  Notation "x ≤ᵂ y" := (wle x y) (at level 80).

  Definition retᵂ [A] (x : A) : wp A :=
    λ P s₀, P s₀ x.

  Definition bindᵂ [A B] (w : wp A) (wf : A → wp B) : wp B :=
    λ P, w (λ s₁ x, wf x P s₁).

  Definition getᵂ : wp state :=
    λ P s, P s s.

  Definition putᵂ (s : state) : wp unit :=
    λ P s₀, P s tt.

  Instance trans [A] : Transitive (@wle A).
  Proof.
    intros x y z h₁ h₂. intros P s₀ h.
    apply h₁. apply h₂.
    assumption.
  Qed.

  (* Monotonicity *)

  Class Monotonous [A] (w : wp A) :=
    ismono : ∀ (P Q : postᵂ A) s₀, (∀ s₁ x, P s₁ x → Q s₁ x) → w P s₀ → w Q s₀.

  Instance retᵂ_ismono [A] (x : A) : Monotonous (retᵂ x).
  Proof.
    intros P Q s₀ hPQ h.
    apply hPQ. apply h.
  Qed.

  Instance bindᵂ_ismono [A B] (w : wp A) (wf : A → wp B) :
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
    ∀ [A B] (w w' : wp A) (wf wf' : A → wp B),
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

  (* Effect observation *)

  Definition θ [A] (c : M A) : wp A :=
    λ P s₀, let '(s₁, x) := c s₀ in P s₁ x.

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
    intros A B c f. intros P s₀ h.
    repeat red. repeat red in h.
    destruct (c s₀) as [s₁ x].
    assumption.
  Qed.

  (* Dijkstra monad *)

  Definition DM A w :=
    { c : M A | θ c ≤ᵂ w }.

  Notation val x := (let 'exist _ t _ := x in t).

  Definition retᴰ [A] (x : A) : DM A (retᵂ x).
  Proof.
    exists (retᴹ x).
    apply θ_ret.
  Defined.

  Definition bindᴰ [A B w wf] (c : DM A w) (f : ∀ x, DM B (wf x))
    `{Monotonous _ w} :
    DM B (bindᵂ w wf).
  Proof.
    exists (bindᴹ (val c) (λ x, val (f x))).
    etransitivity. 1: apply θ_bind.
    apply bindᵂ_mono.
    - assumption.
    - destruct c. simpl. assumption.
    - intro x. destruct (f x). simpl. assumption.
  Qed.

  Definition subcompᴰ [A w w'] (c : DM A w) {h : w ≤ᵂ w'} : DM A w'.
  Proof.
    exists (val c).
    etransitivity. 2: exact h.
    destruct c. assumption.
  Defined.

  Definition getᴰ : DM state getᵂ.
  Proof.
    exists getᴹ.
    cbv. auto.
  Defined.

  Definition putᴰ s : DM unit (putᵂ s).
  Proof.
    exists (putᴹ s).
    cbv. auto.
  Defined.

  (* Partial Dijkstra monad *)

  Definition lift_pre [A] (pre : Prop) : wp A :=
    λ P s₀, pre.

  (* Not sure about how to treat state *)
  (* Definition lift_post [A] (post : A → Prop) : wp A :=
    λ P s₀, ∀ x s₁, post x → P s₁ x. *)

  Definition pure_pre [A] (w : wp A) (P : Prop) :=
    (* ∀ Q s₀, w Q s₀ → P. *)
    lift_pre P ≤ᵂ w.

  (* Unsure about this too  *)
  (* Definition pure_post [A] (w : wp A) (post : A → Prop) :=
    (* ∀ s₀, w (λ s₁ x, post x) s₀. *)
    w ≤ᵂ lift_post post. *)

  Notation "⟨ u ⟩" := (exist _ u _).

  (* Definition refineᵂ [A] (P : A → Prop) (w : wp A) : wp (sig P) :=
    λ Q s₀, w (λ s₁ x, ∃ (h : P x), Q s₁ (exist _ x h)) s₀.

  Instance refineᵂ_ismono [A] (P : A → Prop) (w : wp A) {mw : Monotonous w} :
    Monotonous (refineᵂ P w).
  Proof.
    intros Q R s₀ hQR h.
    red. red in h.
    eapply mw. 2: exact h.
    simpl. intros s₁ x [hP hQ].
    exists hP. apply hQR. assumption.
  Qed. *)

  (** Is this the right definition? Maybe too weak?
      Related to the question of what is a good PDM with respect to a DM.
  *)
  Definition refineᵂ [A] (P : A → Prop) (w : wp A) : wp (sig P) :=
    λ Q s₀, w (λ s₁ x, ∀ (h : P x), Q s₁ (exist _ x h)) s₀.

  Instance refineᵂ_ismono [A] (P : A → Prop) (w : wp A) {mw : Monotonous w} :
    Monotonous (refineᵂ P w).
  Proof.
    intros Q R s₀ hQR h.
    red. red in h.
    eapply mw. 2: exact h.
    simpl. intros s₁ x hQ hP.
    apply hQR. apply hQ.
  Qed.

  Axiom PIR : ∀ (P : Prop) (h1 h2 : P), h1 = h2.

  (* Definition refineᴰ [A w] (c : DM A w) P {h : pure_post w P} :
    DM { x : A | P x } (refineᵂ P w).
  Proof.
    destruct c as [c hc].
    unshelve eexists.
    - intro s. pose (c' := c s). pose (s' := fst c'). pose (x := snd c').
      split. 1: exact s'.
      exists x.
      cbv in hc. specialize (hc (λ _, P) s). simpl in hc.
      destruct (c s) as [s₀ a]. subst c'. simpl in s', x. subst s' x.
      apply hc.
      cbv in h. specialize (h (λ _, P)). simpl in h.
      apply h. auto.
    - simpl. intros Q s hw.
      unfold θ. lazy in hw.
      apply hc in hw. unfold θ in hw.
      lazymatch goal with
      | |- Q _ (exist _ _ ?H) => set (hh := H) ; clearbody hh
      end.
      destruct (c s) as [s' x]. simpl in *.
      destruct hw as [hP hQ].
      assert (hh = hP) by apply PIR. subst.
      assumption.
  Defined. *)

  (* Can we instead have something related to a specific (pure) pre? *)
  Definition respects [A] (x : A) (w : wp A) :=
    ∃ s₀ s₁, ∀ P, w P s₀ → P s₁ x.

  Notation "x ∈ w" := (respects x w) (at level 50).

  Definition refᴰ [A w] (c : DM A w) : DM { x : A | x ∈ w } (refineᵂ _ w).
  Proof.
    destruct c as [c hc].
    unshelve eexists.
    - intro s. pose (c' := c s). pose (s' := fst c'). pose (x := snd c').
      split. 1: exact s'.
      exists x.
      exists s, s'. intros P h.
      cbv in hc. specialize (hc P s).
      forward hc. { assumption. }
      destruct (c s) as [s₀ a]. subst c'. simpl in s', x. subst s' x.
      assumption.
    - simpl. intros Q s hw.
      unfold θ. lazy in hw.
      apply hc in hw. unfold θ in hw.
      lazymatch goal with
      | |- Q _ (exist _ _ ?H) => set (hh := H) ; clearbody hh
      end.
      destruct (c s) as [s' x]. simpl in *.
      apply hw.
  Defined.

  Record PDM A (w : wp A) := {
    pdm_pre : Prop ;
    pdm_pure_pre : pure_pre w pdm_pre ;
    pdm_fun : pdm_pre → DM A w
  }.

  Arguments pdm_pre [_ _].
  Arguments pdm_pure_pre [_ _].
  Arguments pdm_fun [_ _].

  Definition retᴾ [A] (x : A) : PDM A (retᵂ x).
  Proof.
    exists True.
    - cbv. auto.
    - intros _. apply retᴰ.
  Defined.

  Definition getᴾ : PDM state getᵂ.
  Proof.
    exists True.
    - cbv. auto.
    - intros _. apply getᴰ.
  Defined.

  Definition putᴾ (s : state) : PDM unit (putᵂ s).
  Proof.
    exists True.
    - cbv. auto.
    - intros _. apply putᴰ.
  Defined.

  Definition bindᴾ [A B w wf] (c : PDM A w) (f : ∀ x, PDM B (wf x)) :
    Monotonous w →
    (∀ x, Monotonous (wf x)) →
    PDM B (bindᵂ w wf).
  Proof.
    intros mw mwf.
    exists (c.(pdm_pre) ∧ ∀ x, x ∈ w → pdm_pre (f x)).
    1:{
      intros P s₀ h. split.
      - eapply pdm_pure_pre. exact h.
      - intros x hx. destruct hx as [s [s' hx]].
        unfold bindᵂ in h.
        lazymatch type of h with
        | w ?P _ => specialize (hx P)
        end.
        simpl in hx.
        (* Again wrong state! This might be a fundamental issue. *)
        (* The question is, can we something else than x ∈ w, typically
          something that would be a consequence?
        *)
        eapply pdm_pure_pre. eapply hx.
        admit.
    }
    intro hc.
    simple refine (subcompᴰ (bindᴰ (refᴰ (pdm_fun c _)) (λ x, pdm_fun (f (val x)) _))).
    - intuition assumption.
    - destruct x as [x hx]. destruct hc as [? h].
      apply h. assumption.
    - intros Q s₀ h. red in h.
      red. red. eapply mw. 2: exact h.
      simpl. intros s₁ x hf hw.
      assumption.
  Abort.

  Definition prf [A P] (p : { x : A | P x }) : P (val p).
  Proof.
    destruct p. assumption.
  Qed.

  (* Trying to open the box and do it all without relying on bindᴹ *)
  Definition bindᴾ [A B w wf] (c : PDM A w) (f : ∀ x, PDM B (wf x)) :
    Monotonous w →
    (∀ x, Monotonous (wf x)) →
    PDM B (bindᵂ w wf).
  Proof.
    intros mw mwf.
    exists (
      ∃ (h : c.(pdm_pre)),
        ∀ s₀, (f (snd (val (c.(pdm_fun) h) s₀))).(pdm_pre)
    ).
    1:{
      intros P s₀ h.
      unshelve eexists.
      - eapply pdm_pure_pre. eassumption.
      - intros s.
        unfold bindᵂ in h.
        (* As always, the mismatch in state
          This tends to say that the problem is the PDM structure itself
          with its insufficient notion of pure pre. (Or I went for the wrong
          pure pre.)
        *)
        admit.
    }
    intro hpre.
    assert (hc : c.(pdm_pre)).
    { destruct hpre. assumption. }
    assert (hf : ∀ s₀, (f (snd (val (c.(pdm_fun) hc) s₀))).(pdm_pre)).
    { destruct hpre as [hc' hf].
      assert (hc = hc') by apply PIR. subst.
      assumption.
    }
    clear hpre.
    unshelve eexists.
    - intro s₀.
      pose (cᴰ := pdm_fun c hc).
      pose (cᴹ := val cᴰ). pose proof (prf cᴰ : _ cᴹ) as hcᴹ. simpl in hcᴹ.
      pose (s₁ := fst (cᴹ s₀)). pose (x := snd (cᴹ s₀)).
      pose (fᴾ := f x).
      assert (hfᴾ : fᴾ.(pdm_pre)).
      { apply hf.
        (* Here it's not clear how to get it but this is the right place to
        investigate. We don't have any bindᵂ assumption here so nothing relating
        f and c (or x) so no reason to believe that the pre holds.
        It *has* to come from the pure pre, meaning the pure pre must be
        something else that talks about the pre of f or wf x somehow.
        Can we make it more explicit by saying ∀ s₀, ?P (c s₀) or something?
        To get something as close as possible to goal we currently have.

        How about ∀ s₀, let '(s₁, x) := c s₀ in wf x ? s₁
        or just (f x).(pdm_pre)

        Again, I expect the ∀ s₀ to not be entailed by a specific instance of
        bindᵂ...

        The problem is that the pure pre must hold for all initial state so
        anything that mentions them is going to be hard to work with. Maybe the
        notion of pure pre must change or the pre should be taken after the
        initial state (but it would be very invasive).
        Thanks to monotonicity we don't have to think about specific posts and
        can take pTrue := λ s x, True.
        Sadly we can't take ∃ s, w pTrue s → pre because w might require s to
        be non-empty and then we could take the false precondition.
        This once again raises the question of how to make sure the PDM is good
        (at least with respect to the original DM). For instance, we could take
        always false as a precondition, and we could still prove the
        combinators.
        *)
      }
      pose (fᴰ := pdm_fun fᴾ hfᴾ).
      pose (fᴹ := val fᴰ).
      exact (fᴹ s₁).
    - simpl. intros P s h.
      unfold θ.
      destruct c as [pc ppc c]. simpl in *.
      set (cᴰ := c hc) in *. clearbody cᴰ. clear c pc ppc hc.
      destruct cᴰ as [c hc].
      set (hf' := hf s) in *. clearbody hf'. clear hf.
      unfold "≤ᵂ" in hc. specialize hc with (s := s).
      unfold θ in hc.
      set (c' := c s) in *. clearbody c'. clear c.
      destruct c' as [s' x]. simpl in *.
      set (f' := f x) in *. clearbody f'. clear f.
      destruct f' as [pf ppf f]. simpl in *.
      set (f' := f hf') in *. clearbody f'. clear f pf ppf hf'.
      destruct f' as [f hf].
      unfold "≤ᵂ" in hf. specialize hf with (s := s').
      unfold θ in hf.
      set (f' := f s') in *. clearbody f'. clear f.
      destruct f' as [s₁ y].
      apply hf. apply hc.
      apply h.
  Abort.

  (* In DM4Free the state monad is

    D A w := ∀ s : state, PURE A (w s)

    This makes me feel like there is a primitive notion of input somehow and
    that we must take this into account for state.

    In this case the general construction would require the computational
    monad to explicitly come with an input type.
    M A := I → C A
    (maybe I can also depend on A I don't know)
    and it would have to very some properties (typically related to
    θ and some _ ∈ _ notion).

    Then we wouldn't build the PDM on top of a DM but really all at once.
    Which is fine, especially since the requirements on the DM would still
    not be modified, only extended.

    Maybe:
    M A := ∀ (x : I A), C A x
    W A := ∀ (x : I A), W' A x (which could ignore the argument)
    D A w := ∀ (x : I A), D' A w x
    where D' A w x := {
      pre : Prop ;
      hpre : ∀ P arg, w x P arg → pre ;
      fun : pre → { y : C A x | θ x y ≤ᵂ w x }
    }

    Very unsure about over what the θ should be really.
    We still want θ to be a monad morphism so over M. Though maybe it can
    be split too? Will have to try on state then.
    (Could also try on state + IO to have both the ghost thing and real state.)

    Maybe:
    D'' A w x := {
      pre : Prop ;
      hpre : ∀ P arg, w x P arg → pre ;
      body : pre → C A x
    }
    D' A w := ∀ (x : I A), D'' A w x
    D A w := { f : D' A w | ∀ (x : I A) post arg (h : w x post arg), θ ((f x).(body) (pre_from f h)) }
    Still not ok because we do not recover a function in M A.
  *)

  (* To check that we have a PDM with respect to a DM we should check it's
    the least DM with lift from both PURE and DM.
    Typically by saying that for every other P' with both lifts there is a lift
    from P to P'.
  *)

  (* Lift from PURE (somehow) *)

  Definition pure_wp' A := (A → Prop) → Prop.

  Definition pure_mono [A] (w : pure_wp' A) : Prop :=
    ∀ (P Q : A → Prop), (∀ x, P x → Q x) → w P → w Q.

  Definition pure_wp A :=
    { w : pure_wp' A | pure_mono w }.

  Definition PURE A (w : pure_wp A) :=
    val w (λ _, True) → { x : A | ∀ P, val w P → P x }.

  Definition liftᵂ [A] (w : pure_wp A) : wp A :=
    λ P s₀, val w (λ x, P s₀ x).

  Definition liftᴾ [A w] (f : PURE A w) : PDM A (liftᵂ w).
  Proof.
    exists (val w (λ _, True)).
    1:{
      intros Q s₀ h.
      unfold lift_pre. unfold liftᵂ in h.
      destruct w as [w hw].
      eapply hw. 2: exact h.
      intuition auto.
    }
    intro hp. specialize (f hp).
    simple refine (subcompᴰ (retᴰ (val f))).
    intros P s h.
    destruct f as [f hf].
    cbv. apply hf. apply h.
  Defined.

End State.