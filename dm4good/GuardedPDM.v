(* Construction of a PDM using the monad G *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util structures guarded PURE PDM.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Section Guarded.

  (* Computation monad *)

  Context {M : Monad}.

  (* Specification monad *)

  Context {W : Monad} {Word : Order W} (hmono : MonoSpec W Word).

  Existing Instance trans.

  (* Effect observation *)

  Context {θ : observation M W} (hlax : LaxMorphism Word θ).

  Arguments θ [_].

  (* We first build a new computation monad with req *)
  Definition Mᴳ : ReqMonad.
  Proof.
    simple refine {|
      Mq := {|
        Mo A := G (M A) ;
        ret A x := G.(ret) (M.(ret) x)
      |} ;
      req p := G.(bind) (G.(req) p) (λ h, G.(ret) (M.(ret) h))
    |}.
    (* bind *)
    hnf. intros A B c f.
    exists (c.π1 ∧ ∀ x, (f x).π1). intro h.
    simple refine (M.(bind) (c.π2 _) (λ x, (f x).π2 _)).
    - apply h.
    - apply h.
  Defined.

  (* Now we extend the spec monad with req, we do this using a liftᵂ *)
  (* TODO: Should it generally be built this way? *)

  Context (liftᵂ : spec_lift_pure W).

  Arguments liftᵂ [_].

  Definition Wᴳ : ReqMonad := {|
    Mq := W ;
    req p := liftᵂ (pure_wp_reqmon.(req) p)
  |}.

  (* New effect observation *)

  Definition θᴳ : observation Mᴳ Wᴳ :=
    λ A c, Wᴳ.(bind) (Wᴳ.(req) c.π1) (λ h, θ (c.π2 h)).

  (* We now extend the effect observation *)
  Instance hreqlax : @ReqLaxMorphism Mᴳ Wᴳ Word θᴳ.
  Proof.
    constructor. 1: constructor.
    - intros A x.
      unfold θᴳ.
      simpl. etransitivity.
      + eapply bind_mono.
        * admit. (* Maybe we need refl *)
        * intro y. apply θ_ret.
      + (* Would the laws help here? Not clear. *)
        admit.
    - intros A B c f.
      unfold θᴳ. simpl. (* Might be hard to find a general case here *)
      admit.
    - intro p.
      unfold θᴳ. cbn - [pure_wp_reqmon].
      (* Not even clear it works *)
      admit.
  Abort.

  (* Until we find the proper assumptions, we will assume it *)
  Context (hreqlax : @ReqLaxMorphism Mᴳ Wᴳ Word θᴳ).

  (* Partial Dijkstra monad *)

  Definition D : DijkstraMonad Word :=
    PDM.D (M := Mᴳ) (W := Wᴳ) hmono hreqlax.

  (* Lift from PURE *)

  Instance hlift : PureSpec Wᴳ Word liftᵂ.
  Proof.
    constructor.
    intros A w f.
    simpl.
  Abort.

  (* Same here *)
  Context (hlift : PureSpec Wᴳ Word liftᵂ).

  Check liftᴾ (M := Mᴳ) (W := Wᴳ) hmono hreqlax hlift.

End Guarded.