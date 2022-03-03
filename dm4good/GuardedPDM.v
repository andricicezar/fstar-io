(* Construction of a PDM using the monad G *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util structures guarded PURE PDM.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Class LeafPred (M : Type → Type) :=
  leaf : ∀ A, A → M A → Prop.

Notation "x ∈ c" := (leaf _ x c) (at level 80).

Class Leafine M (hleaf : LeafPred M) :=
  leafine : ∀ A (c : M A), M { x : A | x ∈ c }.

Arguments leafine {_ _ _} [_].

Section Guarded.

  (* Computation monad *)

  Context {M} `{Monad M}.

  (* Specification monad *)

  Context {W} `{Monad W} {Word : Order W} (hmono : MonoSpec W).

  (* Effect observation *)

  Context {θ : observation M W} (hlax : LaxMorphism θ).

  Arguments θ [_].

  (* We require a LiftPred before we get to partiality *)

  Context (leafpred : LeafPred M) (hleaf : Leafine M leafpred).

  (* We first build a new computation monad with req *)

  Definition Mᴳ A := G (M A).

  #[refine] Instance Monad_Mᴳ : Monad Mᴳ := {|
    ret A x := ret (M := G) (ret x)
  |}.
  Proof.
    hnf. intros A B c f.
    exists (∃ (h : c.π1), ∀ x, x ∈ c.π2 h → (f x).π1). intro h.
    simple refine (bind (leafine (c.π2 _)) (λ x, (f (val x)).π2 _)).
    - apply h.
    - destruct h as [hp h]. destruct x as [x hx]. apply h.
      apply hx.
  Defined.

  Instance ReqMonad_Mᴳ : ReqMonad Mᴳ := {|
    req p := bind (req p) (λ h, ret (M := G) (ret (M := M) h))
  |}.

  (* Now we extend the spec monad with req, we do this using a liftᵂ *)
  (* TODO: Should it generally be built this way? *)

  Context (liftᵂ : spec_lift_pure W).

  Arguments liftᵂ [_].

  Instance ReqMonad_W : ReqMonad W := {|
    req p := liftᵂ (req p)
  |}.

  (* New effect observation *)

  Definition θᴳ : observation Mᴳ W :=
    λ A c, bind (req c.π1) (λ h, θ (c.π2 h)).

  (* We now extend the effect observation *)
  (* Instance hreqlax : ReqLaxMorphism Word θᴳ.
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
  Abort. *)

  (* Until we find the proper assumptions, we will assume it *)
  Context (θᴳ_lax : LaxMorphism θᴳ) (θᴳ_reqlax : ReqLaxMorphism Word θᴳ).

  (* Partial Dijkstra monad *)

  Definition D A w :=
    PDM.D (θ := θᴳ) A w.

  Instance DijkstraMonad_D : DijkstraMonad D :=
    PDM.DijkstraMonad_D hmono θᴳ_lax.

  (* Lift from PURE *)

  Instance hlift : PureSpec W Word liftᵂ.
  Proof.
    constructor.
    intros A w f.
    simpl.
  Abort.

  (* Same here *)
  Context (hlift : PureSpec W Word liftᵂ).

  Definition liftᴾ :=
    liftᴾ (M := Mᴳ) (W := W) hmono θᴳ_lax θᴳ_reqlax hlift.

End Guarded.