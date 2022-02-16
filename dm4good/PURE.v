(* Encoding of PURE *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util.

Set Default Goal Selector "!".
Set Printing Projections.

Definition pure_wp' A := (A → Prop) → Prop.

Definition pure_mono [A] (w : pure_wp' A) : Prop :=
  ∀ (P Q : A → Prop), (∀ x, P x → Q x) → w P → w Q.

Definition pure_wp A :=
  { w : pure_wp' A | pure_mono w }.

Definition PURE A (w : pure_wp A) :=
  val w (λ _, True) → { x : A | ∀ P, val w P → P x }.