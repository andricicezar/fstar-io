From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util.

(* Guarded monad *)

Definition G A :=
  ∑ (P : Prop), P → A.

Definition retᴳ [A] (x : A) : G A :=
  (True ; λ _, x).

Definition bindᴳ [A B] (x : G A) (f : A → G B) : G B.
Proof.
  exists (∃ (h : x.π1), (f (x.π2 h)).π1).
  simple refine (λ h, (f (x.π2 _)).π2 _).
  - destruct h. assumption.
  - destruct h as [h hf]. assumption.
Defined.

Definition reqᴳ [A] (p : Prop) (x : p → A) : G A :=
  (p ; x).