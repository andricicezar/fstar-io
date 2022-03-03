From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util structures.

(* Guarded monad *)

Definition G (A : Type) :=
  ∑ (P : Prop), P → A.

#[export] Instance Monad_G : Monad G.
Proof.
  simple refine {|
    ret A x := (True ; λ _, x)
  |}.
  (* bind *)
  intros A B x f. simpl.
  exists (∃ (h : x.π1), (f (x.π2 h)).π1).
  simple refine (λ h, (f (x.π2 _)).π2 _).
  - destruct h. assumption.
  - destruct h as [h hf]. assumption.
Defined.

#[export] Instance ReqMonad_G : ReqMonad G := {|
  req p := (p ; λ h, h)
|}.
