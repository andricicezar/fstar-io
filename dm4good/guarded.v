From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util structures.

(* Guarded monad *)

Definition G : ReqMonad.
Proof.
  simple refine {|
    Mq := {|
      Mo A := ∑ (P : Prop), P → A ;
      ret A x := (True ; λ _, x)
      (* We provide bind with tactics *)
    |} ;
    req p := (p ; λ h, h)
  |}.
  (* bind *)
  intros A B x f. simpl.
  exists (∃ (h : x.π1), (f (x.π2 h)).π1).
  simple refine (λ h, (f (x.π2 _)).π2 _).
  - destruct h. assumption.
  - destruct h as [h hf]. assumption.
Defined.