From Coq Require Import Utf8 RelationClasses PropExtensionality.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.

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

Definition coe {A B} (e : A = B) : A → B :=
  match e with
  | eq_refl => λ x, x
  end.

Definition heq {A B : Type} (x : A) (y : B) :=
  ∑ (e : A = B), coe e x = y.

Notation "x ≅ y" := (heq x y) (at level 80).

Lemma sig_ext :
  ∀ A (P : A → Prop) (u v : { x : A | P x }),
    val u = val v →
    u = v.
Proof.
  intros A P u v e.
  destruct u, v. subst. f_equal. apply proof_irrelevance.
Qed.