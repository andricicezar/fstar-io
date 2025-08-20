(** Mechanization of Section 2, Amal Ahmed's PhD Thesis: https://www.ccs.neu.edu/home/amal/ahmedthesis.pdf **)

module SemanticTyping

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open SyntacticTypes

let safe (e:closed_exp) : Type0 =
  forall e'. steps e e' ==> is_value e' \/ can_step e'

(** CA: should e be a value? **)
let rec (∈) (e:closed_exp) (t:typ) : Tot Type0 (decreases %[t;0]) =
  match t with
  | TUnit -> e == EUnit
  | TBool -> e == ETrue \/ e == EFalse
  | TArr t1 t2 ->
      match e with
      | ELam e' ->
          (forall (v:value). v ∈ t1 ==> subst_beta v e' ⋮ t2)
      | _ -> False
and (⋮) (e:closed_exp) (t:typ) : Tot Type0 (decreases %[t;1]) =
  forall (e':closed_exp). steps e e' ==> irred e' ==> e' ∈ t
(** definition of `⋮` is based on the fact that evaluation of
    expressions in the STLC always terminates **)

let lem_value_is_typed_exp e t
  : Lemma (e ∈ t ==> e ⋮ t)
  = admit () (** Amal uses such a lemma **)

let gsub_only_values #g #b (s:gsub g b) =
  forall x. Some? (g x) ==> (s x) ∈ (Some?.v (g x))

let sem_typing (g:env) (e:exp) (t:typ) : Type0 =
  fv_in_env g e /\
  (forall b (s:gsub g b).
    gsub_only_values s ==>  (gsubst s e) ⋮ t)

let lem_sem_typing_closed (e:exp) (t:typ) :
  Lemma (requires sem_typing empty e t)
        (ensures  e ⋮ t) =
  eliminate forall b (s:gsub empty b). (gsubst s e) ⋮ t with true gsub_empty

let safety (e:closed_exp) (t:typ) : Lemma
  (requires sem_typing empty e t)
  (ensures safe e) =
  introduce forall e'. steps e e' ==> is_value e' \/ Some? (step e') with begin
    introduce steps e e' ==> is_value e' \/ Some? (step e') with _. begin
      introduce irred e' ==> is_value e' with _. begin
        eliminate forall b (s: gsub empty b). (gsubst s e) ⋮ t with true gsub_empty;
        assert ((gsubst gsub_empty e) ⋮ t);
        lem_gsubst_empty_identity e;
        assert (e' ∈ t);
        assert (is_value e')
      end
    end
  end

(** Typing Rules as Lemmas *)
let typing_rule_unit (g:env) : Lemma (sem_typing g EUnit TUnit) =
  assert (sem_typing g EUnit TUnit) by (explode ())

let typing_rule_true (g:env) : Lemma (sem_typing g ETrue TBool) =
  assert (sem_typing g ETrue TBool) by (explode ())

let typing_rule_false (g:env) : Lemma (sem_typing g EFalse TBool) =
  assert (sem_typing g EFalse TBool) by (explode ())

let typing_rule_var (g:env) (x:nat) : Lemma
  (requires Some? (g x))
  (ensures sem_typing g (EVar x) (Some?.v (g x))) =
  assert (sem_typing g (EVar x) (Some?.v (g x))) by (explode ())

let typing_rule_lam g (t1:typ) (body:exp) (t2:typ) : Lemma
  (requires sem_typing (extend t1 g) body t2)
  (ensures sem_typing g (ELam body) (TArr t1 t2)) =
  lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  introduce forall b (s:gsub g b). gsub_only_values s ==> gsubst s (ELam body) ⋮ TArr t1 t2 with
    introduce _ ==> _ with _. begin
      let g' = extend t1 g in
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value). v ∈ t1 ==>  subst_beta v body' ⋮ t2 with begin
        introduce _ ==> _ with _. begin
          assert (sem_typing g' body t2);
          eliminate forall b (s:gsub g' b). gsub_only_values s ==> (gsubst s body) ⋮ t2 with false (gsub_extend s t1 v);
          assert (gsubst (gsub_extend s t1 v) body ⋮ t2);
          lem_substitution s t1 v body;
          assert (subst_beta v body' ⋮ t2)
        end
      end;
      assert (gsubst s (ELam body) ∈ TArr t1 t2);
      lem_value_is_typed_exp (gsubst s (ELam body)) (TArr t1 t2)
    end

let typing_rule_app g (e1:exp) (e2:exp) (t1:typ) (t2:typ) : Lemma
  (requires sem_typing g e1 (TArr t1 t2) /\ sem_typing g e2 t1)
  (ensures sem_typing g (EApp e1 e2) t2) =
  lem_fv_in_env_app g e1 e2;
  introduce forall b (s:gsub g b). gsub_only_values s ==> gsubst s (EApp e1 e2) ⋮ t2 with
    introduce gsub_only_values s ==> gsubst s (EApp e1 e2) ⋮ t2 with _. begin
      introduce forall e'. steps (gsubst s (EApp e1 e2)) e' /\ irred e' ==> e' ∈ t2 with begin
        introduce _ ==> e' ∈ t2 with h. begin
          let steps_e_e' : squash (steps (EApp (gsubst s e1) (gsubst s e2)) e') = () in
          FStar.Squash.map_squash #_ #(squash (e' ∈ t2)) steps_e_e' (fun steps_e_e' ->
            let (e11, e2') = destruct_steps_eapp (gsubst s e1) (gsubst s e2) e' steps_e_e' in
            assert (ELam e11 ∈ TArr t1 t2);
            assert (e2' ∈ t1);
            assert (subst_beta e2' e11 ⋮ t2);
            assert (e' ∈ t2)
          )
        end
      end
    end

let typing_rule_if g (e1:exp) (e2:exp) (e3:exp) (t:typ) : Lemma
  (requires sem_typing g e1 TBool /\ sem_typing g e2 t /\ sem_typing g e3 t)
  (ensures sem_typing g (EIf e1 e2 e3) t) =
  lem_fv_in_env_if g e1 e2 e3;
  introduce forall b (s:gsub g b). gsub_only_values s ==> gsubst s (EIf e1 e2 e3) ⋮ t with
    introduce gsub_only_values s ==> gsubst s (EIf e1 e2 e3) ⋮ t with _. begin
      introduce forall e'. steps (gsubst s (EIf e1 e2 e3)) e' /\ irred e' ==> e' ∈ t with begin
        introduce _ ==> e' ∈ t with h. begin
          let steps_e_e' : squash (steps (EIf (gsubst s e1) (gsubst s e2) (gsubst s e3)) e') = () in
          FStar.Squash.map_squash #_ #(squash (e' ∈ t)) steps_e_e' (fun steps_e_e' ->
            let e1' = destruct_steps_eif (gsubst s e1) (gsubst s e2) (gsubst s e3) e' steps_e_e' in
            assert (e1' ∈ TBool);
            assert (e' ∈ t)
          )
        end
      end
    end
