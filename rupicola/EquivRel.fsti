module EquivRel

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open SyntacticTypes

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __closed terms__. **)
let rec (∋) (t:typ) (p:elab_typ t * closed_exp) : Tot Type0 (decreases %[t;0]) =
  let fs_v = fst p in
  let e = snd p in
  match t with
  | TUnit -> fs_v == () /\ e == EUnit
  | TBool -> (fs_v == true /\ e == ETrue) \/ (fs_v == false /\ e == EFalse)
  | TArr t1 t2 -> begin
    let fs_f : elab_typ t1 -> elab_typ t2 = fs_v in
    match e with
    | ELam e' ->
      (forall (v:value) (fs_v:elab_typ t1). t1 ∋ (fs_v, v) ==>
        t2 ⦂ (fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
and (⦂) (t:typ) (p: elab_typ t * closed_exp) : Tot Type0 (decreases %[t;1]) =
  let fs_e = fst p in
  let e = snd p in
  forall (e':closed_exp). steps e e' ==> irred e' ==> t ∋ (fs_e, e')

let lem_values_are_expressions t fs_e e : (** lemma used by Amal **)
  Lemma (requires t ∋ (fs_e, e))
        (ensures  t ⦂ (fs_e, e)) = admit ()

(** F* Evaluation Environment : variable -> value **)

(** We compile F* values, not F* expressions.
    When compiling F* lambdas, there is no way to match and get
    the body of the lambda.

    To avoid this limitation, we do closure conversion of F* lambdas:
    - be a lambda f:'a -> 'b
    - we wrap f to a function that takes as argument an F* evaluation environment
      that was extended to contain a value of type 'a
    - we take the value from the environment to open f:
        fun fs_s -> f (get_v fs_s 0)

    What is cool about this is to define compilation to STLC the environment is abstract.
 **)

val fs_env (g:env) : Type u#0
val fs_empty : fs_env empty
val get_v : #g:env -> fs_env g -> x:var{Some? (g x)} -> elab_typ (Some?.v (g x))
val fs_extend : #g:env -> fs_s:fs_env g -> #t:typ -> elab_typ t -> fs_env (extend t g)
val fs_shrink : #t:typ -> #g:env -> fs_env (extend t g) -> fs_env g

val lem_fs_extend #g (fs_s:fs_env g) #t (v:elab_typ t) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fs_s x == get_v (fs_extend fs_s v) (x+1)) /\
  get_v (fs_extend fs_s v) 0 == v)
  [SMTPat (fs_extend fs_s v)]

val lem_fs_shrink #g #t (fs_s:fs_env (extend t g)) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fs_s (x+1) == get_v (fs_shrink fs_s) x))
  [SMTPat (fs_shrink fs_s)]

val shrink_extend_inverse #g (fs_s:fs_env g) #t (x:elab_typ t) : Lemma (fs_shrink (fs_extend fs_s x) == fs_s)
  [SMTPat (fs_shrink (fs_extend fs_s x))]

let (∽) (#g:env) #b (s:gsub g b) (fs_s:fs_env g) : Type0 =
  forall (x:var). Some? (g x) ==>
    Some?.v (g x) ∋ (get_v fs_s x, s x)

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __open terms__. **)
let equiv (#g:env) (t:typ) (fs_e:fs_env g -> elab_typ t) (e:exp) : Type0 =
  fv_in_env g e /\
  forall b (s:gsub g b) (fs_s:fs_env g).
    s ∽ fs_s ==>  t ⦂ (fs_e fs_s, gsubst s e)

let (≈) (#g:env) (#t:typ) (fs_v:fs_env g -> elab_typ t) (e:exp) : Type0 =
  equiv #g t fs_v e

(** Equiv closed terms **)
let equiv_closed_terms (#t:typ) (fs_e:elab_typ t) (e:closed_exp) :
  Lemma (requires equiv #empty t (fun _ -> fs_e) e)
        (ensures  t ⦂ (fs_e, e)) =
  eliminate forall b (s:gsub empty b) (fs_s:fs_env empty).
    s ∽ fs_s ==>  t ⦂ ((fun _ -> fs_e) fs_s, gsubst s e) with true gsub_empty fs_empty

(** Rules **)

let equiv_unit g
  : Lemma ((fun (_:fs_env g) -> ()) `equiv TUnit` EUnit)
  = assert ((fun (_:fs_env g) -> ()) `equiv TUnit` EUnit) by (explode ())

let equiv_true g
  : Lemma ((fun (_:fs_env g) -> true) `equiv TBool` ETrue)
  = assert ((fun (_:fs_env g) -> true) `equiv TBool` ETrue) by (explode ())

let equiv_false g
  : Lemma ((fun (_:fs_env g) -> false) `equiv TBool` EFalse)
  = assert ((fun (_:fs_env g) -> false) `equiv TBool` EFalse) by (explode ())

let equiv_var g (x:var{Some? (g x)})
  : Lemma ((fun (fs_s:fs_env g) -> get_v fs_s x) ≈ EVar x)
  = assert ((fun (fs_s:fs_env g) -> get_v fs_s x) ≈ EVar x) by (explode ())

let equiv_lam g (t1:typ) (body:exp) (t2:typ) (f:fs_env g -> elab_typ (TArr t1 t2)) : Lemma
  (requires (fun (fs_s:fs_env (extend t1 g)) -> f (fs_shrink #t1 fs_s) (get_v fs_s 0)) ≈ body)
            // the asymmetry is here. body is an open expression, while for f, I don't have an open expression
            // the equiv is quantifying over the free variable of body, but not get_v
  (ensures f ≈ (ELam body)) =
  let g' = extend t1 g in
  assume (fv_in_env g (ELam body));
  introduce forall b (s:gsub g b) fs_s. s ∽ fs_s ==> TArr t1 t2 ⦂ (f fs_s, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:elab_typ t1). t1 ∋ (fs_v, v) ==>  t2 ⦂ (f fs_s fs_v, subst_beta v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fs_s' = fs_extend fs_s fs_v in
          eliminate forall b (s':gsub g' b) fs_s'. s' ∽ fs_s' ==>  t2 ⦂ (f (fs_shrink #t1 fs_s') (get_v fs_s' 0), (gsubst s' body))
            with false s' fs_s';
          assert (s ∽ fs_s);
          assert (gsub_extend s t1 v ∽ fs_extend fs_s fs_v);
          assert (t2 ⦂ (f (fs_shrink fs_s') (get_v fs_s' 0), (gsubst s' body)));
          assert (get_v (fs_extend fs_s fs_v) 0 == fs_v);
          assert (t2 ⦂ (f (fs_shrink fs_s') fs_v, (gsubst s' body)));
          assert (t2 ⦂ (f fs_s fs_v, (gsubst s' body)));
          lem_substitution s t1 v body;
          assert (t2 ⦂ (f fs_s fs_v, subst_beta v body'))
        end
      end;
      assert (TArr t1 t2 ∋ (f fs_s, gsubst s (ELam body)));
      lem_values_are_expressions (TArr t1 t2) (f fs_s) (gsubst s (ELam body));
      assert (TArr t1 t2 ⦂ (f fs_s, gsubst s (ELam body)))
    end
  end

let equiv_app g (t1:typ) (t2:typ) (e1:exp) (e2:exp) (fs_e1:fs_env g -> elab_typ (TArr t1 t2)) (fs_e2:fs_env g -> elab_typ t1) : Lemma
  (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2)
  (ensures (fun fs_s -> (fs_e1 fs_s) (fs_e2 fs_s)) ≈ (EApp e1 e2)) =
  assert (fv_in_env g e1);
  assert (fv_in_env g e2);
  assume (fv_in_env g (EApp e1 e2)); (** should be proveable **)
  introduce forall b (s:gsub g b) fs_s. s ∽ fs_s ==> t2 ⦂ ((fs_e1 fs_s) (fs_e2 fs_s), gsubst s (EApp e1 e2)) with begin
    let fs_e1' = fs_e1 fs_s in
    let fs_e2' = fs_e2 fs_s in
    let fs_e = fs_e1' fs_e2' in
    introduce s ∽ fs_s ==>  t2 ⦂ (fs_e, gsubst s (EApp e1 e2)) with _. begin
      introduce forall (e':closed_exp). steps (gsubst s (EApp e1 e2)) e' /\ irred e' ==> t2 ∋ (fs_e, e') with begin
        introduce _ ==> t2 ∋ (fs_e, e') with h. begin
          let steps_e_e' : squash (steps (EApp (gsubst s e1) (gsubst s e2)) e') = () in
          FStar.Squash.map_squash #_ #(squash (t2 ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            let (e11, e2') = destruct_steps_eapp (gsubst s e1) (gsubst s e2) e' steps_e_e' in
            assert (TArr t1 t2 ∋ (fs_e1', ELam e11));
            assert (t1 ∋ (fs_e2', e2'));
            assert (t2 ⦂ (fs_e, subst_beta e2' e11));
            assert (t2 ∋ (fs_e, e'))
          )
        end
      end
    end
  end

let equiv_if g (t:typ) (e1:exp) (e2:exp) (e3:exp) (fs_e1:fs_env g -> elab_typ TBool) (fs_e2:fs_env g -> elab_typ t) (fs_e3:fs_env g -> elab_typ t) : Lemma
  (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2 /\ fs_e3 ≈ e3)
  (ensures (fun fs_s -> if fs_e1 fs_s then fs_e2 fs_s else fs_e3 fs_s) ≈ EIf e1 e2 e3) =
  assert (fv_in_env g e1);
  assert (fv_in_env g e2);
  assert (fv_in_env g e3);
  assume (fv_in_env g (EIf e1 e2 e3)); (** should be proveable **)
  introduce forall b (s:gsub g b) fs_s. s ∽ fs_s ==> t ⦂ ((if fs_e1 fs_s then fs_e2 fs_s else fs_e3 fs_s), gsubst s (EIf e1 e2 e3)) with begin
    let fs_e1' = fs_e1 fs_s in
    let fs_e2' = fs_e2 fs_s in
    let fs_e3' = fs_e3 fs_s in
    let fs_e = if fs_e1' then fs_e2' else fs_e3' in
    introduce s ∽ fs_s ==>  t ⦂ (fs_e, gsubst s (EIf e1 e2 e3)) with _. begin
      introduce forall (e':closed_exp). steps (gsubst s (EIf e1 e2 e3)) e' /\ irred e' ==> t ∋ (fs_e, e') with begin
        introduce _ ==> t ∋ (fs_e, e') with h. begin
          let steps_e_e' : squash (steps (EIf (gsubst s e1) (gsubst s e2) (gsubst s e3)) e') = () in
          FStar.Squash.map_squash #_ #(squash (t ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            let e1' = destruct_steps_eif (gsubst s e1) (gsubst s e2) (gsubst s e3) e' steps_e_e' in
            assert (TBool ∋ (fs_e1', e1'));
            assert (t ∋ (fs_e, e'))
          )
        end
      end
    end
  end
