module EquivRel

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open SyntacticTypes

//#set-options "--print_implicits --print_universes"
//let test (f:(x:'a -> PURE Type0 ('w x))) (x:'a) : Type0 by (dump "H"; compute (); dump "H") =
//  'w x (fun _ -> True) ==>  f x

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __closed terms__. **)
let rec (∋) (t:typsr) (p:get_Type t * closed_exp) : Tot Type0 (decreases %[get_rel t;0]) =
  let fs_v = fst p in
  let e = snd p in
  match get_rel t with
  | RUnit -> fs_v == () /\ e == EUnit
  | RBool -> (fs_v == true /\ e == ETrue) \/ (fs_v == false /\ e == EFalse)
  | RArr #t1 #t2 #s1 #s2 r1 r2 -> begin
    let fs_f : s1 -> s2 = fs_v in
    match e with
    | ELam e' ->
      (forall (v:value) (fs_v:s1). (| t1, s1, r1 |) ∋ (fs_v, v) ==>
        (| t2, s2, r2 |) ⦂ (fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
  | RRefined #t' #s' r' p -> begin
    assert (p fs_v);
    (| t', s', r' |) ∋ (fs_v, e)
  end
  | RArrWP #t1 #t2 #s1 #s2 r1 r2 wp -> begin
    let fs_f : (x:s1 -> PURE s2 (wp x)) = fs_v in
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    match e with
    | ELam e' ->
      (forall (v:value) (fs_v:s1).
        (| t1, s1, r1 |) ∋ (fs_v, v) /\ as_requires (wp fs_v) ==>  (** Interesting that we do not need to quantify over post-conditions because of monotonicity **)
         (| t2, s2, r2 |) ⦂ (fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
and (⦂) (t:typsr) (p: get_Type t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
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
val get_v : #g:env -> fs_env g -> x:var{Some? (g x)} -> get_Type (Some?.v (g x))
val fs_extend : #g:env -> fs_s:fs_env g -> #t:typsr -> get_Type t -> fs_env (extend t g)
val fs_shrink : #t:typsr -> #g:env -> fs_env (extend t g) -> fs_env g

val lem_fs_extend #g (fs_s:fs_env g) #t (v:get_Type t) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fs_s x == get_v (fs_extend fs_s v) (x+1)) /\
  get_v (fs_extend fs_s v) 0 == v)
  [SMTPat (fs_extend fs_s v)]

val lem_fs_shrink #g #t (fs_s:fs_env (extend t g)) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fs_s (x+1) == get_v (fs_shrink fs_s) x))
  [SMTPat (fs_shrink fs_s)]

val shrink_extend_inverse #g (fs_s:fs_env g) #t (x:get_Type t) : Lemma (fs_shrink (fs_extend fs_s x) == fs_s)
  [SMTPat (fs_shrink (fs_extend fs_s x))]

let (∽) (#g:env) #b (s:gsub g b) (fs_s:fs_env g) : Type0 =
  forall (x:var). Some? (g x) ==>
    Some?.v (g x) ∋ (get_v fs_s x, s x)

type fs_open_term (g:env) (pre:fs_env g -> Type0) (a:Type) =
  s:(fs_env g){pre s} -> a

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __open terms__. **)
let equiv (#g:env) (t:typsr) (pre:fs_env g -> Type0) (fs_e:fs_open_term g pre (get_Type t)) (e:exp) : Type0 =
  fv_in_env g e /\
  forall b (s:gsub g b) (fs_s:fs_env g).
    s ∽ fs_s /\ pre fs_s ==>  t ⦂ (fs_e fs_s, gsubst s e)

let (≈) (#g:env) (#t:typsr) (#pre:fs_env g -> Type0) (fs_v:fs_open_term g pre (get_Type t)) (e:exp) : Type0 =
  equiv #g t pre fs_v e

(** Equiv closed terms **)
let equiv_closed_terms (#t:typsr) (fs_e:get_Type t) (e:closed_exp) :
  Lemma (requires equiv #empty t (fun _ -> True) (fun _ -> fs_e) e)
        (ensures  t ⦂ (fs_e, e)) =
  eliminate forall b (s:gsub empty b) (fs_s:fs_env empty).
    s ∽ fs_s ==>  t ⦂ ((fun _ -> fs_e) fs_s, gsubst s e) with true gsub_empty fs_empty

(** Rules **)

let tunit : typsr =
  (| _, _, RUnit |)

let equiv_unit g
  : Lemma ((fun (_:fs_env g) -> ()) `equiv tunit (fun _ -> True)` EUnit)
  = assert ((fun (_:fs_env g) -> ()) `equiv tunit (fun _ -> True)` EUnit) by (explode ())

let tbool : typsr =
  (| _, _, RBool |)

let equiv_true g
  : Lemma ((fun (_:fs_env g) -> true) `equiv tbool (fun _ -> True)` ETrue)
  = assert ((fun (_:fs_env g) -> true) `equiv tbool (fun _ -> True)` ETrue) by (explode ())

let equiv_false g
  : Lemma ((fun (_:fs_env g) -> false) `equiv tbool (fun _ -> True)` EFalse)
  = assert ((fun (_:fs_env g) -> false) `equiv tbool (fun _ -> True)` EFalse) by (explode ())

let equiv_var g (x:var{Some? (g x)})
  : Lemma ((fun (fs_s:fs_env g) -> get_v fs_s x) ≈ EVar x)
  = assert ((fun (fs_s:fs_env g) -> get_v fs_s x) ≈ EVar x) by (explode ())

let equiv_lam g (t1:typsr) (body:exp) (t2:typsr) (pre:fs_env g -> Type0) (f:fs_open_term g pre (get_Type (mk_arrow t1 t2))) : Lemma
  (requires (fun (fs_s:(s:(fs_env (extend t1 g)){pre s})) -> f (fs_shrink #t1 fs_s) (get_v fs_s 0)) ≈ body)
  (ensures f ≈ (ELam body)) =
  lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  introduce forall b (s:gsub g b) fs_s. s ∽ fs_s ==> mk_arrow t1 t2 ⦂ (f fs_s, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:get_Type t1). t1 ∋ (fs_v, v) ==>  t2 ⦂ (f fs_s fs_v, subst_beta v body') with begin
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
      assert (mk_arrow t1 t2 ∋ (f fs_s, gsubst s (ELam body)));
      lem_values_are_expressions (mk_arrow t1 t2) (f fs_s) (gsubst s (ELam body));
      assert (mk_arrow t1 t2 ⦂ (f fs_s, gsubst s (ELam body)))
    end
  end

let equiv_app g (t1:typsr) (t2:typsr) (e1:exp) (e2:exp) (fs_e1:fs_env g -> get_Type (mk_arrow t1 t2)) (fs_e2:fs_env g -> get_Type t1) : Lemma
  (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2)
  (ensures (fun fs_s -> (fs_e1 fs_s) (fs_e2 fs_s)) ≈ (EApp e1 e2)) =
  lem_fv_in_env_app g e1 e2;
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
            assert (mk_arrow t1 t2 ∋ (fs_e1', ELam e11));
            assert (t1 ∋ (fs_e2', e2'));
            eliminate forall (v:value) (fs_v:get_Type t1). t1 ∋ (fs_v, v) ==>
              t2 ⦂ (fs_e1' fs_v, subst_beta v e11)
            with e2' fs_e2';
            assert (t2 ⦂ (fs_e, subst_beta e2' e11));
            assert (t2 ∋ (fs_e, e'))
          )
        end
      end
    end
  end

let equiv_if g (t:typsr) (e1:exp) (e2:exp) (e3:exp) (fs_e1:fs_env g -> get_Type tbool) (fs_e2:fs_env g -> get_Type t) (fs_e3:fs_env g -> get_Type t) : Lemma
  (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2 /\ fs_e3 ≈ e3)
  (ensures (fun fs_s -> if fs_e1 fs_s then fs_e2 fs_s else fs_e3 fs_s) ≈ EIf e1 e2 e3) =
  lem_fv_in_env_if g e1 e2 e3;
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
            assert (tbool ∋ (fs_e1', e1'));
            assert (t ∋ (fs_e, e'))
          )
        end
      end
    end
  end

 (**
let equiv_lam_wp g (t1:typsr) (body:exp) (t2:typsr) wp (f:fs_env g -> get_Type (mk_arrow_wp t1 t2 wp)) : Lemma
  (requires (fun (fs_s:fs_env (extend t1 g)) -> f (fs_shrink #t1 fs_s) (get_v fs_s 0)) ≈ body)
            // the asymmetry is here. body is an open expression, while for f, I don't have an open expression
            // the equiv is quantifying over the free variable of body, but not get_v
  (ensures f ≈ (ELam body)) =
  admit ()
**)
