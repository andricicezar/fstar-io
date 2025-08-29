module ExpRel

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open TypRel

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __closed terms__. **)
let rec (∋) (t:typsr) (p:get_Type t * closed_exp) : Tot Type0 (decreases %[get_rel t;0]) =
  let fs_v = fst p in
  let e = snd p in
  match get_rel t with
  | RUnit -> fs_v == () /\ e == EUnit
  | RBool -> (fs_v == true /\ e == ETrue) \/ (fs_v == false /\ e == EFalse)
  | RArr #s1 #s2 r1 r2 -> begin
    let fs_f : s1 -> s2 = fs_v in
    match e with
    | ELam e' ->
      (forall (v:value) (fs_v:s1). (| s1, r1 |) ∋ (fs_v, v) ==>
        (| s2, r2 |) ⦂ (fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
  | RPair #s1 #s2 r1 r2 -> begin
    match e with
    | EPair e1 e2 ->
      (| s1, r1 |) ∋ (fst #s1 #s2 fs_v, e1) /\ (| s2, r2 |) ∋ (snd #s1 #s2 fs_v, e2)
    | _ -> False
  end
  | RDPair #t1 #s1 r1 s2 xr2 -> begin
    let fs_v : (x:s1 & s2 x) = fs_v in
    let (| t2, r2 |) = xr2 (dfst fs_v) in
    assume (r2 << get_rel t);
    match e with
    | EPair e1 e2 ->
      (| t1, s1, r1 |) ∋ (dfst fs_v, e1) /\
      (| t2, _,  r2 |) ∋ (dsnd fs_v, e2)
    | _ -> False
  end
and (⦂) (t:typsr) (p: get_Type t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
  let fs_e = fst p in
  let e = snd p in
  forall (e':closed_exp). steps e e' ==> irred e' ==> t ∋ (fs_e, e')

let lem_values_are_expressions t fs_e e : (** lemma used by Amal **)
  Lemma (requires t ∋ (fs_e, e))
        (ensures  t ⦂ (fs_e, e)) = admit ()

let rec lem_values_are_values t fs_e (e:closed_exp) :
  Lemma (requires t ∋ (fs_e, e))
        (ensures is_value e)
        (decreases e) =
  match get_rel t with
  | RUnit -> ()
  | RBool -> ()
  | RArr #s1 #s2 r1 r2 -> ()
  | RPair #s1 #s2 r1 r2 ->
    let EPair e1 e2 = e in
    lem_values_are_values (| s1, r1 |) (fst #s1 #s2 fs_e) e1;
    lem_values_are_values (| s2, r2 |) (snd #s1 #s2 fs_e) e2

let safety (t:typsr) (fs_e:get_Type t) (e:closed_exp) : Lemma
  (requires t ⦂ (fs_e, e))
  (ensures safe e) =
  introduce forall e'. steps e e' ==> is_value e' \/ can_step e' with begin
    introduce steps e e' ==> is_value e' \/ can_step e' with _. begin
      introduce irred e' ==> is_value e' with _. begin
        assert (t ∋ (fs_e, e'));
        lem_values_are_values t fs_e e';
        assert (is_value e')
      end
    end
  end

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

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __open terms__. **)
let equiv (#g:env) ((| s, r |):typsr) (fs_e:fs_env g -> get_Type t) (e:exp) : Type0 =
  fv_in_env g e /\
  forall b (s:gsub g b) (fs_s:fs_env g).
    s ∽ fs_s ==>  (| s fs_s, r fs_s |) ⦂ (fs_e fs_s, gsubst s e)

let (≈) (#g:env) (#t:typsr) (fs_v:fs_env g -> get_Type t) (e:exp) : Type0 =
  equiv #g t fs_v e

(** Equiv closed terms **)
let equiv_closed_terms (#t:typsr) (fs_e:get_Type t) (e:closed_exp) :
  Lemma (requires equiv #empty t (fun _ -> fs_e) e)
        (ensures  t ⦂ (fs_e, e)) =
  eliminate forall b (s:gsub empty b) (fs_s:fs_env empty).
    s ∽ fs_s ==>  t ⦂ ((fun _ -> fs_e) fs_s, gsubst s e) with true gsub_empty fs_empty

let lem_equiv_exp_are_equiv (g:env) (#t:typsr) (fs_e:get_Type t) (e:closed_exp) :
  Lemma (requires t ⦂ (fs_e, e))
        (ensures  equiv #empty t (fun _ -> fs_e) e) =
  introduce forall b (s:gsub empty b) (fs_s:fs_env empty).
    s ∽ fs_s ==>  t ⦂ ((fun _ -> fs_e) fs_s, gsubst s e) with begin
    assert (gsubst s e == e)
  end

(** Rules **)

let tunit : typsr =
  (| _, RUnit |)

let equiv_unit g
  : Lemma ((fun (_:fs_env g) -> ()) `equiv tunit` EUnit)
  = assert ((fun (_:fs_env g) -> ()) `equiv tunit` EUnit) by (explode ())

let tbool : typsr =
  (| _, RBool |)

let equiv_true g
  : Lemma ((fun (_:fs_env g) -> true) `equiv tbool` ETrue)
  = assert ((fun (_:fs_env g) -> true) `equiv tbool` ETrue) by (explode ())

let equiv_false g
  : Lemma ((fun (_:fs_env g) -> false) `equiv tbool` EFalse)
  = assert ((fun (_:fs_env g) -> false) `equiv tbool` EFalse) by (explode ())

let equiv_var g (x:var{Some? (g x)})
  : Lemma ((fun (fs_s:fs_env g) -> get_v fs_s x) ≈ EVar x)
  =
  introduce forall b (s:gsub g b) fs_s. s ∽ fs_s ==>  Some?.v (g x) ⦂ (get_v fs_s x, gsubst s (EVar x)) with begin
    introduce _ ==> _ with _. begin
      assert (Some?.v (g x) ∋ (get_v fs_s x, s x));
      lem_values_are_expressions (Some?.v (g x)) (get_v fs_s x) (s x)
    end
  end

let equiv_lam g (t1:typsr) (body:exp) (t2:typsr) (f:fs_env g -> get_Type (mk_arrow t1 t2)) : Lemma
  (requires (fun (fs_s:fs_env (extend t1 g)) -> f (fs_shrink #t1 fs_s) (get_v fs_s 0)) ≈ body)
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
    let fs_e1 = fs_e1 fs_s in
    let fs_e2 = fs_e2 fs_s in
    let fs_e = fs_e1 fs_e2 in
    let e = EApp (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EApp e1 e2) == e);
    let EApp e1 e2 = e in
    introduce s ∽ fs_s ==>  t2 ⦂ (fs_e, e) with _. begin
      introduce forall (e':closed_exp). steps e e' /\ irred e' ==> t2 ∋ (fs_e, e') with begin
        introduce _ ==> t2 ∋ (fs_e, e') with h. begin
          let steps_e_e' : squash (steps e e') = () in
          FStar.Squash.map_squash #_ #(squash (t2 ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            let (e11, e2') = destruct_steps_eapp e1 e2 e' steps_e_e' in
            assert (mk_arrow t1 t2 ∋ (fs_e1, ELam e11));
            introduce True ==>  t1 ∋ (fs_e2, e2') with _. begin
              assert (t1 ⦂ (fs_e2, e2));
              assert (steps e2 e2');
              assert (irred e2')
            end;
            eliminate forall (v:value) (fs_v:get_Type t1). t1 ∋ (fs_v, v) ==>
              t2 ⦂ (fs_e1 fs_v, subst_beta v e11)
            with e2' fs_e2;
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
    let fs_e1 = fs_e1 fs_s in
    let fs_e = if fs_e1 then fs_e2 fs_s else fs_e3 fs_s in
    let e = EIf (gsubst s e1) (gsubst s e2) (gsubst s e3) in
    assert (gsubst s (EIf e1 e2 e3) == e);
    let EIf e1 e2 e3 = e in
    introduce s ∽ fs_s ==>  t ⦂ (fs_e, e) with _. begin
      introduce forall (e':closed_exp). steps e e' /\ irred e' ==> t ∋ (fs_e, e') with begin
        introduce _ ==> t ∋ (fs_e, e') with h. begin
          let steps_e_e' : squash (steps e e') = () in
          FStar.Squash.map_squash #_ #(squash (t ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            let e1' = destruct_steps_eif e1 e2 e3 e' steps_e_e' in
            assert (tbool ∋ (fs_e1, e1'));
            assert (t ∋ (fs_e, e'))
          )
        end
      end
    end
  end

let equiv_pair g (t1 t2:typsr) (e1:exp) (e2:exp) (fs_e1:fs_env g -> get_Type t1) (fs_e2:fs_env g -> get_Type t2) : Lemma
  (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2)
  (ensures (fun fs_s -> (fs_e1 fs_s, fs_e2 fs_s)) `equiv (mk_pair t1 t2)` EPair e1 e2) =
  lem_fv_in_env_pair g e1 e2;
  let t = mk_pair t1 t2 in
  introduce forall b (s:gsub g b) fs_s. s ∽ fs_s ==>  t ⦂ ((fs_e1 fs_s, fs_e2 fs_s), gsubst s (EPair e1 e2)) with begin
    let fs_e1 = fs_e1 fs_s in
    let fs_e2 = fs_e2 fs_s in
    let fs_e = (fs_e1, fs_e2) in
    let e = EPair (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EPair e1 e2) == e);
    let EPair e1 e2 = e in
    introduce s ∽ fs_s ==>  t ⦂ (fs_e, e) with _. begin
      introduce forall (e':closed_exp). steps e e' /\ irred e' ==> t ∋ (fs_e, e') with begin
        introduce _ ==> t ∋ (fs_e, e') with h. begin
          let steps_e_e' : squash (steps e e') = () in
          FStar.Squash.map_squash #_ #(squash (t ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            let (e1', e2') = destruct_steps_epair e1 e2 e' steps_e_e' in
            assert (t1 ∋ (fs_e1, e1'));
            assert (t2 ∋ (fs_e2, e2'));
            assert (t ∋ (fs_e, EPair e1' e2'));
            lem_values_are_expressions t fs_e (EPair e1' e2')
          )
        end
      end
    end
  end

let equiv_pair_fst_app g (t1 t2:typsr) (e12:exp) (fs_e12:fs_env g -> get_Type t1 & get_Type t2) : Lemma
  (requires fs_e12 `equiv (mk_pair t1 t2)` e12) (** is this too strict? we only care for the left to be equivalent. **)
  (ensures (fun fs_s -> fst (fs_e12 fs_s)) `equiv t1` (EFst e12)) =
  introduce forall b (s:gsub g b) fs_s. s ∽ fs_s ==>  t1 ⦂ (fst (fs_e12 fs_s), gsubst s (EFst e12)) with begin
    let fs_e12 = fs_e12 fs_s in
    let fs_e = fst fs_e12 in
    let e = EFst (gsubst s e12) in
    assert (gsubst s (EFst e12) == e);
    let EFst e12 = e in
    introduce s ∽ fs_s ==>  t1 ⦂ (fs_e, e) with _. begin
      introduce forall (e':closed_exp). steps e e' /\ irred e' ==> t1 ∋ (fs_e, e') with begin
        introduce _ ==> t1 ∋ (fs_e, e') with h. begin
          let steps_e_e' : squash (steps e e') = () in
          FStar.Squash.map_squash #_ #(squash (t1 ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            let e12' = destruct_steps_epair_fst e12 e' steps_e_e' in
            eliminate (mk_pair t1 t2) ⦂ (fs_e12, e12) /\ steps e12 e12' /\ irred e12'
            returns (mk_pair t1 t2) ∋ (fs_e12, e12') with _ _. ();
            let EPair e1' e2' = e12' in
            assert (t1 ∋ (fs_e, e1'));
            lem_destruct_steps_epair_fst e1' e2' e';
            assert (t1 ∋ (fs_e, e'))
          )
        end
      end
    end
  end

let equiv_pair_fst g (t1 t2:typsr) : Lemma
  (requires True)
  (ensures (fun _ -> fst #(get_Type t1) #(get_Type t2)) `equiv #g (mk_arrow (mk_pair t1 t2) t1)` (ELam (EFst (EVar 0)))) =
  let tp = mk_pair t1 t2 in
  let t = mk_arrow tp t1 in
  let fs_e : (get_Type t1 & get_Type t2) -> get_Type t1 = fst in
  let fs_e' : fs_env g -> get_Type t = (fun _ -> fs_e) in
  let e = ELam (EFst (EVar 0)) in
  introduce forall b (s:gsub g b) fs_s. s ∽ fs_s ==>  t ⦂ (fs_e' fs_s, gsubst s e) with begin
    assert (gsubst s e == e);
    assert (fs_e' fs_s == fs_e);

    eliminate True /\ True
    returns t ∋ (fs_e, e) with _ _. begin
      introduce forall (v:value) (fs_v:get_Type tp). tp ∋ (fs_v, v) ==>
        t1 ⦂ (fs_e fs_v, subst_beta v (EFst (EVar 0))) with begin
        introduce _ ==> _ with _. begin
          lem_values_are_expressions tp fs_v v;
          lem_equiv_exp_are_equiv empty #tp fs_v v;
          assert ((fun _ -> fs_v) `equiv #empty tp` v);
          equiv_pair_fst_app empty t1 t2 v (fun _ -> fs_v);
          assert ((fun _ -> fs_e fs_v) `equiv #empty t1` (EFst v));
          equiv_closed_terms #t1 (fs_e fs_v) (EFst v);
          assert (subst_beta v (EFst (EVar 0)) == EFst v);
          ()
        end
      end
    end;

    assert (t ∋ (fs_e, e));
    lem_values_are_expressions t fs_e e;
    assert (t ⦂ (fs_e, e))
  end

let equiv_pair_snd_app g (t1 t2:typsr) (e12:exp) (fs_e12:fs_env g -> get_Type t1 & get_Type t2) : Lemma
  (requires fs_e12 `equiv (mk_pair t1 t2)` e12) (** is this too strict? we only care for the left to be equivalent. **)
  (ensures (fun fs_s -> snd (fs_e12 fs_s)) `equiv t2` (ESnd e12)) =
  introduce forall b (s:gsub g b) fs_s. s ∽ fs_s ==>  t2 ⦂ (snd (fs_e12 fs_s), gsubst s (ESnd e12)) with begin
    let fs_e12 = fs_e12 fs_s in
    let fs_e = snd fs_e12 in
    let e = ESnd (gsubst s e12) in
    assert (gsubst s (ESnd e12) == e);
    let ESnd e12 = e in
    introduce s ∽ fs_s ==>  t2 ⦂ (fs_e, e) with _. begin
      introduce forall (e':closed_exp). steps e e' /\ irred e' ==> t2 ∋ (fs_e, e') with begin
        introduce _ ==> t2 ∋ (fs_e, e') with h. begin
          let steps_e_e' : squash (steps e e') = () in
          FStar.Squash.map_squash #_ #(squash (t2 ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            let e12' = destruct_steps_epair_snd e12 e' steps_e_e' in
            eliminate (mk_pair t1 t2) ⦂ (fs_e12, e12) /\ steps e12 e12' /\ irred e12'
            returns (mk_pair t1 t2) ∋ (fs_e12, e12') with _ _. ();
            let EPair e1' e2' = e12' in
            assert (t2 ∋ (fs_e, e2'));
            lem_destruct_steps_epair_snd e1' e2' e';
            assert (t2 ∋ (fs_e, e'))
          )
        end
      end
    end
  end

let equiv_pair_snd g (t1 t2:typsr) : Lemma
  (requires True)
  (ensures (fun _ -> snd #(get_Type t1) #(get_Type t2)) `equiv #g (mk_arrow (mk_pair t1 t2) t2)` (ELam (ESnd (EVar 0)))) =
  let tp = mk_pair t1 t2 in
  let t = mk_arrow tp t2 in
  let fs_e : (get_Type t1 & get_Type t2) -> get_Type t2 = snd in
  let fs_e' : fs_env g -> get_Type t = (fun _ -> fs_e) in
  let e = ELam (ESnd (EVar 0)) in
  introduce forall b (s:gsub g b) fs_s. s ∽ fs_s ==>  t ⦂ (fs_e' fs_s, gsubst s e) with begin
    assert (gsubst s e == e);
    assert (fs_e' fs_s == fs_e);

    eliminate True /\ True
    returns t ∋ (fs_e, e) with _ _. begin
      introduce forall (v:value) (fs_v:get_Type tp). tp ∋ (fs_v, v) ==>
        t2 ⦂ (fs_e fs_v, subst_beta v (ESnd (EVar 0))) with begin
        introduce _ ==> _ with _. begin
          lem_values_are_expressions tp fs_v v;
          lem_equiv_exp_are_equiv empty #tp fs_v v;
          assert ((fun _ -> fs_v) `equiv #empty tp` v);
          equiv_pair_snd_app empty t1 t2 v (fun _ -> fs_v);
          assert ((fun _ -> fs_e fs_v) `equiv #empty t2` (ESnd v));
          equiv_closed_terms #t2 (fs_e fs_v) (ESnd v);
          assert (subst_beta v (ESnd (EVar 0)) == ESnd v);
          ()
        end
      end
    end;

    assert (t ∋ (fs_e, e));
    lem_values_are_expressions t fs_e e;
    assert (t ⦂ (fs_e, e))
  end
