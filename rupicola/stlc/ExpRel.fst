module ExpRel

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open QTyp

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __closed terms__. **)
let rec (∋) (t:qType) (p:get_Type t * closed_exp) : Tot Type0 (decreases %[get_rel t;0]) =
  let fs_v = fst p in
  let e = snd p in
  match get_rel t with // way to "match" on F* types
  | QUnit -> fs_v == () /\ e == EUnit
  | QBool -> (fs_v == true /\ e == ETrue) \/ (fs_v == false /\ e == EFalse)
  | QArr #s1 #s2 r1 r2 -> begin
    let fs_f : s1 -> s2 = fs_v in
    match e with
    | ELam e' ->
      (forall (v:value) (fs_v:s1). (| s1, r1 |) ∋ (fs_v, v) ==>
        (| s2, r2 |) ⦂ (fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
  | QPair #s1 #s2 r1 r2 -> begin
    match e with
    | EPair e1 e2 ->
      (| s1, r1 |) ∋ (fst #s1 #s2 fs_v, e1) /\ (| s2, r2 |) ∋ (snd #s1 #s2 fs_v, e2)
    | _ -> False
  end
and (⦂) (t:qType) (p: get_Type t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
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
  | QUnit -> ()
  | QBool -> ()
  | QArr #s1 #s2 r1 r2 -> ()
  | QPair #s1 #s2 r1 r2 ->
    let EPair e1 e2 = e in
    lem_values_are_values (| s1, r1 |) (fst #s1 #s2 fs_e) e1;
    lem_values_are_values (| s2, r2 |) (snd #s1 #s2 fs_e) e2

let safety (t:qType) (fs_e:get_Type t) (e:closed_exp) : Lemma
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
        fun fsG -> f (index fsG 0)

    What is cool about this is to define compilation to STLC the environment is abstract.
 **)

let (∽) (#g:typ_env) #b (fsG:eval_env g) (s:gsub g b) : Type0 =
  forall (x:var). Some? (g x) ==>
    Some?.v (g x) ∋ (index fsG x, s x)

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __open terms__. **)
let equiv (#g:typ_env) (t:qType) (fs_e:fs_oexp g t) (e:exp) : Type0 =
  fv_in_env g e /\
  forall b (s:gsub g b) (fsG:eval_env g).
    fsG ∽ s ==>  t ⦂ (fs_e fsG, gsubst s e)

let (≈) (#g:typ_env) (#t:qType) (fs_v:fs_oexp g t) (e:exp) : Type0 =
  equiv #g t fs_v e

(** Equiv closed terms **)
let equiv_closed_terms (#t:qType) (fs_e:get_Type t) (e:closed_exp) :
  Lemma (requires equiv #empty t (fun _ -> fs_e) e)
        (ensures  t ⦂ (fs_e, e)) =
  eliminate forall b (s:gsub empty b) (fsG:eval_env empty).
    fsG ∽ s ==>  t ⦂ ((fun _ -> fs_e) fsG, gsubst s e) with true gsub_empty empty_eval

let lem_equiv_exp_are_equiv (g:typ_env) (#t:qType) (fs_e:get_Type t) (e:closed_exp) :
  Lemma (requires t ⦂ (fs_e, e))
        (ensures  equiv #empty t (fun _ -> fs_e) e) =
  introduce forall b (s:gsub empty b) (fsG:eval_env empty).
    fsG ∽ s ==>  t ⦂ ((fun _ -> fs_e) fsG, gsubst s e) with begin
    assert (gsubst s e == e)
  end

(** Rules **)

let tunit : qType =
  (| _, QUnit |)

let equiv_unit g
  : Lemma ((fun (_:eval_env g) -> ()) `equiv tunit` EUnit)
  = assert ((fun (_:eval_env g) -> ()) `equiv tunit` EUnit) by (explode ())

let tbool : qType =
  (| _, QBool |)

let equiv_true g
  : Lemma ((fun (_:eval_env g) -> true) `equiv tbool` ETrue)
  = assert ((fun (_:eval_env g) -> true) `equiv tbool` ETrue) by (explode ())

let equiv_false g
  : Lemma ((fun (_:eval_env g) -> false) `equiv tbool` EFalse)
  = assert ((fun (_:eval_env g) -> false) `equiv tbool` EFalse) by (explode ())

let equiv_var g (x:var{Some? (g x)})
  : Lemma ((fun (fsG:eval_env g) -> index fsG x) ≈ EVar x)
  =
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==>  Some?.v (g x) ⦂ (index fsG x, gsubst s (EVar x)) with begin
    introduce _ ==> _ with _. begin
      assert (Some?.v (g x) ∋ (index fsG x, s x));
      lem_values_are_expressions (Some?.v (g x)) (index fsG x) (s x)
    end
  end

let equiv_lam #g (t1:qType) (t2:qType) (f:fs_oexp g (t1 ^-> t2)) (body:exp) : Lemma
  (requires (fun (fsG:eval_env (extend t1 g)) -> f (tail #t1 fsG) (hd fsG)) ≈ body)
  (ensures f ≈ (ELam body)) =
  lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==>  (t1 ^-> t2) ⦂ (f fsG, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:get_Type t1). t1 ∋ (fs_v, v) ==>  t2 ⦂ (f fsG fs_v, subst_beta v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fsG' = stack fsG fs_v in
          eliminate forall b (s':gsub g' b) (fsG':eval_env g'). fsG' ∽ s' ==>  t2 ⦂ (f (tail #t1 fsG') (hd #t1 #g fsG'), (gsubst s' body))
            with false s' fsG';
          assert (fsG ∽ s);
          assert (stack fsG fs_v ∽ gsub_extend s t1 v);
          assert (t2 ⦂ (f (tail fsG') (hd fsG'), (gsubst s' body)));
          assert (hd (stack fsG fs_v) == fs_v);
          assert (t2 ⦂ (f (tail fsG') fs_v, (gsubst s' body)));
          assert (t2 ⦂ (f fsG fs_v, (gsubst s' body)));
          lem_substitution s t1 v body;
          assert (t2 ⦂ (f fsG fs_v, subst_beta v body'))
        end
      end;
      assert ((t1 ^-> t2) ∋ (f fsG, gsubst s (ELam body)));
      lem_values_are_expressions (t1 ^-> t2) (f fsG) (gsubst s (ELam body));
      assert ((t1 ^-> t2) ⦂ (f fsG, gsubst s (ELam body)))
    end
  end

let equiv_app #g
  (#t1:qType) (#t2:qType)
  (fs_e1:fs_oexp g (t1 ^-> t2)) (fs_e2:fs_oexp g t1)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2)
    (ensures (fun fsG -> (fs_e1 fsG) (fs_e2 fsG)) ≈ (EApp e1 e2))
  =
  lem_fv_in_env_app g e1 e2;
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==> t2 ⦂ ((fs_e1 fsG) (fs_e2 fsG), gsubst s (EApp e1 e2)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e2 = fs_e2 fsG in
    let fs_e = fs_e1 fs_e2 in
    let e = EApp (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EApp e1 e2) == e);
    let EApp e1 e2 = e in
    introduce fsG ∽ s ==>  t2 ⦂ (fs_e, e) with _. begin
      introduce forall (e':closed_exp). steps e e' /\ irred e' ==> t2 ∋ (fs_e, e') with begin
        introduce _ ==> t2 ∋ (fs_e, e') with h. begin
          let steps_e_e' : squash (steps e e') = () in
          FStar.Squash.map_squash #_ #(squash (t2 ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            let (e11, e2') = destruct_steps_eapp e1 e2 e' steps_e_e' in
            assert ((t1 ^-> t2) ∋ (fs_e1, ELam e11));
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

let equiv_if #g (#t:qType) (fs_e1:fs_oexp g tbool) (fs_e2:fs_oexp g t) (fs_e3:fs_oexp g t) (e1:exp) (e2:exp) (e3:exp) : Lemma
  (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2 /\ fs_e3 ≈ e3)
  (ensures (fun fsG -> if fs_e1 fsG then fs_e2 fsG else fs_e3 fsG) ≈ EIf e1 e2 e3) =
  lem_fv_in_env_if g e1 e2 e3;
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==> t ⦂ ((if fs_e1 fsG then fs_e2 fsG else fs_e3 fsG), gsubst s (EIf e1 e2 e3)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e = if fs_e1 then fs_e2 fsG else fs_e3 fsG in
    let e = EIf (gsubst s e1) (gsubst s e2) (gsubst s e3) in
    assert (gsubst s (EIf e1 e2 e3) == e);
    let EIf e1 e2 e3 = e in
    introduce fsG ∽ s ==>  t ⦂ (fs_e, e) with _. begin
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

let equiv_pair g (t1 t2:qType) (fs_e1:fs_oexp g t1) (fs_e2:fs_oexp g t2) (e1:exp) (e2:exp) : Lemma
  (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2)
  (ensures (fun fsG -> (fs_e1 fsG, fs_e2 fsG)) `equiv (t1 ^* t2)` EPair e1 e2) =
  lem_fv_in_env_pair g e1 e2;
  let t = t1 ^* t2 in
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==>  t ⦂ ((fs_e1 fsG, fs_e2 fsG), gsubst s (EPair e1 e2)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e2 = fs_e2 fsG in
    let fs_e = (fs_e1, fs_e2) in
    let e = EPair (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EPair e1 e2) == e);
    let EPair e1 e2 = e in
    introduce fsG ∽ s ==>  t ⦂ (fs_e, e) with _. begin
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

let equiv_pair_fst_app g (t1 t2:qType) (fs_e12:fs_oexp g (t1 ^* t2)) (e12:exp) : Lemma
  (requires fs_e12 `equiv (t1 ^* t2)` e12) (** is this too strict? we only care for the left to be equivalent. **)
  (ensures (fun fsG -> fst (fs_e12 fsG)) `equiv t1` (EFst e12)) =
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==>  t1 ⦂ (fst (fs_e12 fsG), gsubst s (EFst e12)) with begin
    let fs_e12 = fs_e12 fsG in
    let fs_e = fst fs_e12 in
    let e = EFst (gsubst s e12) in
    assert (gsubst s (EFst e12) == e);
    let EFst e12 = e in
    introduce fsG ∽ s ==>  t1 ⦂ (fs_e, e) with _. begin
      introduce forall (e':closed_exp). steps e e' /\ irred e' ==> t1 ∋ (fs_e, e') with begin
        introduce _ ==> t1 ∋ (fs_e, e') with h. begin
          let steps_e_e' : squash (steps e e') = () in
          FStar.Squash.map_squash #_ #(squash (t1 ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            let e12' = destruct_steps_epair_fst e12 e' steps_e_e' in
            eliminate (t1 ^* t2) ⦂ (fs_e12, e12) /\ steps e12 e12' /\ irred e12'
            returns (t1 ^* t2) ∋ (fs_e12, e12') with _ _. ();
            let EPair e1' e2' = e12' in
            assert (t1 ∋ (fs_e, e1'));
            lem_destruct_steps_epair_fst e1' e2' e';
            assert (t1 ∋ (fs_e, e'))
          )
        end
      end
    end
  end

let equiv_pair_fst g (t1 t2:qType)
  : Lemma
    (requires True)
    (ensures (fun _ -> fst #(get_Type t1) #(get_Type t2)) `equiv #g ((t1 ^* t2) ^-> t1)` (ELam (EFst (EVar 0))))
  =
  let tp = t1 ^* t2 in
  let t = tp ^-> t1 in
  let fs_e : (get_Type t1 & get_Type t2) -> get_Type t1 = fst in
  let fs_e' : eval_env g -> get_Type t = (fun _ -> fs_e) in
  let e = ELam (EFst (EVar 0)) in
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==>  t ⦂ (fs_e' fsG, gsubst s e) with begin
    assert (gsubst s e == e);
    assert (fs_e' fsG == fs_e);

    eliminate True /\ True
    returns t ∋ (fs_e, e) with _ _. begin
      introduce forall (v:value) (fs_v:get_Type tp). tp ∋ (fs_v, v) ==>
        t1 ⦂ (fs_e fs_v, subst_beta v (EFst (EVar 0))) with begin
        introduce _ ==> _ with _. begin
          lem_values_are_expressions tp fs_v v;
          lem_equiv_exp_are_equiv empty #tp fs_v v;
          assert ((fun _ -> fs_v) `equiv #empty tp` v);
          equiv_pair_fst_app empty t1 t2 (fun _ -> fs_v) v;
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

let equiv_pair_snd_app g (t1 t2:qType) (fs_e12:fs_oexp g (t1 ^* t2)) (e12:exp)
  : Lemma
    (requires fs_e12 `equiv (t1 ^* t2)` e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures (fun fsG -> snd (fs_e12 fsG)) `equiv t2` (ESnd e12))
  =
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==>  t2 ⦂ (snd (fs_e12 fsG), gsubst s (ESnd e12)) with begin
    let fs_e12 = fs_e12 fsG in
    let fs_e = snd fs_e12 in
    let e = ESnd (gsubst s e12) in
    assert (gsubst s (ESnd e12) == e);
    let ESnd e12 = e in
    introduce fsG ∽ s ==>  t2 ⦂ (fs_e, e) with _. begin
      introduce forall (e':closed_exp). steps e e' /\ irred e' ==> t2 ∋ (fs_e, e') with begin
        introduce _ ==> t2 ∋ (fs_e, e') with h. begin
          let steps_e_e' : squash (steps e e') = () in
          FStar.Squash.map_squash #_ #(squash (t2 ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            let e12' = destruct_steps_epair_snd e12 e' steps_e_e' in
            eliminate (t1 ^* t2) ⦂ (fs_e12, e12) /\ steps e12 e12' /\ irred e12'
            returns (t1 ^* t2) ∋ (fs_e12, e12') with _ _. ();
            let EPair e1' e2' = e12' in
            assert (t2 ∋ (fs_e, e2'));
            lem_destruct_steps_epair_snd e1' e2' e';
            assert (t2 ∋ (fs_e, e'))
          )
        end
      end
    end
  end

let equiv_pair_snd g (t1 t2:qType)
  : Lemma
    (requires True)
    (ensures (fun _ -> snd #(get_Type t1) #(get_Type t2)) `equiv #g ((t1 ^* t2) ^-> t2)` (ELam (ESnd (EVar 0))))
  =
  let tp = t1 ^* t2 in
  let t = tp ^-> t2 in
  let fs_e : (get_Type t1 & get_Type t2) -> get_Type t2 = snd in
  let fs_e' : eval_env g -> get_Type t = (fun _ -> fs_e) in
  let e = ELam (ESnd (EVar 0)) in
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==>  t ⦂ (fs_e' fsG, gsubst s e) with begin
    assert (gsubst s e == e);
    assert (fs_e' fsG == fs_e);

    eliminate True /\ True
    returns t ∋ (fs_e, e) with _ _. begin
      introduce forall (v:value) (fs_v:get_Type tp). tp ∋ (fs_v, v) ==>
        t2 ⦂ (fs_e fs_v, subst_beta v (ESnd (EVar 0))) with begin
        introduce _ ==> _ with _. begin
          lem_values_are_expressions tp fs_v v;
          lem_equiv_exp_are_equiv empty #tp fs_v v;
          assert ((fun _ -> fs_v) `equiv #empty tp` v);
          equiv_pair_snd_app empty t1 t2 (fun _ -> fs_v) v;
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
