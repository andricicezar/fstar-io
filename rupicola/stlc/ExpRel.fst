module ExpRel

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open QTyp

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __closed terms__. **)
let rec (∋) (t:qType) (p:fs_val t * closed_exp) : Tot Type0 (decreases %[get_rel t;0]) =
  let (fs_v, e) = p in
  match get_rel t with // way to "match" on F* types
  | QUnit -> fs_v == () /\ e == EUnit
  | QBool -> (fs_v == true /\ e == ETrue) \/ (fs_v == false /\ e == EFalse)
  | QString -> (match e with | EString s -> fs_v == s | _ -> False)
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
  | QSum #s1 #s2 r1 r2 -> begin
    let fs_v : either s1 s2 = fs_v in
    match fs_v, e with
    | Inl fs_v', EInl e' -> (| s1, r1 |) ∋ (fs_v', e')
    | Inr fs_v', EInr e' -> (| s2, r2 |) ∋ (fs_v', e')
    | _ -> False
  end
and (⦂) (t:qType) (p: fs_val t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
  let (fs_e, e) = p in
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
  | QString -> ()
  | QArr #s1 #s2 r1 r2 -> ()
  | QPair #s1 #s2 r1 r2 ->
    let EPair e1 e2 = e in
    lem_values_are_values (| s1, r1 |) (fst #s1 #s2 fs_e) e1;
    lem_values_are_values (| s2, r2 |) (snd #s1 #s2 fs_e) e2
  | QSum #s1 #s2 r1 r2 ->
    match fs_e, e with
    | Inl fs_e', EInl e' -> lem_values_are_values (| s1, r1 |) fs_e' e'
    | Inr fs_e', EInr e' -> lem_values_are_values (| s2, r2 |) fs_e' e'


let safety (t:qType) (fs_e:fs_val t) (e:closed_exp) : Lemma
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
let equiv (#g:typ_env) (t:qType) (fs_e:fs_oval g t) (e:exp) : Type0 =
  fv_in_env g e /\
  forall b (s:gsub g b) (fsG:eval_env g).
    fsG ∽ s ==>  t ⦂ (fs_e fsG, gsubst s e)

let (≈) (#g:typ_env) (#t:qType) (fs_v:fs_oval g t) (e:exp) : Type0 =
  equiv #g t fs_v e

(** Equiv closed terms **)
let equiv_closed_terms (#t:qType) (fs_e:fs_val t) (e:closed_exp) :
  Lemma (requires equiv #empty t (fun _ -> fs_e) e)
        (ensures  t ⦂ (fs_e, e)) =
  eliminate forall b (s:gsub empty b) (fsG:eval_env empty).
    fsG ∽ s ==>  t ⦂ ((fun _ -> fs_e) fsG, gsubst s e) with true gsub_empty empty_eval

let lem_equiv_exp_are_equiv (g:typ_env) (#t:qType) (fs_e:fs_val t) (e:closed_exp) :
  Lemma (requires t ⦂ (fs_e, e))
        (ensures  equiv #empty t (fun _ -> fs_e) e) =
  introduce forall b (s:gsub empty b) (fsG:eval_env empty).
    fsG ∽ s ==>  t ⦂ ((fun _ -> fs_e) fsG, gsubst s e) with begin
    assert (gsubst s e == e)
  end

(** Rules **)

let equiv_unit g
  : Lemma ((fun (_:eval_env g) -> ()) `equiv qUnit` EUnit)
  =
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==>  qUnit ⦂ ((), gsubst s EUnit) with begin
    introduce _ ==> _ with _. begin
      assert (qUnit ∋ ((), EUnit));
      lem_values_are_expressions qUnit () EUnit
    end
  end

let equiv_true g
  : Lemma ((fun (_:eval_env g) -> true) `equiv qBool` ETrue)
  =
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==>  qBool ⦂ (true, gsubst s ETrue) with begin
    introduce _ ==> _ with _. begin
      assert (qBool ∋ (true, ETrue));
      lem_values_are_expressions qBool true ETrue
    end
  end

let equiv_false g
  : Lemma ((fun (_:eval_env g) -> false) `equiv qBool` EFalse)
  =
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==>  qBool ⦂ (false, gsubst s EFalse) with begin
    introduce _ ==> _ with _. begin
      assert (qBool ∋ (false, EFalse));
      lem_values_are_expressions qBool false EFalse
    end
  end

let equiv_string g (str:string)
  : Lemma ((fun (_:eval_env g) -> str) `equiv qString` EString str)
  =
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==>  qString ⦂ (str, gsubst s (EString str)) with begin
    introduce _ ==> _ with _. begin
      assert (qString ∋ (str, EString str));
      lem_values_are_expressions qString str (EString str)
    end
  end

(** Used in compilation **)
let equiv_var0 (g:typ_env) (t:qType)
  : Lemma ((fun (fsG:eval_env (extend t g)) -> hd fsG) ≈ EVar 0)
  =
  introduce forall b (s:gsub (extend t g) b) fsG. fsG ∽ s ==>  t ⦂ (hd fsG, gsubst s (EVar 0)) with begin
    introduce _ ==> _ with _. begin
      index_0_hd fsG;
      assert (t ∋ (hd fsG, s 0));
      lem_values_are_expressions t (hd fsG) (s 0)
    end
  end

(** Used in compilation **)
let equiv_varS (#g:typ_env) #a #t (s:fs_oval g a) (e:exp)
  : Lemma
      (requires (equiv #g a s e))
      (ensures (equiv #(extend t g) a (fun fsG -> s (tail fsG)) (subst sub_inc e)))
  = admit ()

(** Used in the back-translation **)
let equiv_var g (x:var{Some? (g x)})
  : Lemma ((fun (fsG:eval_env g) -> index fsG x) ≈ EVar x)
  =
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==>  Some?.v (g x) ⦂ (index fsG x, gsubst s (EVar x)) with begin
    introduce _ ==> _ with _. begin
      assert (Some?.v (g x) ∋ (index fsG x, s x));
      lem_values_are_expressions (Some?.v (g x)) (index fsG x) (s x)
    end
  end

let equiv_lam #g (#t1:qType) (#t2:qType) (fs_body:fs_oval (extend t1 g) t2) (body:exp) : Lemma
  (requires fs_body ≈ body)
  (ensures (fun fsG x -> fs_body (stack fsG x)) `equiv (t1 ^-> t2)` (ELam body)) =
  lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  let f : fs_oval g (t1 ^-> t2) = fun fsG x -> fs_body (stack fsG x) in
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==>  (t1 ^-> t2) ⦂ (f fsG, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:fs_val t1). t1 ∋ (fs_v, v) ==>  t2 ⦂ (f fsG fs_v, subst_beta v body') with begin
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


#push-options "--z3rlimit 5000 --fuel 5000"
let equiv_app #g
  (#t1:qType) (#t2:qType)
  (fs_e1:fs_oval g (t1 ^-> t2)) (fs_e2:fs_oval g t1)
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
            safety t1 fs_e2 e2;
            let t1_typ = type_quotation_to_typ (get_rel t1) in
            let t2_typ = type_quotation_to_typ (get_rel t2) in
            let (e11, e2') = destruct_steps_eapp e1 e2 e' steps_e_e' t1_typ t2_typ in
            assume ((t1 ^-> t2) ∋ (fs_e1, ELam e11)); (** TODO/Cezar: this was working before the refactoring **)
            introduce True ==>  t1 ∋ (fs_e2, e2') with _. begin
              assert (t1 ⦂ (fs_e2, e2));
              assert (steps e2 e2');
              assert (irred e2')
            end;
            eliminate forall (v:value) (fs_v:fs_val t1). t1 ∋ (fs_v, v) ==>
              t2 ⦂ (fs_e1 fs_v, subst_beta v e11)
            with e2' fs_e2;
            assert (t2 ⦂ (fs_e, subst_beta e2' e11));
            assert (t2 ∋ (fs_e, e'))
          )
        end
      end
    end
  end

let equiv_if #g (#t:qType) (fs_e1:fs_oval g qBool) (fs_e2:fs_oval g t) (fs_e3:fs_oval g t) (e1:exp) (e2:exp) (e3:exp) : Lemma
  (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2 /\ fs_e3 ≈ e3)
  (ensures (fun fsG -> if fs_e1 fsG then fs_e2 fsG else fs_e3 fsG) ≈ EIf e1 e2 e3) =
  lem_fv_in_env_if g e1 e2 e3;
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==> t ⦂ ((if fs_e1 fsG then fs_e2 fsG else fs_e3 fsG), gsubst s (EIf e1 e2 e3)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e = if fs_e1 then fs_e2 fsG else fs_e3 fsG in
    let e = EIf (gsubst s e1) (gsubst s e2) (gsubst s e3) in
    assert (gsubst s (EIf e1 e2 e3) == e);
    let EIf e1 e2 e3 = e in
    introduce fsG ∽ s ==> t ⦂ (fs_e, e) with _. begin
      introduce forall (e':closed_exp). steps e e' /\ irred e' ==> t ∋ (fs_e, e') with begin
        introduce _ ==> t ∋ (fs_e, e') with h. begin
          let steps_e_e' : squash (steps e e') = () in
          FStar.Squash.map_squash #_ #(squash (t ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            safety qBool fs_e1 e1;
            safety t (fs_e2 fsG) e2;
            safety t (fs_e3 fsG) e3;
            let e1' = destruct_steps_eif e1 e2 e3 e' steps_e_e' in
            assert (qBool ∋ (fs_e1, e1'));
            assert (ETrue? e1' ==> (t ∋ (fs_e2 fsG, e')));
            assert (EFalse? e1' ==> (t ∋ (fs_e3 fsG, e')));
            assert (t ∋ (fs_e, e'))
          )
        end
      end
    end
  end
#pop-options

let equiv_pair #g (#t1 #t2:qType) (fs_e1:fs_oval g t1) (fs_e2:fs_oval g t2) (e1:exp) (e2:exp) : Lemma
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
            safety t1 fs_e1 e1;
            safety t2 fs_e2 e2;
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

let equiv_pair_fst_app #g (#t1 #t2:qType) (fs_e12:fs_oval g (t1 ^* t2)) (e12:exp) : Lemma
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
            safety (t1 ^* t2) fs_e12 e12;
            let t1_typ = type_quotation_to_typ (get_rel t1) in
            let t2_typ = type_quotation_to_typ (get_rel t2) in
            let e12' = destruct_steps_epair_fst e12 e' steps_e_e' t1_typ t2_typ in
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

let equiv_pair_snd_app #g (#t1 #t2:qType) (fs_e12:fs_oval g (t1 ^* t2)) (e12:exp)
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
            safety (t1 ^* t2) fs_e12 e12;
            let t1_typ = type_quotation_to_typ (get_rel t1) in
            let t2_typ = type_quotation_to_typ (get_rel t2) in
            let e12' = destruct_steps_epair_snd e12 e' steps_e_e' t1_typ t2_typ in
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

let equiv_inl #g (#t1 t2:qType) (fs_e:fs_oval g t1) (e:exp) : Lemma
  (requires fs_e ≈ e)
  (ensures (fun fsG -> Inl (fs_e fsG)) `equiv (t1 ^+ t2)` (EInl e)) =
  admit ()

let equiv_inr #g (t1 #t2:qType) (fs_e:fs_oval g t2) (e:exp) : Lemma
  (requires fs_e ≈ e)
  (ensures (fun fsG -> Inr (fs_e fsG)) `equiv (t1 ^+ t2)` (EInr e)) =
  admit ()

let equiv_case
  #g
  (#t1 #t2 #t3:qType)
  (fs_case:fs_oval g (t1 ^+ t2))
  (fs_lc:fs_oval (extend t1 g) t3)
  (fs_rc:fs_oval (extend t2 g) t3)
  (e_case e_lc e_rc:exp)
  : Lemma
    (requires fs_case ≈ e_case /\ fs_lc ≈ e_lc /\ fs_rc ≈ e_rc)
    (ensures (fun fsG -> match fs_case fsG with | Inl x -> fs_lc (stack fsG x) | Inr x -> fs_rc (stack fsG x)) `equiv t3` (ECase e_case e_lc e_rc))
  = admit ()
