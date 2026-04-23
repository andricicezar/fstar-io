module LogRelTargetSource.CompatibilityLemmas

open LambdaIO
open LambdaIO.DestructLemmas
open IOStar
open QTypes.Subst
open QTypes.OpenValComp
open QTypes.HelperTactics
open LogRelTargetSource

let bind_squash (a #b:Type) (f:a -> GTot (squash b)) : Pure (squash b) (requires a) (ensures fun _ -> True) =
  FStar.Squash.bind_squash #a () f

let get_squash = FStar.Squash.get_proof

let compat_oval_unit g : Lemma (fs_oval_return g #qUnit () ⊐ EUnit) =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qUnit ⊇ (h, (), gsubst s EUnit) with begin
    introduce _ ==> _ with _. begin
      assert (qUnit ∋ (h, (), EUnit));
      lem_values_are_expressions qUnit h () EUnit
    end
  end

let compat_oval_true g : Lemma (fs_oval_return g #qBool true ⊐ ETrue) =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qBool ⊇ (h, true, gsubst s ETrue) with begin
    introduce _ ==> _ with _. begin
      assert (qBool ∋ (h, true, ETrue));
      lem_values_are_expressions qBool h true ETrue
    end
  end

let compat_oval_false g : Lemma (fs_oval_return g #qBool false ⊐ EFalse) =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qBool ⊇ (h, false, gsubst s EFalse) with begin
    introduce _ ==> _ with _. begin
      assert (qBool ∋ (h, false, EFalse));
      lem_values_are_expressions qBool h false EFalse
    end
  end

let compat_oval_file_descr g fd : Lemma (fs_oval_return g #qFileDescr fd ⊐ EFileDescr fd) =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qFileDescr ⊇ (h, fd, gsubst s (EFileDescr fd)) with begin
    introduce _ ==> _ with _. begin
      assert (qFileDescr ∋ (h, fd, (EFileDescr fd)));
      lem_values_are_expressions qFileDescr h fd (EFileDescr fd)
    end
  end

let compat_oval_string g (str:string) : Lemma (fs_oval_return g #qString str ⊐ EString str) =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qString ⊇ (h, str, gsubst s (EString str)) with begin
    introduce _ ==> _ with _. begin
      assert (qString ∋ (h, str, EString str));
      lem_values_are_expressions qString h str (EString str)
    end
  end

#push-options "--z3rlimit 10"
let helper_compat_val_string_eq (e':closed_exp) (h:history) (lt:local_trace h) (fs_e1:fs_val qString) (fs_e2:fs_val qString) (e1 e2:closed_exp)
  : Lemma
    (requires e_beh (EStringEq e1 e2) e' h lt /\
              qString ⊇ (h, fs_e1, e1) /\
              (forall (lt:local_trace h). qString ⊇ (h++lt, fs_e2, e2)))
    (ensures (qBool ∋ (h, (fs_e1 = fs_e2), e') /\ lt == []))
  =
  lem_forall_values_are_values qString h fs_e1;
  assert (forall e1' lt1. e_beh e1 e1' h lt1 ==> is_value e1');
  bind_squash (steps (EStringEq e1 e2) e' h lt) (fun steps_e_e' ->
    let (e1', (| lt1, lt' |)) = destruct_steps_estringeq_e1 e1 e2 e' h lt steps_e_e' in
    lem_value_is_irred e1';
    assert (qString ∋ (h, fs_e1, e1') /\ lt1 == []);
    let EString s1 = e1' in
    lem_forall_values_are_values qString (h++lt1) fs_e2;
    assert (forall e2' lt2. e_beh e2 e2' (h++lt1) lt2 ==> is_value e2');
    bind_squash (steps (EStringEq e1' e2) e' (h++lt1) lt') (fun sts1 ->
      trans_history h lt1 lt';
      let (e2', (| lt2, lt'' |)) = destruct_steps_estringeq_e2 e1' e2 e' (h++lt1) lt' sts1 in
      lem_value_is_irred e2';
      assert (qString ∋ (h++lt1, fs_e2, e2') /\ lt2 == []);
      let EString s2 = e2' in
      (* Now: steps (EStringEq (EString s1) (EString s2)) e' ((h++lt1)++lt2) lt'' *)
      trans_history (h++lt1) lt2 lt'';
      bind_squash (steps (EStringEq (EString s1) (EString s2)) e' ((h++lt1)++lt2) lt'') (fun sts2 ->
        match sts2 with
        | SRefl _ _ ->
          (* EStringEq (EString s1) (EString s2) is not irred: StringEqReturn applies *)
          let _ : step (EStringEq (EString s1) (EString s2)) (if s1 = s2 then ETrue else EFalse) ((h++lt1)++lt2) None = StringEqReturn s1 s2 ((h++lt1)++lt2) in
          false_elim ()
        | STrans step_seq step_rest ->
          match step_seq with
          | StringEqReturn _ _ _ ->
            lem_value_is_irred (if s1 = s2 then ETrue else EFalse);
            lem_irred_implies_srefl_steps step_rest;
            get_squash (qBool ∋ (h, (fs_e1 = fs_e2), e') /\ lt == [])
          | StringEqLeft _ step_e1 ->
            lem_value_is_irred (EString s1);
            false_elim ()
          | StringEqRight _ step_e2 ->
            lem_value_is_irred (EString s2);
            false_elim ()
      )))
#pop-options

let compat_oval_string_eq #g #preS1 #preS2
  (fs_e1:fs_oval g qString preS1) (fs_e2:fs_oval g qString preS2)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊐ e1 /\ fs_e2 ⊐ e2)
    (ensures fs_oval_eq_string fs_e1 fs_e2 ⊐ EStringEq e1 e2) =
  lem_fv_in_env_string_eq g e1 e2;
  introduce forall b (s:gsub g b) fsG h. (fsG `(∽) h` s /\ (spec_env_app preS1 preS2) fsG) ==> qBool ⊇ (h, (fs_e1 fsG = fs_e2 fsG), gsubst s (EStringEq e1 e2)) with begin
    let preS1 = preS1 fsG in
    let preS2 = preS2 fsG in
    let pre = (preS1 /\ preS2) in
    let e = EStringEq (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EStringEq e1 e2) == e);
    let EStringEq e1 e2 = e in
    introduce (fsG `(∽) h` s /\ pre) ==> qBool ⊇ (h, (fs_e1 fsG = fs_e2 fsG), e) with _. begin
      introduce forall (e':closed_exp) lt. e_beh e e' h lt ==> (qBool ∋ (h, (fs_e1 fsG = fs_e2 fsG), e') /\ lt == []) with begin
        introduce e_beh e e' h lt ==> (qBool ∋ (h, (fs_e1 fsG = fs_e2 fsG), e') /\ lt == []) with _. begin
          lem_shift_type_value_environments h fsG s;
          helper_compat_val_string_eq e' h lt (fs_e1 fsG) (fs_e2 fsG) e1 e2
        end
      end
    end
  end

(** Used in backtranslation **)
let compat_oval_var g (x:var{Some? (g x)}) : Lemma (fs_oval_var g x ⊐ EVar x) =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> Some?.v (g x) ⊇ (h, index fsG x, gsubst s (EVar x)) with begin
    introduce _ ==> _ with _. begin
      assert (Some?.v (g x) ∋ (h, index fsG x, s x));
      lem_values_are_expressions (Some?.v (g x)) h (index fsG x) (s x)
    end
  end

(** Used in compilation **)
let compat_oval_axiom (g:typ_env) (t:qType) : Lemma (fs_oval_axiom g t ⊐ EVar 0) =
  introduce forall b (s:gsub (extend t g) b) fsG h. fsG `(∽) h` s ==>  t ⊇ (h, hd fsG, gsubst s (EVar 0)) with begin
    introduce _ ==> _ with _. begin
      lem_index_0_hd fsG;
      assert (t ∋ (h, hd fsG, s 0));
      lem_values_are_expressions t h (hd fsG) (s 0)
    end
  end

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
 (** Used in compilation **)
let compat_weaken (#g:typ_env) #a #t #pre (s:fs_oval g a pre) (e:exp)
  : Lemma
      (requires (s ⊐ e))
      (ensures (fs_oval_weaken t s ⊐ subst sub_inc e))
  =
  lem_fv_in_env_weaken g t e;
  introduce forall b (s':gsub (extend t g) b) (fsG:eval_env (extend t g)) (h:history). (fsG `(∽) h` s' /\ (spec_env_weaken pre) fsG) ==> a ⊇ (h, s (tail fsG), gsubst s' (subst sub_inc e)) with begin
    introduce (fsG `(∽) h` s' /\ (spec_env_weaken pre) fsG) ==> a ⊇ (h, s (tail fsG), gsubst s' (subst sub_inc e)) with _. begin
      lem_index_tail fsG;
      let f : var -> exp = fun (y:var) -> s' (y+1) in
      introduce (forall (x:var{x>0}). EVar? (s' x)) ==> a ⊇ (h, s (tail fsG), gsubst s' (subst sub_inc e)) with _. begin
        eliminate forall b_ (s_:gsub g b_) (fsG_:eval_env g) (h_:history). (fsG_ `(∽) h_` s_ /\ pre fsG_) ==> a ⊇ (h_, s fsG_, gsubst s_ e) with true f (tail fsG) h;
        shift_sub_equiv_sub_inc_rename #t s' e f
      end;
      introduce (~(forall (x:var{x>0}). EVar? (s' x))) ==> ((spec_env_weaken pre) fsG /\ a ⊇ (h, s (tail fsG), gsubst s' (subst sub_inc e))) with _. begin
        eliminate forall b_ (s_:gsub g b_) (fsG_:eval_env g) (h_:history). (fsG_ `(∽) h_` s_ /\ pre fsG_) ==> a ⊇ (h_, s fsG_, gsubst s_ e) with false f (tail fsG) h;
        shift_sub_equiv_sub_inc_no_rename #t #g s' e f
      end
    end
  end
#pop-options

let compat_oval_lambda #g (#t1:qType) (#preBody:spec_env (extend t1 g)) (#t2:qType) (fs_body:fs_oval (extend t1 g) t2 preBody) (body:exp) : Lemma
  (requires fs_body ⊐ body)
  (ensures (fs_oval_lambda fs_body ⊐ ELam body)) =
  lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  let f : fs_oval g (t1 ^-> t2) (spec_env_lambda_tot preBody) = fun fsG x -> fs_body (stack fsG x) in
  introduce forall b (s:gsub g b) fsG h. (fsG `(∽) h` s /\ (spec_env_lambda_tot preBody) fsG) ==> (t1 ^-> t2) ⊇ (h, f fsG, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∋ (h++lt_v, fs_v, v) ==> t2 ⊇ (h++lt_v, f fsG fs_v, subst_beta v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fsG' = stack fsG fs_v in
          let h' = h++lt_v in
          let f' () : Pure (fs_val (t1 ^-> t2)) (requires ((spec_env_lambda_tot preBody) fsG)) (ensures (fun _ -> True)) = f (tail #t1 fsG') in
          let f' : fs_val t2 = f' () (hd #t1 #g fsG') in
          assert ((fsG' `(∽) h'` s' /\ preBody fsG') ==> t2 ⊇ (h', f', gsubst s' body));
          assert (fsG `(∽) h` s);
          assert ((spec_env_lambda_tot preBody) fsG);
          assert (t1 ∋ (h++lt_v, fs_v, v));
          introduce forall (x:var). Some? (g x) ==> Some?.v (g x) ∋ (h++lt_v, index fsG x, s x) with begin
            introduce _ ==> _ with _. begin
              val_type_closed_under_history_extension (Some?.v (g x)) h (index fsG x) (s x)
            end
          end;
          assert (stack fsG fs_v `(∽) h'` gsub_extend s t1 v);
          assert (preBody fsG');
          assert (t2 ⊇ (h', f', (gsubst s' body)));
          assert (hd (stack fsG fs_v) == fs_v);
          assert (t2 ⊇ (h', f (tail fsG') fs_v, gsubst s' body));
          assert (t2 ⊇ (h', f fsG fs_v, (gsubst s' body)));
          lem_substitution s t1 v body;
          assert (t2 ⊇ (h', f fsG fs_v, subst_beta v body'))
        end
      end;
      assert ((t1 ^-> t2) ∋ (h, f fsG, gsubst s (ELam body)));
      lem_values_are_expressions (t1 ^-> t2) h (f fsG) (gsubst s (ELam body));
      assert ((t1 ^-> t2) ⊇ (h, f fsG, gsubst s (ELam body)))
    end
  end

let helper_compat_oval_app (e':closed_exp) (h:history) (lt:local_trace h) (t1 t2:qType) (fs_e1:fs_val (t1 ^-> t2)) (fs_e2:fs_val t1) (e1 e2:closed_exp) :
  Lemma
    (requires e_beh (EApp e1 e2) e' h lt /\
              (t1 ^-> t2) ⊇ (h, fs_e1, e1) /\
              (forall (lt:local_trace h). t1 ⊇ (h++lt, fs_e2, e2)))
    (ensures (t2 ∋ (h, fs_e1 fs_e2, e') /\ lt == [])) =
  assert (forall e1' lt1. e_beh e1 e1' h lt1 ==> (ELam? e1' /\ is_closed e1'));
  FStar.Squash.bind_squash #(steps (EApp e1 e2) e' h lt) () (fun sts1 ->
    let t1_typ = type_quotation_to_typ (get_rel t1) in
    let t2_typ = type_quotation_to_typ (get_rel t2) in
    let (e11, (| lt1, lt' |)) = destruct_steps_eapp_e1 e1 e2 e' h lt sts1 t1_typ t2_typ in
    lem_forall_values_are_values t1 (h++lt1) fs_e2;
    assert (forall e2' (lt2:local_trace (h++lt1)). e_beh e2 e2' (h++lt1) lt2 ==> is_value e2');
    bind_squash (steps (EApp (ELam e11) e2) e' (h++lt1) lt') (fun sts2 ->
      trans_history h lt1 lt';
      let (e2', (| lt2, lt'' |)) = destruct_steps_eapp_e2 e11 e2 e' (h++lt1) lt' sts2 in
      eliminate forall e1' lt1. e_beh e1 e1' h lt1 ==> ((t1 ^-> t2) ∋ (h, fs_e1, e1') /\ lt1 == []) with (ELam e11) lt1;
      lem_value_is_irred (ELam e11);
      eliminate forall e2' lt2. e_beh e2 e2' (h++lt1) lt2 ==> (t1 ∋ (h++lt1, fs_e2, e2') /\ lt2 == []) with e2' lt2;
      lem_value_is_irred e2';
      unfold_contains_arrow t1 t2 h fs_e1 e11;
      assert (t2 ⊇ (h, fs_e1 fs_e2, subst_beta e2' e11));
      assert (t2 ∋ (h, fs_e1 fs_e2, e'));
      get_squash (t2 ∋ (h, fs_e1 fs_e2, e') /\ lt == [])
    )
  )

let compat_oval_app #g #preS1 #preS2
  (#t1:qType) (#t2:qType)
  (fs_e1:fs_oval g (t1 ^-> t2) preS1) (fs_e2:fs_oval g t1 preS2)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊐ e1 /\ fs_e2 ⊐ e2)
    (ensures fs_oval_app fs_e1 fs_e2 ⊐ EApp e1 e2) =
  lem_fv_in_env_app g e1 e2;
  introduce forall b (s:gsub g b) fsG h. (fsG `(∽) h` s /\ (spec_env_app preS1 preS2) fsG) ==> t2 ⊇ (h, (fs_e1 fsG) (fs_e2 fsG), gsubst s (EApp e1 e2)) with begin
    let preS1 = preS1 fsG in
    let preS2 = preS2 fsG in
    let pre = (preS1 /\ preS2) in
    let fs_e1 () : Pure (fs_val (t1 ^-> t2)) (requires preS1) (ensures (fun _ -> True)) = fs_e1 fsG in
    let fs_e2 () : Pure (fs_val t1) (requires preS2) (ensures (fun _ -> True)) = fs_e2 fsG in
    let fs_e () : Pure (fs_val t2) (requires pre) (ensures (fun _ -> True)) = (fs_e1 ()) (fs_e2 ()) in
    let e = EApp (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EApp e1 e2) == e);
    let EApp e1 e2 = e in
    introduce (fsG `(∽) h` s /\ pre) ==> t2 ⊇ (h, fs_e (), e) with _. begin
      introduce forall (e':closed_exp) lt. e_beh e e' h lt ==> (t2 ∋ (h, fs_e (), e') /\ lt == []) with begin
        introduce e_beh e e' h lt ==> (t2 ∋ (h, fs_e (), e') /\ lt == []) with _. begin
          lem_shift_type_value_environments h fsG s;
          helper_compat_oval_app e' h lt t1 t2 (fs_e1 ()) (fs_e2 ()) e1 e2
        end
      end
    end
  end

let helper_compat_val_if (e':closed_exp) (#h:history) (lt:local_trace h) (t:qType) (fs_e1:fs_val qBool) (fs_e:fs_val t) (e1:closed_exp) (e2:closed_exp) (e3:closed_exp)  :
  Lemma
    (requires (steps (EIf e1 e2 e3) e' h lt) /\
              (indexed_irred e' (h++lt)) /\
              (qBool ⊇ (h, fs_e1, e1)) /\
              (if fs_e1 then t ⊇ (h, fs_e, e2) else t ⊇ (h, fs_e, e3)))
    (ensures (t ∋ (h, fs_e, e') /\ lt == [])) =
  assert (forall e1' lt1. e_beh e1 e1' h lt1 ==> (ETrue? e1' \/ EFalse? e1'));
  bind_squash (steps (EIf e1 e2 e3) e' h lt) (fun sts ->
    let (e1', (| lt1, lt2 |)) = destruct_steps_eif e1 e2 e3 e' h lt sts in
    assert (qBool ∋ (h, fs_e1, e1') /\ lt1 == []);
    assert (t ∋ (h, fs_e, e') /\ lt2 == []);
    get_squash (t ∋ (h, fs_e, e') /\ lt == []))

let compat_oval_if #g
  (#t:qType) #preC #preT #preE
  (fs_e1:fs_oval g qBool preC) (fs_e2:fs_oval g t preT) (fs_e3:fs_oval g t preE)
  (e1:exp) (e2:exp) (e3:exp)
  : Lemma
    (requires fs_e1 ⊐ e1 /\ fs_e2 ⊐ e2 /\ fs_e3 ⊐ e3)
    (ensures fs_oval_if fs_e1 fs_e2 fs_e3 ⊐ EIf e1 e2 e3) =
  lem_fv_in_env_if g e1 e2 e3;
  introduce forall b (s:gsub g b) fsG h. (fsG `(∽) h` s /\ (spec_env_if fs_e1 preT preE) fsG) ==> t ⊇ (h, (if fs_e1 fsG then fs_e2 fsG else fs_e3 fsG), gsubst s (EIf e1 e2 e3)) with begin
    let e = EIf (gsubst s e1) (gsubst s e2) (gsubst s e3) in
    assert (gsubst s (EIf e1 e2 e3) == e);
    let EIf e1 e2 e3 = e in
    introduce (fsG `(∽) h` s /\ (spec_env_if fs_e1 preT preE) fsG) ==> t ⊇ (h, (if fs_e1 fsG then fs_e2 fsG else fs_e3 fsG), e) with _. begin
      let fs_e1 = fs_e1 fsG in
      let fs_e = if fs_e1 then fs_e2 fsG else fs_e3 fsG in
      introduce forall (e':closed_exp) lt. e_beh e e' h lt ==> (t ∋ (h, fs_e, e') /\ lt == []) with begin
        introduce e_beh e e' h lt ==> (t ∋ (h, fs_e, e') /\ lt == []) with _. begin
          assert (qBool ⊇ (h, fs_e1, e1));
          assert (if fs_e1 then t ⊇ (h, fs_e, e2) else t ⊇ (h, fs_e, e3));
          helper_compat_val_if e' lt t fs_e1 fs_e e1 e2 e3
        end
      end
    end
  end

let helper_compat_oval_pair (e':closed_exp) (h:history) (lt:local_trace h) (t1 t2:qType) (fs_e1:fs_val t1) (fs_e2:fs_val t2) (e1 e2:closed_exp)
  : Lemma
    (requires e_beh (EPair e1 e2) e' h lt /\
              t1 ⊇ (h, fs_e1, e1) /\
              (forall (lt:local_trace h). t2 ⊇ (h++lt, fs_e2, e2)))
    (ensures ((t1 ^* t2) ∋ (h, fs_val_pair fs_e1 fs_e2, e') /\ lt == [])) =
  lem_forall_values_are_values t1 h fs_e1;
  assert (forall e1' lt1. e_beh e1 e1' h lt1 ==> is_value e1');
  bind_squash (steps (EPair e1 e2) e' h lt) (fun steps_e_e' ->
    let (e1', (| lt1, lt' |)) = destruct_steps_epair_e1 e1 e2 e' h lt steps_e_e' in
    lem_forall_values_are_values t2 (h++lt1) fs_e2;
    assert (forall e2' lt2. e_beh e2 e2' (h++lt1) lt2 ==> is_value e2');
    bind_squash (steps (EPair e1' e2) e' (h++lt1) lt') (fun sts1 ->
      trans_history h lt1 lt';
      let (e2', (| lt2, lt'' |)) = destruct_steps_epair_e2 e1' e2 e' (h++lt1) lt' sts1 in
      lem_value_is_irred e1';
      lem_value_is_irred e2';
      assert (t1 ∋ (h, fs_e1, e1'));
      assert (t2 ∋ (h, fs_e2, e2'));
      assert ((t1 ^* t2) ∋ (h, fs_val_pair fs_e1 fs_e2, EPair e1' e2'));
      lem_values_are_expressions (t1 ^* t2) h (fs_val_pair fs_e1 fs_e2) (EPair e1' e2');
      get_squash ((t1 ^* t2) ∋ (h, fs_val_pair fs_e1 fs_e2, e') /\ lt == [])))

let compat_oval_pair #g #preX #preY
  (#t1 #t2:qType)
  (fs_e1:fs_oval g t1 preX) (fs_e2:fs_oval g t2 preY)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊐ e1 /\ fs_e2 ⊐ e2)
    (ensures fs_oval_pair fs_e1 fs_e2 ⊐ EPair e1 e2) =
  lem_fv_in_env_pair g e1 e2;
  let t = t1 ^* t2 in
  introduce forall b (s:gsub g b) fsG h. (fsG `(∽) h` s /\ (spec_env_app preX preY) fsG) ==>  t ⊇ (h, (fs_e1 fsG, fs_e2 fsG), gsubst s (EPair e1 e2)) with begin
    let preX = preX fsG in
    let preY = preY fsG in
    let pre = (preX /\ preY) in
    let fs_e1 () : Pure (fs_val t1) (requires preX) (ensures (fun _ -> True)) = fs_e1 fsG in
    let fs_e2 () : Pure (fs_val t2) (requires preY) (ensures (fun _ -> True)) = fs_e2 fsG in
    let fs_e () : Pure (fs_val (t1 ^* t2)) (requires pre) (ensures (fun _ -> True)) = (fs_e1 (), fs_e2()) in
    let e = EPair (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EPair e1 e2) == e);
    let EPair e1 e2 = e in
    introduce (fsG `(∽) h` s /\ pre) ==>  t ⊇ (h, fs_e (), e) with _. begin
      introduce forall (e':closed_exp) lt. e_beh e e' h lt ==> (t ∋ (h, fs_e (), e') /\ lt == []) with begin
        introduce _ ==> (t ∋ (h, fs_e (), e') /\ lt == []) with _. begin
          lem_shift_type_value_environments h fsG s;
          helper_compat_oval_pair e' h lt t1 t2 (fs_e1 ()) (fs_e2 ()) e1 e2
        end
      end
    end
  end

let helper_compat_oval_pair_fst
  (e':closed_exp) (h:history) (lt:local_trace h) (t1 t2:qType) (fs_e12:fs_val (t1 ^* t2)) (e12:closed_exp) :
  Lemma
    (requires e_beh (EFst e12) e' h lt /\
              (t1 ^* t2) ⊇ (h, fs_e12, e12))
    (ensures (t1 ∋ (h, fst fs_e12, e') /\ lt == [])) =
  lem_forall_values_are_values (t1 ^* t2) h fs_e12;
  assert (forall e12' lt12. e_beh e12 e12' h lt12 ==> (EPair? e12' /\ is_value e12'));
  bind_squash (steps (EFst e12) e' h lt) (fun steps_e_e' ->
    let t1_typ = type_quotation_to_typ (get_rel t1) in
    let t2_typ = type_quotation_to_typ (get_rel t2) in
    let (e12', (| lt12, lt_f |)) = destruct_steps_epair_fst e12 e' h lt steps_e_e' t1_typ t2_typ in
    lem_value_is_irred e12';
    assert ((t1 ^* t2) ⊇ (h, fs_e12, e12));
    eliminate forall e12' lt12. e_beh e12 e12' h lt12 ==> ((t1 ^* t2) ∋ (h, fs_e12, e12') /\ lt12 == []) with e12' lt12;
    assert ((t1 ^* t2) ∋ (h, fs_e12, e12') /\ lt12 == []);
    let EPair e1' e2' = e12' in
    lem_value_is_irred e1';
    lem_value_is_irred e2';
    assert (t1 ∋ (h, fst fs_e12, e1'));
    lem_destruct_steps_epair_fst e1' e2' e' h lt_f;
    assert (t1 ∋ (h, fst fs_e12, e'));
    get_squash (t1 ∋ (h, fst fs_e12, e') /\ lt == []))

let compat_oval_pair_fst #g
  (#t1 #t2:qType) #pre
  (fs_e12:fs_oval g (t1 ^* t2) pre)
  (e12:exp)
  : Lemma
    (requires fs_e12 ⊐ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures fs_oval_fmap fs_e12 fst ⊐ (EFst e12)) =
  lem_fv_in_env_fst g e12;
  introduce forall b (s:gsub g b) fsG h. (fsG `(∽) h` s /\ pre fsG) ==>  t1 ⊇ (h, fst (fs_e12 fsG), gsubst s (EFst e12)) with begin
    let e = EFst (gsubst s e12) in
    assert (gsubst s (EFst e12) == e);
    let EFst e12 = e in
    introduce (fsG `(∽) h` s /\ pre fsG) ==> t1 ⊇ (h, fst (fs_e12 fsG), e) with _. begin
      let fs_e12 = fs_e12 fsG in
      let fs_e = fst fs_e12 in
      introduce forall (e':closed_exp) lt. e_beh e e' h lt ==> (t1 ∋ (h, fs_e, e') /\ lt == []) with begin
        introduce e_beh e e' h lt ==> (t1 ∋ (h, fs_e, e') /\ lt == []) with _. begin
          helper_compat_oval_pair_fst e' h lt t1 t2 fs_e12 e12
        end
      end
    end
  end

let helper_compat_oval_pair_snd (e':closed_exp) (h:history) (lt:local_trace h) (t1 t2:qType) (fs_e12:fs_val (t1 ^* t2)) (e12:closed_exp) :
  Lemma
    (requires e_beh (ESnd e12) e' h lt /\
              (t1 ^* t2) ⊇ (h, fs_e12, e12))
    (ensures  t2 ∋ (h, snd fs_e12, e') /\ lt == []) =
  lem_forall_values_are_values (t1 ^* t2) h fs_e12;
  assert (forall e12' lt12. e_beh e12 e12' h lt12 ==> (EPair? e12' /\ is_value e12'));
  bind_squash (steps (ESnd e12) e' h lt) (fun steps_e_e' ->
    let t1_typ = type_quotation_to_typ (get_rel t1) in
    let t2_typ = type_quotation_to_typ (get_rel t2) in
    let (e12', (| lt12, lt_f |)) = destruct_steps_epair_snd e12 e' h lt steps_e_e' t1_typ t2_typ in
    lem_value_is_irred e12';
    assert ((t1 ^* t2) ⊇ (h, fs_e12, e12));
    eliminate forall e12' lt12. e_beh e12 e12' h lt12 ==> ((t1 ^* t2) ∋ (h, fs_e12, e12') /\ lt12 == []) with e12' lt12;
    assert ((t1 ^* t2) ∋ (h, fs_e12, e12') /\ lt12 == []);
    let EPair e1' e2' = e12' in
    lem_value_is_irred e1';
    lem_value_is_irred e2';
    assert (t2 ∋ (h, snd fs_e12, e2'));
    lem_destruct_steps_epair_snd e1' e2' e' h lt_f;
    assert (t2 ∋ (h, snd fs_e12, e'));
    get_squash (t2 ∋ (h, snd fs_e12, e') /\ lt == []))

let compat_oval_pair_snd #g (#t1 #t2:qType) #pre (fs_e12:fs_oval g (t1 ^* t2) pre) (e12:exp)
  : Lemma
    (requires fs_e12 ⊐ e12)
    (ensures fs_oval_fmap fs_e12 snd ⊐ (ESnd e12)) =
  lem_fv_in_env_snd g e12;
  introduce forall b (s:gsub g b) fsG h. (fsG `(∽) h` s /\ pre fsG) ==> t2 ⊇ (h, snd (fs_e12 fsG), gsubst s (ESnd e12)) with begin
    let e = ESnd (gsubst s e12) in
    assert (gsubst s (ESnd e12) == e);
    let ESnd e12 = e in
    introduce (fsG `(∽) h` s /\ pre fsG) ==> t2 ⊇ (h, snd (fs_e12 fsG), e) with _. begin
      let fs_e12 = fs_e12 fsG in
      let fs_e = snd fs_e12 in
      introduce forall (e':closed_exp) lt. e_beh e e' h lt ==> (t2 ∋ (h, fs_e, e') /\ lt == []) with begin
        introduce e_beh e e' h lt ==> (t2 ∋ (h, fs_e, e') /\ lt == []) with _. begin
        helper_compat_oval_pair_snd e' h lt t1 t2 fs_e12 e12
        end
      end
    end
  end

let helper_compat_oval_inl (ex':closed_exp) (h:history) (lt:local_trace h) (t1 t2:qType) (fs_e:fs_val t1) (e:closed_exp) :
  Lemma
    (requires e_beh (EInl e) ex' h lt /\ t1 ⊇ (h, fs_e, e))
    (ensures (t1 ^+ t2) ∋ (h, Inl #(fs_val t1) #(fs_val t2) fs_e, ex') /\ lt == []) =
  lem_forall_values_are_values t1 h fs_e;
  assert (forall e' lt'. e_beh e e' h lt' ==> is_value e');
  bind_squash (steps (EInl e) ex' h lt) (fun steps_e_e' ->
    let (e', (| lt12, lt_f |)) = destruct_steps_einl e ex' h lt steps_e_e' in
    lem_value_is_irred e';
    lem_value_is_irred (EInl e');
    assert (t1 ∋ (h, fs_e, e') /\ lt12 == []);
    lem_destruct_steps_einl e' ex' h lt_f;
    assert ((t1 ^+ t2) ∋ (h, Inl #(fs_val t1) #(fs_val t2) fs_e, ex'));
    get_squash ((t1 ^+ t2) ∋ (h, Inl #(fs_val t1) #(fs_val t2) fs_e, ex') /\ lt == []))

let compat_oval_inl #g (#t1 t2:qType) #pre (fs_e:fs_oval g t1 pre) (e:exp) : Lemma
  (requires fs_e ⊐ e)
  (ensures fs_oval_fmap #g #t1 #(t1 ^+ t2) fs_e Inl ⊐ (EInl e)) =
  lem_fv_in_env_inl g e;
  let t = t1 ^+ t2 in
  introduce forall b (s:gsub g b) fsG h. (fsG `(∽) h` s /\ pre fsG) ==> (t1 ^+ t2) ⊇ (h, Inl (fs_e fsG), gsubst s (EInl e)) with begin
    let ex = EInl (gsubst s e) in
    assert (gsubst s (EInl e) == ex);
    let EInl e = ex in
    introduce (fsG `(∽) h` s /\ pre fsG) ==> t ⊇ (h, Inl #(fs_val t1) #(fs_val t2) (fs_e fsG), ex) with _. begin
      let fs_e = fs_e fsG in
      let fs_ex = Inl #(fs_val t1) #(fs_val t2) fs_e in
      introduce forall (ex':closed_exp) lt. e_beh ex ex' h lt ==> (t ∋ (h, fs_ex, ex') /\ lt == []) with begin
        introduce _ ==> (t ∋ (h, fs_ex, ex') /\ lt == []) with _. begin
        helper_compat_oval_inl ex' h lt t1 t2 fs_e e
        end
      end
    end
  end

let helper_compat_oval_inr (ex':closed_exp) (h:history) (lt:local_trace h) (t1 t2:qType) (fs_e:fs_val t2) (e:closed_exp) :
  Lemma
    (requires (e_beh (EInr e) ex' h lt /\ t2 ⊇ (h, fs_e, e)))
    (ensures  (t1 ^+ t2) ∋ (h, Inr #(fs_val t1) #(fs_val t2) fs_e, ex') /\ lt == []) =
  lem_forall_values_are_values t2 h fs_e;
  assert (forall e' lt'. e_beh e e' h lt' ==> is_value e');
  bind_squash (steps (EInr e) ex' h lt) (fun steps_e_e' ->
    let (e', (| lt12, lt_f |)) = destruct_steps_einr e ex' h lt steps_e_e' in
    lem_value_is_irred e';
    lem_value_is_irred (EInr e');
    assert (t2 ∋ (h, fs_e, e') /\ lt12 == []);
    lem_destruct_steps_einr e' ex' h lt_f;
    assert ((t1 ^+ t2) ∋ (h, Inr #(fs_val t1) #(fs_val t2) fs_e, ex'));
    get_squash ((t1 ^+ t2) ∋ (h, Inr #(fs_val t1) #(fs_val t2) fs_e, ex') /\ lt == []))

let compat_oval_inr #g (t1 #t2:qType) #pre (fs_e:fs_oval g t2 pre) (e:exp) : Lemma
  (requires fs_e ⊐ e)
  (ensures fs_oval_fmap #g #t2 #(t1 ^+ t2) fs_e Inr ⊐ (EInr e)) =
  lem_fv_in_env_inr g e;
  let t = t1 ^+ t2 in
  introduce forall b (s:gsub g b) fsG h. (fsG `(∽) h` s /\ pre fsG) ==> (t1 ^+ t2) ⊇ (h, Inr (fs_e fsG), gsubst s (EInr e)) with begin
    let ex = EInr (gsubst s e) in
    assert (gsubst s (EInr e) == ex);
    let EInr e = ex in
    introduce (fsG `(∽) h` s /\ pre fsG) ==> t ⊇ (h, Inr #(fs_val t1) #(fs_val t2) (fs_e fsG), ex) with _. begin
      let fs_e = fs_e fsG in
      let fs_ex = Inr #(fs_val t1) #(fs_val t2) fs_e in
      introduce forall (ex':closed_exp) lt. e_beh ex ex' h lt ==> (t ∋ (h, fs_ex, ex') /\ lt == []) with begin
        introduce _ ==> (t ∋ (h, fs_ex, ex') /\ lt == []) with _. begin
          helper_compat_oval_inr ex' h lt t1 t2 fs_e e
        end
      end
    end
  end

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let helper_compat_val_case (e':closed_exp)
  (#h:history) (lt:local_trace h)
  (#t1 #t2 #t3:qType)
  (fs_case:fs_val (t1 ^+ t2))
  (fs_r:fs_val t3)
  (e_case:closed_exp)
  (e_lc:exp{is_closed (ELam e_lc)})
  (e_rc:exp{is_closed (ELam e_rc)}) :
  Lemma
    (requires (
      steps (ECase e_case e_lc e_rc) e' h lt /\
      indexed_irred e' (h++lt) /\
      (t1 ^+ t2) ⊇ (h, fs_case, e_case) /\
      (Inl? fs_case ==> (forall (v:value). t1 ∋ (h, Inl?.v fs_case, v) ==> t3 ⊇ (h, fs_r, subst_beta v e_lc))) /\
      (Inr? fs_case ==> (forall (v:value). t2 ∋ (h, Inr?.v fs_case, v) ==> t3 ⊇ (h, fs_r, subst_beta v e_rc)))))
    (ensures t3 ∋ (h, fs_r, e') /\ lt == []) =
  lem_forall_values_are_values (t1 ^+ t2) h fs_case;
  introduce forall e_sc' lt'. e_beh e_case e_sc' h lt' ==> (EInl? e_sc' \/ EInr? e_sc') with begin
    introduce _ ==> _ with _. begin
      eliminate forall e_sc'' lt''. e_beh e_case e_sc'' h lt'' ==> ((t1 ^+ t2) ∋ (h, fs_case, e_sc'') /\ lt'' == []) with e_sc' lt';
      match fs_case, e_sc' with
      | Inl _, EInl _ -> ()
      | Inr _, EInr _ -> ()
      | _ -> false_elim ()
    end
  end;
  bind_squash (steps (ECase e_case e_lc e_rc) e' h lt) (fun sts ->
    let t1_typ = type_quotation_to_typ (get_rel t1) in
    let t2_typ = type_quotation_to_typ (get_rel t2) in
    let (e_sc', (| lt1, lt2 |)) = destruct_steps_ecase e_case e_lc e_rc e' h lt sts t1_typ t2_typ in
    eliminate forall e_sc'' lt'. e_beh e_case e_sc'' h lt' ==> ((t1 ^+ t2) ∋ (h, fs_case, e_sc'') /\ lt' == []) with e_sc' lt1;
    let res   = match e_sc' with | EInl _ -> e_lc | EInr _ -> e_rc in
    let res'  = match e_sc' with | EInl x -> x | EInr x -> x in
    let tres' = match e_sc' with | EInl _ -> t1 | EInr _ -> t2 in
    match fs_case, e_sc' with
    | Inl fs_x, EInl v -> begin
      assert (Inl? fs_case);
      assert (t1 ∋ (h, fs_x, v));
      eliminate forall (v':value). t1 ∋ (h, Inl?.v fs_case, v') ==> t3 ⊇ (h, fs_r, subst_beta v' e_lc) with v;
      assert (t3 ⊇ (h, fs_r, subst_beta v e_lc))
    end
    | Inr fs_x, EInr v -> begin
      assert (Inr? fs_case);
      assert (t2 ∋ (h, fs_x, v));
      eliminate forall (v':value). t2 ∋ (h, Inr?.v fs_case, v') ==> t3 ⊇ (h, fs_r, subst_beta v' e_rc) with v;
      assert (t3 ⊇ (h, fs_r, subst_beta v e_rc))
    end
    | _ -> false_elim ();
    assert (t3 ⊇ (h, fs_r, subst_beta res' res));
    get_squash (t3 ∋ (h, fs_r, e') /\ lt == []))
#pop-options

#push-options "--z3rlimit 10"
let compat_oval_case
  #g
  (#t1 #t2 #t3:qType)
  (#preCase:spec_env g)
  (#preLc:spec_env (extend t1 g))
  (#preRc:spec_env (extend t2 g))
  (fs_case:fs_oval g (t1 ^+ t2) preCase)
  (fs_lc:fs_oval (extend t1 g) t3 preLc)
  (fs_rc:fs_oval (extend t2 g) t3 preRc)
  (e_case e_lc e_rc:exp)
  : Lemma
    (requires fs_case ⊐ e_case /\ fs_lc ⊐ e_lc /\ fs_rc ⊐ e_rc)
    (ensures fs_oval_case fs_case fs_lc fs_rc ⊐ ECase e_case e_lc e_rc) =
  lem_fv_in_env_case g t1 t2 e_case e_lc e_rc;
  lem_fv_in_env_lam g t1 e_lc;
  lem_fv_in_env_lam g t2 e_rc;
  introduce forall b (s:gsub g b) fsG h.
    (fsG `(∽) h` s /\ (spec_env_case fs_case preLc preRc) fsG) ==> t3 ⊇ (h, fs_oval_case fs_case fs_lc fs_rc fsG, gsubst s (ECase e_case e_lc e_rc)) with begin
    let preCaseH = preCase fsG in
    let fs_case_v () : Pure (fs_val (t1 ^+ t2)) (requires preCaseH) (ensures (fun _ -> True)) = fs_case fsG in
    let fs_e () : Pure (fs_val t3)
      (requires (preCaseH /\
                  (Inl? (fs_case_v ()) ==> preLc (stack fsG (Inl?.v (fs_case_v ())))) /\
                  (Inr? (fs_case_v ()) ==> preRc (stack fsG (Inr?.v (fs_case_v ()))))))
      (ensures (fun _ -> True))
      = match fs_case_v () with
        | Inl x -> fs_lc (stack fsG x)
        | Inr x -> fs_rc (stack fsG x) in
    let e = ECase (gsubst s e_case) (subst (sub_elam s) e_lc) (subst (sub_elam s) e_rc) in
    assert (gsubst s (ECase e_case e_lc e_rc) == e);
    let ECase e_case_s e_lc_s e_rc_s = e in
    assert (e_lc_s == subst (sub_elam s) e_lc);
    assert (e_rc_s == subst (sub_elam s) e_rc);
    introduce (fsG `(∽) h` s /\ (spec_env_case fs_case preLc preRc) fsG) ==> t3 ⊇ (h, fs_e (), e) with _. begin
      assert ((t1 ^+ t2) ⊇ (h, fs_case_v (), e_case_s));
      introduce Inl? (fs_case_v ()) ==> (forall (v:value). t1 ∋ (h, Inl?.v (fs_case_v ()), v) ==> t3 ⊇ (h, fs_e (), subst_beta v e_lc_s)) with _. begin
        let prove_inl_branch () : Lemma
          (requires Inl? (fs_case_v ()))
          (ensures forall (v:value). t1 ∋ (h, Inl?.v (fs_case_v ()), v) ==> t3 ⊇ (h, fs_e (), subst_beta v e_lc_s)) =
          introduce forall (v:value). t1 ∋ (h, Inl?.v (fs_case_v ()), v) ==> t3 ⊇ (h, fs_e (), subst_beta v e_lc_s) with begin
            introduce _ ==> _ with _. begin
            let s' = gsub_extend s t1 v in
            let fsG' = stack fsG (Inl?.v (fs_case_v ())) in
            assert ((fsG' `(∽) h` s' /\ preLc fsG') ==> t3 ⊇ (h, fs_lc fsG', gsubst s' e_lc));
            assert (fsG `(∽) h` s);
            assert (t1 ∋ (h, Inl?.v (fs_case_v ()), v));
            lem_values_are_values t1 h (Inl?.v (fs_case_v ())) v;
            assert (stack fsG (Inl?.v (fs_case_v ())) `(∽) h` gsub_extend s t1 v);
            assert (preLc fsG');
            assert (t3 ⊇ (h, fs_lc fsG', gsubst s' e_lc));
            lem_substitution s t1 v e_lc;
            assert (subst_beta v e_lc_s == gsubst s' e_lc);
            assert (t3 ⊇ (h, fs_lc fsG', subst_beta v e_lc_s));
            assert (fs_e () == fs_lc fsG');
            assert (t3 ⊇ (h, fs_e (), subst_beta v e_lc_s))
            end
          end in
        prove_inl_branch ()
      end;
      introduce Inr? (fs_case_v ()) ==> (forall (v:value). t2 ∋ (h, Inr?.v (fs_case_v ()), v) ==> t3 ⊇ (h, fs_e (), subst_beta v e_rc_s)) with _. begin
        let prove_inr_branch () : Lemma
          (requires Inr? (fs_case_v ()))
          (ensures forall (v:value). t2 ∋ (h, Inr?.v (fs_case_v ()), v) ==> t3 ⊇ (h, fs_e (), subst_beta v e_rc_s)) =
          introduce forall (v:value). t2 ∋ (h, Inr?.v (fs_case_v ()), v) ==> t3 ⊇ (h, fs_e (), subst_beta v e_rc_s) with begin
            introduce _ ==> _ with _. begin
            let s' = gsub_extend s t2 v in
            let fsG' = stack fsG (Inr?.v (fs_case_v ())) in
            assert ((fsG' `(∽) h` s' /\ preRc fsG') ==> t3 ⊇ (h, fs_rc fsG', gsubst s' e_rc));
            assert (fsG `(∽) h` s);
            assert (t2 ∋ (h, Inr?.v (fs_case_v ()), v));
            lem_values_are_values t2 h (Inr?.v (fs_case_v ())) v;
            assert (stack fsG (Inr?.v (fs_case_v ())) `(∽) h` gsub_extend s t2 v);
            assert (preRc fsG');
            assert (t3 ⊇ (h, fs_rc fsG', gsubst s' e_rc));
            lem_substitution s t2 v e_rc;
            assert (subst_beta v e_rc_s == gsubst s' e_rc);
            assert (t3 ⊇ (h, fs_rc fsG', subst_beta v e_rc_s));
            assert (fs_e () == fs_rc fsG');
            assert (t3 ⊇ (h, fs_e (), subst_beta v e_rc_s))
            end
          end in
        prove_inr_branch ()
      end;
      introduce forall (e':closed_exp) lt. e_beh e e' h lt ==> (t3 ∋ (h, fs_e (), e') /\ lt == []) with begin
        introduce e_beh e e' h lt ==> (t3 ∋ (h, fs_e (), e') /\ lt == []) with _. begin
          helper_compat_val_case e' lt (fs_case_v ()) (fs_e ()) e_case_s e_lc_s e_rc_s
        end
      end
    end
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let compat_oval_lambda_ocomp #g (#t1:qType) (#preBody:spec_env (extend t1 g)) (#t2:qType) (fs_body:fs_ocomp (extend t1 g) t2 preBody) (body:exp)
  : Lemma
    (requires fs_body ⊒ body)
    (ensures fs_oval_lambda_ocomp fs_body ⊐ (ELam body)) =
  lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  let f : fs_oval g (t1 ^->!@ t2) (spec_env_lambda_tot preBody) = fun fsG x -> fs_body (stack fsG x) in
  assert (f == fs_oval_lambda_ocomp fs_body)
    by (FStar.Tactics.norm [delta_only [`%fs_oval_lambda_ocomp]]; FStar.Tactics.trefl ());
  introduce forall b (s:gsub g b) fsG h. (fsG `(∽) h` s /\ (spec_env_lambda_tot preBody) fsG) ==> (t1 ^->!@ t2) ⊇ (h, f fsG, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∋ (h++lt_v, fs_v, v) ==> t2 ⫄ (h++lt_v, (f fsG) fs_v, subst_beta v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fsG' = stack fsG fs_v in
          let h' = h++lt_v in
          let f1 () : Pure (fs_val (t1 ^->!@ t2))
            (requires ((spec_env_lambda_tot preBody) fsG))
            (ensures (fun _ -> True)) =
            f (tail #t1 fsG') in
          let f' : fs_comp t2 = f1 () (hd #t1 #g fsG') in
          assert ((fsG' `(∽) h'` s' /\ preBody fsG') ==> t2 ⫄ (h', f', gsubst s' body));
          assert ((spec_env_lambda_tot preBody) fsG);
          assert (preBody fsG');
          assert (fsG `(∽) h` s);
          assert (t1 ∋ (h++lt_v, fs_v, v));
          introduce forall (x:var). Some? (g x) ==> Some?.v (g x) ∋ (h++lt_v, index fsG x, s x) with begin
            introduce _ ==> _ with _. begin
              val_type_closed_under_history_extension (Some?.v (g x)) h (index fsG x) (s x)
            end
          end;
          assert (stack fsG fs_v `(∽) h'` gsub_extend s t1 v);
          assert (t2 ⫄ (h', f', gsubst s' body));
          assert (hd (stack fsG fs_v) == fs_v);
          assert (t2 ⫄ (h', f (tail fsG') fs_v, gsubst s' body));
          assert (t2 ⫄ (h', f fsG fs_v, gsubst s' body));
          lem_substitution s t1 v body;
          assert (t2 ⫄ (h', f fsG fs_v, subst_beta v body'))
        end
      end;
      assert (forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∋ (h++lt_v, fs_v, v) ==> t2 ⫄ (h++lt_v, f fsG fs_v, subst_beta v body'));
      fold_in_io_arrow t1 t2 h (f fsG) body';
      assert ((t1 ^->!@ t2) ∋ (h, f fsG, ELam body'));
      assert ((t1 ^->!@ t2) ∋ (h, f fsG, gsubst s (ELam body)));
      lem_values_are_expressions (t1 ^->!@ t2) h (f fsG) (gsubst s (ELam body));
      assert ((t1 ^->!@ t2) ⊇ (h, f fsG, gsubst s (ELam body)))
    end
  end;
  assert (fv_in_env g (ELam body));
  assert (forall b (s:gsub g b) fsG h. (fsG `(∽) h` s /\ (spec_env_lambda_tot preBody) fsG) ==> (t1 ^->!@ t2) ⊇ (h, f fsG, gsubst s (ELam body)));
  assert (f == fs_oval_lambda_ocomp fs_body)
    by (FStar.Tactics.norm [delta_only [`%fs_oval_lambda_ocomp]]; FStar.Tactics.trefl ());
  assert (forall b (s:gsub g b) fsG h. (fsG `(∽) h` s /\ (spec_env_lambda_tot preBody) fsG) ==> (t1 ^->!@ t2) ⊇ (h, fs_oval_lambda_ocomp fs_body fsG, gsubst s (ELam body)));
  assert_norm (superset_oval #g (t1 ^->!@ t2) (fs_oval_lambda_ocomp fs_body) (ELam body) ==
    (fv_in_env g (ELam body) /\
    (forall b (s:gsub g b) (fsG:eval_env g) (h:history).
      (fsG `(∽) h` s /\ (spec_env_lambda_tot preBody) fsG) ==> (t1 ^->!@ t2) ⊇ (h, fs_oval_lambda_ocomp fs_body fsG, gsubst s (ELam body)))));
  assert (superset_oval #g (t1 ^->!@ t2) (fs_oval_lambda_ocomp fs_body) (ELam body))
#pop-options

let compat_ocomp_return #g (#t:qType) #pre (fs_x:fs_oval g t pre) (x:exp)
  : Lemma
    (requires fs_x ⊐ x)
    (ensures fs_ocomp_return_oval fs_x ⊒ x) =
  introduce forall b (s:gsub g b) fsG h. (fsG `(∽) h` s /\ pre fsG) ==> t ⫄ (h, return (fs_x fsG), gsubst s x) with begin
    introduce _ ==> _ with _. begin
      let fs_x = fs_x fsG in
      let fs_e = return fs_x in
      let e = gsubst s x in
      introduce forall (lt:local_trace h) (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:fs_val t). t ∋ (h++lt, fs_r, e') /\ (fs_beh fs_e h lt fs_r)) with begin
        introduce e_beh e e' h lt ==> (exists (fs_r:fs_val t). t ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
        assert (t ⊇ (h, fs_x, e));
        eliminate forall e' lt'. e_beh e e' h lt' ==> (t ∋ (h, fs_x, e') /\ lt' == []) with e' lt;
        assert (t ∋ (h++lt, fs_x, e'));
        lem_thetaP_return fs_x h
        end
      end
    end
  end

#push-options "--ifuel 10 --z3rlimit 20 --fuel 2 --split_queries always"
let helper_compat_ocomp_bind (e':closed_exp) (#h:history) (lt:local_trace h) (#a:qType) (#b:qType) (fs_k':fs_val a -> fs_comp b) (fs_m:fs_comp a) (m k':exp) :
Lemma
  (requires is_closed (EApp (ELam k') m) /\
            (e_beh (EApp (ELam k') m) e' h lt) /\
            ((a ^->!@ b) ⊇ (h, fs_k', (ELam k'))) /\
            (a ⫄ (h, fs_m, m)))
  (ensures (exists (fs_r:fs_val b). b ∋ (h++lt, fs_r, e') /\ fs_beh (fs_comp_bind fs_m (fun m' -> fs_k' m')) h lt fs_r)) =
  bind_squash (steps (EApp (ELam k') m) e' h lt) #(exists (fs_r:fs_val b). b ∋ (h++lt, fs_r, e') /\ fs_beh (fs_comp_bind fs_m (fun m' -> fs_k' m')) h lt fs_r) (fun sts1 ->
    assert ((a ^->!@ b) ⊇ (h, fs_k', (ELam k'))); 
    assert (forall k_ lt1. e_beh (ELam k') k_ h lt1 ==> (ELam? k_ /\ is_closed k_));
    let a_typ = type_quotation_to_typ (get_rel a) in
    let b_typ = type_quotation_to_typ (get_rel b) in
    lem_value_is_irred (ELam k');
    let (k', (| [], lt |)) = destruct_steps_eapp_e1 (ELam k') m e' h lt sts1 a_typ b_typ in
    assert ((a ^->!@ b) ∋ (h, fs_k', (ELam k')));
    lem_forall_values_are_values_prod a h;
    let (m', (| lt1, lt' |)) = destruct_steps_eapp_e2 k' m e' h lt sts1 in
    eliminate forall m' lt1. e_beh m m' h lt1 ==> (exists (fs_r_m:fs_val a). a ∋ (h++lt1, fs_r_m, m') /\ fs_beh fs_m h lt1 fs_r_m) with m' lt1;
    lem_value_is_irred m';
    unfold_contains_io_arrow a b fs_k' k' h;
    eliminate exists (fs_r_m:fs_val a). a ∋ (h++lt1, fs_r_m, m') /\ fs_beh fs_m h lt1 fs_r_m
      returns exists (fs_r:fs_val b). b ∋ (h++lt, fs_r, e') /\ fs_beh (fs_comp_bind fs_m (fun m' -> fs_k' m')) h lt fs_r with _. begin
    trans_history h lt1 lt';
    eliminate exists (fs_r':fs_val b). b ∋ ((h++lt1)++lt', fs_r', e') /\ fs_beh (fs_k' fs_r_m) (h++lt1) lt' fs_r'
      returns exists (fs_r:fs_val b). b ∋ (h++lt, fs_r, e') /\ fs_beh (fs_comp_bind fs_m (fun m' -> fs_k' m')) h lt fs_r with _. begin
    assert (fs_beh fs_m h lt1 fs_r_m);
    assert (fs_beh ((fun m' -> fs_k' m') fs_r_m) (h++lt1) lt' fs_r');
    lem_fs_beh_bind fs_m h lt1 fs_r_m (fun m' -> fs_k' m') lt' fs_r'
    end
  end)
#pop-options

let compat_ocomp_bind #g (#a #b:qType) (#preM:spec_env g) (#preK:spec_env (extend a g)) (fs_m:fs_ocomp g a preM) (fs_k:fs_ocomp (extend a g) b preK) (m k:exp)
  : Lemma
    (requires fs_m ⊒ m /\ fs_k ⊒ k)
    (ensures (fs_ocomp_bind fs_m fs_k) ⊒ (EApp (ELam k) m)) =
  lem_fv_in_env_lam g a k;
  lem_fv_in_env_app g (ELam k) m;
  compat_oval_lambda_ocomp fs_k k;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(∽) h` s /\ spec_env_bind preM preK fsG) ==> b ⫄ (h, fs_ocomp_bind fs_m fs_k fsG, gsubst s (EApp (ELam k) m)) with begin
    let k' = subst (sub_elam s) k in
    assert (gsubst s (ELam k) == ELam k');
    let e = EApp (ELam k') (gsubst s m) in
    assert (gsubst s (EApp (ELam k) m) == e);
    let EApp (ELam k') m = e in
    introduce (fsG `(∽) h` s /\ spec_env_bind preM preK fsG) ==> b ⫄ (h, fs_ocomp_bind fs_m fs_k fsG, e) with _. begin
      assert (preM fsG);
      assert ((spec_env_lambda_tot preK) fsG);
      let fs_m' () : Pure (fs_comp a) (requires preM fsG) (ensures (fun _ -> True)) = fs_m fsG in
      let fs_k_oval : fs_oval g (a ^->!@ b) (spec_env_lambda_tot preK) = fun fsG x -> fs_k (stack fsG x) in
      assert (fs_k_oval == fs_oval_lambda_ocomp fs_k);
      let fs_k' () : Pure (fs_val (a ^->!@ b)) (requires (spec_env_lambda_tot preK) fsG) (ensures (fun _ -> True)) = fs_k_oval fsG in
      let fs_e = fs_comp_bind (fs_m' ()) (fun m' -> (fs_k' ()) m') in
      assert ((fs_ocomp_bind fs_m fs_k fsG) == fs_e);
      introduce forall lt (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:fs_val b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
        introduce e_beh e e' h lt ==> (exists (fs_r:fs_val b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
          lem_shift_type_value_environments h fsG s;
          assert ((a ^->!@ b) ⊇ (h, fs_oval_lambda_ocomp fs_k fsG, gsubst s (ELam k)));
          assert ((a ^->!@ b) ⊇ (h, fs_oval_lambda_ocomp fs_k fsG, ELam k'));
          assert ((a ^->!@ b) ⊇ (h, fs_k_oval fsG, ELam k'));
          assert ((a ^->!@ b) ⊇ (h, fs_k' (), ELam k'));
          helper_compat_ocomp_bind e' lt (fs_k' ()) (fs_m' ()) m k'
        end
      end
    end
  end

let helper_compat_ocomp_app_oval_oval_steps (e':closed_exp) (h:history) (lt:local_trace h) (a b:qType) (fs_f:fs_val (a ^->!@ b)) (fs_x:fs_val a) (f x:closed_exp) :
Lemma
  (requires (
    (e_beh (EApp f x) e' h lt) /\
    ((a ^->!@ b) ⊇ (h, fs_f, f)) /\
    (forall (lt:local_trace h). a ⊇ (h++lt, fs_x, x))))
  (ensures (exists (fs_r:fs_val b). b ∋ (h++lt, fs_r, e') /\ fs_beh (fs_f fs_x) h lt fs_r)) =
  assert (forall f' lt1. e_beh f f' h lt1 ==> (ELam? f' /\ is_closed f'));
  bind_squash (steps (EApp f x) e' h lt) (fun sts1 ->
    let a_typ = type_quotation_to_typ (get_rel a) in
    let b_typ = type_quotation_to_typ (get_rel b) in
    let (f1, (| lt1, lt' |)) = destruct_steps_eapp_e1 f x e' h lt sts1 a_typ b_typ in
    lem_forall_values_are_values a (h++lt1) fs_x;
    assert (forall x' (lt2:local_trace (h++lt1)). e_beh x x' (h++lt1) lt2 ==> is_value x');
    bind_squash (steps (EApp (ELam f1) x) e' (h++lt1) lt') (fun sts2 ->
      trans_history h lt1 lt';
      let (x', (| lt2, lt'' |)) = destruct_steps_eapp_e2 f1 x e' (h++lt1) lt' sts2 in
      eliminate forall f' lt1. e_beh f f' h lt1 ==> ((a ^->!@ b) ∋ (h, fs_f, f') /\ lt1 == []) with (ELam f1) lt1;
      lem_value_is_irred (ELam f1);
      eliminate forall x' lt2. e_beh x x' h lt2 ==> (a ∋ (h, fs_x, x') /\ lt2 == []) with x' lt2;
      lem_value_is_irred x';
      unfold_contains_io_arrow a b fs_f f1 h;
      assert (b ⫄ (h, fs_f fs_x, subst_beta x' f1));
      assert (exists (fs_r:fs_val b). b ∋ (h++lt, fs_r, e') /\ fs_beh (fs_f fs_x) h lt fs_r);
      get_squash (exists (fs_r:fs_val b). b ∋ (h++lt, fs_r, e') /\ fs_beh (fs_f fs_x) h lt fs_r)))

let compat_ocomp_app_oval_oval #g (#a #b:qType) #preF (fs_f:fs_oval g (a ^->!@ b) preF) #preX (fs_x:fs_oval g a preX) (f x:exp)
  : Lemma
    (requires fs_f ⊐ f /\ fs_x ⊐ x)
    (ensures (fs_ocomp_app_oval_oval fs_f fs_x) ⊒ (EApp f x)) =
  lem_fv_in_env_app g f x;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(∽) h` s /\ (spec_env_app preF preX) fsG) ==> b ⫄ (h, (fs_f fsG) (fs_x fsG), gsubst s (EApp f x)) with begin
    let preF = preF fsG in
    let preX = preX fsG in
    let pre = (preF /\ preX) in
    let fs_f () : Pure (fs_val (a ^->!@ b)) (requires preF) (ensures (fun _ -> True))  = fs_f fsG in
    let fs_x () : Pure (fs_val a) (requires preX) (ensures (fun _ -> True))  = fs_x fsG in
    let fs_e () : Pure (fs_comp b) (requires pre) (ensures (fun _ -> True))  = (fs_f ()) (fs_x ()) in
    let e = EApp (gsubst s f) (gsubst s x) in
    assert (gsubst s (EApp f x) == e);
    let EApp f x = e in
    introduce (fsG `(∽) h` s /\ pre) ==> b ⫄ (h, fs_e (), e) with _. begin
      introduce forall lt (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:fs_val b). b  ∋ (h++lt, fs_r, e') /\ (fs_beh (fs_e ()) h lt fs_r)) with begin
        introduce _ ==> (exists (fs_r:fs_val b). b ∋ (h++lt, fs_r, e') /\ fs_beh (fs_e ()) h lt fs_r) with _. begin
          lem_shift_type_value_environments h fsG s;
          helper_compat_ocomp_app_oval_oval_steps e' h lt a b (fs_f ()) (fs_x ()) f x
        end
      end
    end
  end

let helper_compat_ocomp_if_val (ex':closed_exp) (#h:history) (lt:local_trace h) (a:qType) (fs_c:fs_val qBool) (fs_e:fs_comp a) (c t e:closed_exp) :
  Lemma
    (requires (e_beh (EIf c t e) ex' h lt /\
               qBool ⊇ (h, fs_c, c) /\
               (if fs_c then a ⫄ (h, fs_e, t) else a ⫄ (h, fs_e, e))))
    (ensures (exists (fs_r:fs_val a). a ∋ (h++lt, fs_r, ex') /\ fs_beh fs_e h lt fs_r)) =
  assert (forall c' lt'. e_beh c c' h lt' ==> (ETrue? c' \/ EFalse? c'));
  bind_squash (steps (EIf c t e) ex' h lt) #(exists (fs_r:fs_val a). a ∋ (h++lt, fs_r, ex') /\ fs_beh fs_e h lt fs_r) (fun sts ->
    let (c', (| lt1, lt2 |)) = destruct_steps_eif c t e ex' h lt sts in
    assert (qBool ∋ (h, fs_c, c') /\ lt1 == []);
    assert (exists (fs_r:fs_val a). a ∋ (h++lt2, fs_r, ex') /\ fs_beh fs_e h lt2 fs_r))

let compat_ocomp_if_oval #g (#a:qType) #preC #preT #preE
  (fs_c:fs_oval g qBool preC) (fs_t:fs_ocomp g a preT) (fs_e:fs_ocomp g a preE) (c t e:exp)
  : Lemma
    (requires fs_c ⊐ c /\ fs_t ⊒ t /\ fs_e ⊒ e)
    (ensures (fs_ocomp_if_oval fs_c fs_t fs_e) ⊒ (EIf c t e)) =
  lem_fv_in_env_if g c t e;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(∽) h` s /\ (spec_env_if fs_c preT preE) fsG) ==> a ⫄ (h, (if (fs_c fsG) then (fs_t fsG) else (fs_e fsG)), gsubst s (EIf c t e)) with begin
    let ex = EIf (gsubst s c) (gsubst s t) (gsubst s e) in
    assert (gsubst s (EIf c t e) == ex);
    let EIf c t e = ex in
    introduce (fsG `(∽) h` s /\ (spec_env_if fs_c preT preE) fsG) ==> a ⫄ (h, (if fs_c fsG then fs_t fsG else fs_e fsG), ex) with _. begin
      let fs_c = fs_c fsG in
      let fs_ex = if fs_c then fs_t fsG else fs_e fsG in
      introduce forall lt (ex':closed_exp). e_beh ex ex' h lt ==> (exists (fs_r:fs_val a). a ∋ (h++lt, fs_r, ex') /\ fs_beh fs_ex h lt fs_r) with begin
        introduce e_beh ex ex' h lt ==> (exists (fs_r:fs_val a). a ∋ (h++lt, fs_r, ex') /\ fs_beh fs_ex h lt fs_r) with _. begin
          assert (qBool ⊇ (h, fs_c, c));
          assert (if fs_c then a ⫄ (h, fs_ex, t) else a ⫄ (h, fs_ex, e));
          helper_compat_ocomp_if_val ex' lt a fs_c fs_ex c t e
        end
      end
    end
  end

#push-options "--fuel 2 --z3rlimit 10"
let helper_compat_prod_case_val
  (e':closed_exp)
  (#h:history) (lt:local_trace h)
  (#a #b #c:qType)
  (fs_sc:fs_val (a ^+ b))
  (fs_r:fs_comp c)
  (e_sc:closed_exp)
  (e_li:exp{is_closed (ELam e_li)})
  (e_ri:exp{is_closed (ELam e_ri)}) :
  Lemma
    (requires (
      steps (ECase e_sc e_li e_ri) e' h lt /\
      indexed_irred e' (h++lt) /\
      (a ^+ b) ⊇ (h, fs_sc, e_sc) /\ 
      (Inl? fs_sc ==> (forall (v:value). a ∋ (h, Inl?.v fs_sc, v) ==> c ⫄ (h, fs_r, subst_beta v e_li))) /\
      (Inr? fs_sc ==> (forall (v:value). b ∋ (h, Inr?.v fs_sc, v) ==> c ⫄ (h, fs_r, subst_beta v e_ri)))))
    (ensures (exists (fs_r':fs_val c). c ∋ (h++lt, fs_r', e') /\ fs_beh fs_r h lt fs_r')) =
  lem_forall_values_are_values (a ^+ b) h fs_sc;
  assert (forall e_sc' lt'. e_beh e_sc e_sc' h lt' ==> (EInl? e_sc' \/ EInr? e_sc'));
  bind_squash (steps (ECase e_sc e_li e_ri) e' h lt) #(exists (fs_r':fs_val c). c ∋ (h++lt, fs_r', e') /\ fs_beh fs_r h lt fs_r') (fun sts -> 
    let a_typ = type_quotation_to_typ (get_rel a) in
    let b_typ = type_quotation_to_typ (get_rel b) in
    let (e_sc', (| lt1, lt2 |)) = destruct_steps_ecase e_sc e_li e_ri e' h lt sts a_typ b_typ in
    eliminate forall e_sc'' lt'. e_beh e_sc e_sc'' h lt' ==> ((a ^+ b) ∋ (h, fs_sc, e_sc'') /\ lt' == []) with e_sc' lt1;
    let res = match e_sc' with | EInl _ -> e_li | EInr _ -> e_ri in
    let res' = match e_sc' with | EInl x -> x | EInr x -> x in
    let tres' = match e_sc' with | EInl _ -> a | EInr _ -> b in
    match fs_sc, e_sc' with
    | Inl fs_x, EInl v -> begin
      assert (Inl? fs_sc);
      assert (a ∋ (h, fs_x, v));
      eliminate forall (v':value). a ∋ (h, Inl?.v fs_sc, v') ==> c ⫄ (h, fs_r, subst_beta v' e_li) with v;
      assert (c ⫄ (h, fs_r, subst_beta v e_li))
      end
    | Inr fs_x, EInr v -> begin
      assert (Inr? fs_sc);
      assert (b ∋ (h, fs_x, v));
      eliminate forall (v':value). b ∋ (h, Inr?.v fs_sc, v') ==> c ⫄ (h, fs_r, subst_beta v' e_ri) with v;
      assert (c ⫄ (h, fs_r, subst_beta v e_ri))
      end
    | _ -> false_elim ();
    assert (c ⫄ (h, fs_r, subst_beta res' res));
    get_squash (exists (fs_r':fs_val c). c ∋ (h++lt, fs_r', e') /\ fs_beh fs_r h lt fs_r'))
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 1 --ifuel 1"
let compat_ocomp_case_oval 
  #g 
  (#a #b #c:qType) 
  (#preCond:spec_env g)
  (#preInlc:spec_env (extend a g))
  (#preInrc:spec_env (extend b g))
  (fs_cond:fs_oval g (a ^+ b) preCond) 
  (fs_inlc:fs_ocomp (extend a g) c preInlc) 
  (fs_inrc:fs_ocomp (extend b g) c preInrc) 
  (cond inlc inrc:exp)
  : Lemma
    (requires fs_cond ⊐ cond /\ fs_inlc ⊒ inlc /\ fs_inrc ⊒ inrc)
    (ensures (fs_ocomp_case_oval fs_cond fs_inlc fs_inrc) ⊒ (ECase cond inlc inrc)) =
  lem_fv_in_env_case g a b cond inlc inrc;
  lem_fv_in_env_lam g a inlc;
  lem_fv_in_env_lam g b inrc;
  compat_oval_lambda_ocomp fs_inlc inlc;
  compat_oval_lambda_ocomp fs_inrc inrc;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(∽) h` s /\ (spec_env_case fs_cond preInlc preInrc) fsG) ==> c ⫄ (h, fs_ocomp_case_oval fs_cond fs_inlc fs_inrc fsG, gsubst s (ECase cond inlc inrc)) with begin
    let preCondH = preCond fsG in
    let fs_sc_v () : Pure (fs_val (a ^+ b)) (requires preCondH) (ensures (fun _ -> True)) = fs_cond fsG in
    let fs_e () : Pure (fs_comp c)
      (requires (preCondH /\
                  (Inl? (fs_sc_v ()) ==> preInlc (stack fsG (Inl?.v (fs_sc_v ())))) /\
                  (Inr? (fs_sc_v ()) ==> preInrc (stack fsG (Inr?.v (fs_sc_v ()))))))
      (ensures (fun _ -> True))
      = match fs_sc_v () with
        | Inl x -> fs_inlc (stack fsG x)
        | Inr x -> fs_inrc (stack fsG x) in
    let e = ECase (gsubst s cond) (subst (sub_elam s) inlc) (subst (sub_elam s) inrc) in
    assert (gsubst s (ECase cond inlc inrc) == e);
    let ECase cond_s inlc_s inrc_s = e in
    assert (inlc_s == subst (sub_elam s) inlc);
    assert (inrc_s == subst (sub_elam s) inrc);
    introduce (fsG `(∽) h` s /\ (spec_env_case fs_cond preInlc preInrc) fsG) ==> c ⫄ (h, fs_e (), e) with _. begin
      assert ((a ^+ b) ⊇ (h, fs_sc_v (), cond_s));
      introduce Inl? (fs_sc_v ()) ==> (forall (v:value). a ∋ (h, Inl?.v (fs_sc_v ()), v) ==> c ⫄ (h, fs_e (), subst_beta v inlc_s)) with _. begin
        let prove_inl_branch () : Lemma
          (requires Inl? (fs_sc_v ()))
          (ensures forall (v:value). a ∋ (h, Inl?.v (fs_sc_v ()), v) ==> c ⫄ (h, fs_e (), subst_beta v inlc_s)) = 
          introduce forall (v:value). a ∋ (h, Inl?.v (fs_sc_v ()), v) ==> c ⫄ (h, fs_e (), subst_beta v inlc_s) with begin
            introduce _ ==> _ with _. begin
            let s' = gsub_extend s a v in
            let fsG' = stack fsG (Inl?.v (fs_sc_v ())) in
            assert ((fsG' `(∽) h` s' /\ preInlc fsG') ==> c ⫄ (h, fs_inlc fsG', gsubst s' inlc));
            assert (fsG `(∽) h` s);
            assert (a ∋ (h, Inl?.v (fs_sc_v ()), v));
            lem_values_are_values a h (Inl?.v (fs_sc_v ())) v; 
            assert (stack fsG (Inl?.v (fs_sc_v ())) `(∽) h` gsub_extend s a v);
            assert (preInlc fsG');
            assert (c ⫄ (h, fs_inlc fsG', gsubst s' inlc));
            lem_substitution s a v inlc;
            assert (subst_beta v inlc_s == gsubst s' inlc);
            assert (fs_e () == fs_inlc fsG');
            assert (c ⫄ (h, fs_e (), subst_beta v inlc_s))
            end
          end in
        prove_inl_branch ()
      end;
      introduce Inr? (fs_sc_v ()) ==> (forall (v:value). b ∋ (h, Inr?.v (fs_sc_v ()), v) ==> c ⫄ (h, fs_e (), subst_beta v inrc_s)) with _. begin
        let prove_inr_branch () : Lemma
          (requires Inr? (fs_sc_v ()))
          (ensures forall (v:value). b ∋ (h, Inr?.v (fs_sc_v ()), v) ==> c ⫄ (h, fs_e (), subst_beta v inrc_s)) = 
          introduce forall (v:value). b ∋ (h, Inr?.v (fs_sc_v ()), v) ==> c ⫄ (h, fs_e (), subst_beta v inrc_s) with begin
            introduce _ ==> _ with _. begin
            let s' = gsub_extend s b v in
            let fsG' = stack fsG (Inr?. v (fs_sc_v ())) in
            assert ((fsG' `(∽) h` s' /\ preInrc fsG') ==> c ⫄ (h, fs_inrc fsG', gsubst s' inrc));
            assert (fsG `(∽) h` s);
            assert (b ∋ (h, Inr?.v (fs_sc_v ()), v));
            lem_values_are_values b h (Inr?.v (fs_sc_v ())) v; 
            assert (stack fsG (Inr?.v (fs_sc_v ())) `(∽) h` gsub_extend s b v);
            assert (preInrc fsG');
            assert (c ⫄ (h, fs_inrc fsG', gsubst s' inrc));
            lem_substitution s b v inrc;
            assert (subst_beta v inrc_s == gsubst s' inrc);
            assert (fs_e () == fs_inrc fsG');
            assert (c ⫄ (h, fs_e (), subst_beta v inrc_s))
            end
          end in
        prove_inr_branch ()
      end;
      introduce forall (e':closed_exp) lt. e_beh e e' h lt ==> (exists (fs_r':fs_val c). c ∋ (h++lt, fs_r', e') /\ fs_beh (fs_e ()) h lt fs_r') with begin
        introduce e_beh e e' h lt ==> (exists (fs_r':fs_val c). c ∋ (h++lt, fs_r', e') /\ fs_beh (fs_e ()) h lt fs_r') with _. begin
          helper_compat_prod_case_val e' lt (fs_sc_v ()) (fs_e ()) cond_s inlc_s inrc_s
        end
      end
    end
  end
#pop-options

let lem_value_steps_gives_refl (e:value) (e':closed_exp) (h:history) (lt:local_trace h) :
  Lemma
    (requires steps e e' h lt)
    (ensures e == e' /\ lt == []) =
  lem_value_is_irred e;
  introduce steps e e' h lt ==> (e == e' /\ lt == []) with _. begin
    FStar.Squash.bind_squash #(steps e e' h lt) () (fun sts ->
      lem_irred_implies_srefl_steps sts)
  end

(* From ∋ at q_io_args, derive the as_e_io_args representation *)
let lem_if_arg_value_then_exists (op:io_ops) (h:history) (fs_arg:fs_val (q_io_args op)) (val_arg:closed_exp) :
  Lemma
    (requires (q_io_args op) ∋ (h, fs_arg, val_arg))
    (ensures exists (args:io_args op). val_arg == as_e_io_args op args) =
  match op with
  | OWrite -> begin
    let EPair (EFileDescr arg1) (EString arg2) = val_arg in
    assert (as_e_io_args OWrite (arg1, arg2) == val_arg)
    end
  | _ -> ()

(*#push-options "--fuel 2 --z3rlimit 10"
let lem_ecall_result_facts
  (op:io_ops)
  (fs_arg:fs_val (q_io_args op){fs_val (q_io_args op) == io_args op})
  (args:io_args op)
  (res:io_res op args{fs_val (q_io_res op) == io_res op args})
  (val_arg:value)
  (e':closed_exp)
  (h:history) :
  Lemma
    (requires
      (q_io_args op) ∋ (h, fs_arg, val_arg) /\
      io_post h op args res /\
      val_arg == as_e_io_args op args /\
      e' == as_e_io_res op args res)
    (ensures
      (q_io_res op) ∋ (h ++ [op_to_ev op args res], res, e') /\
      fs_beh (fs_comp_call_val op fs_arg) h [op_to_ev op args res] res) =
  match op with
  | OOpen -> lem_thetaP_call OOpen fs_arg res h
  | ORead -> lem_thetaP_call ORead fs_arg res h
  | OClose -> lem_thetaP_call OClose fs_arg res h
  | OWrite -> lem_thetaP_call OWrite fs_arg res h
#pop-options*)

(* General helper for all ops - no case analysis on op *)
#push-options "--fuel 4 --z3rlimit 20"
let rec destruct_steps_ecall_arg_all
  (op:io_ops) (arg:closed_exp) (e':closed_exp) (h:history) (lt:local_trace h)
  (fs_arg:fs_val (q_io_args op))
  (st:steps (ECall op arg) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt) /\
      (q_io_args op) ⊇ (h, fs_arg, arg))
    (ensures fun (val_arg, (| lt1, lt' |)) ->
      (q_io_args op) ∋ (h, fs_arg, val_arg) /\
      (exists (args:io_args op). val_arg == as_e_io_args op args) /\
      steps arg val_arg h lt1 /\
      steps (ECall op arg) (ECall op val_arg) h lt1 /\
      steps (ECall op val_arg) e' (h++lt1) lt' /\
      (lt == (lt1 @ lt')))
    (decreases st) =
  match st with
  | SRefl _ h -> begin
    (* ECall op arg is irreducible, but it can always step — contradiction.
       First derive indexed_irred arg h from indexed_irred (ECall op arg) h. *)
    introduce forall (arg':closed_exp) (oev:option (event_h h)). step arg arg' h oev ==> False with begin
      introduce _ ==> _ with st. begin
        FStar.Squash.bind_squash st (fun st -> FStar.Squash.return_squash (SCall #arg #arg' #h #oev #op st))
      end
    end;
    assert (e_beh arg arg h []);
    assert ((q_io_args op) ∋ (h, fs_arg, arg));
    lem_if_arg_value_then_exists op h fs_arg arg;
    can_step_ecall_val op arg h;
    false_elim ()
    end
  | STrans #e #f2 #e' #h #_ #lt23 step_ecall step_ecall_steps -> begin
    let (ECall _ arg) = e in
    match step_ecall with
    | SCall #arg #arg' #h' #oev #_ step_arg -> begin
      let (ECall _ arg') = f2 in
      lem_step_implies_steps arg arg' h oev;
      lem_step_implies_steps (ECall op arg) (ECall op arg') h oev;
      let lt1 : local_trace h = as_lt oev in
      let s2 : steps (ECall op arg') e' (h++lt1) lt23 = step_ecall_steps in
      trans_history h lt1 lt23;
      lem_superset_preserved_by_step (q_io_args op) h fs_arg arg arg' oev;
      let (val_arg, (| lt1', lt' |)) = destruct_steps_ecall_arg_all op arg' e' (h++lt1) lt23 fs_arg s2 in
      trans_history h lt1 lt1';
      lem_steps_transitive arg arg' val_arg h lt1 lt1';
      lem_steps_transitive (ECall op arg) (ECall op arg') (ECall op val_arg) h lt1 lt1';
      assert ((q_io_args op) ∋ (h++lt1, fs_arg, val_arg));
      (* from ⊇ preservation, the trace from arg to val_arg is empty *)
      lem_value_is_irred val_arg;
      assert (e_beh arg val_arg h (lt1 @ lt1'));
      assert ((lt1 @ lt1') == []);
      (val_arg, (| (lt1 @ lt1'), lt' |))
      end
    | SCallReturn _ _ args _ -> begin
      (* arg is already as_e_io_args form, which is a value *)
      lem_value_is_irred (as_e_io_args op args);
      assert (e_beh arg arg h []);
      assert ((q_io_args op) ∋ (h, fs_arg, arg));
      lem_if_arg_value_then_exists op h fs_arg arg;
      (arg, (| [], lt |))
      end
    end
#pop-options

(* General step decomposition for all ops using ⫄ threading.
   Unlike destruct_steps_ecall_arg_all (which uses ⊇), this threads the original
   ⫄ computation relation and accumulated steps through the recursion.
   This avoids needing indexed_sem_expr_shape, which doesn't exist for OWrite. *)
#push-options "--fuel 4 --z3rlimit 20"
let rec destruct_steps_ecall_arg_comp
  (op:io_ops) (arg:closed_exp) (e':closed_exp) (h:history) (lt:local_trace h)
  (st:steps (ECall op arg) e' h lt)
  (arg0:closed_exp) (h0:history) (lt_acc:local_trace h0) (fs_arg0:fs_comp (q_io_args op))
  : Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt) /\
      h == h0 ++ lt_acc /\
      (q_io_args op) ⫄ (h0, fs_arg0, arg0) /\
      squash (steps arg0 arg h0 lt_acc))
    (ensures fun (val_arg, (| lt1, lt' |)) ->
      indexed_irred val_arg (h++lt1) /\
      (exists (args:io_args op). val_arg == as_e_io_args op args) /\
      steps arg val_arg h lt1 /\
      steps (ECall op arg) (ECall op val_arg) h lt1 /\
      steps (ECall op val_arg) e' (h++lt1) lt' /\
      (lt == (lt1 @ lt')))
    (decreases st) =
  match st with
  | SRefl _ h -> begin
    (* ECall op arg is irreducible → derive indexed_irred arg h *)
    introduce forall (arg':closed_exp) (oev:option (event_h h)). step arg arg' h oev ==> False with begin
      introduce _ ==> _ with st. begin
        FStar.Squash.bind_squash st (fun st -> FStar.Squash.return_squash (SCall #arg #arg' #h #oev #op st))
      end
    end;
    assert (e_beh arg0 arg h0 lt_acc);
    (* From ⫄ + e_beh, derive that arg has the as_e_io_args form *)
    Classical.forall_intro (Classical.move_requires (fun (fs_r:fs_val (q_io_args op)) -> lem_if_arg_value_then_exists op (h0++lt_acc) fs_r arg));
    can_step_ecall_val op arg h;
    false_elim ()
    end
  | STrans #e #f2 #e' #h #_ #lt23 step_ecall step_ecall_steps -> begin
    let (ECall _ arg) = e in
    match step_ecall with
    | SCall #arg #arg' #h' #oev #_ step_arg -> begin
      let (ECall _ arg') = f2 in
      lem_step_implies_steps arg arg' h oev;
      lem_step_implies_steps (ECall op arg) (ECall op arg') h oev;
      let lt1 : local_trace h = as_lt oev in
      let s2 : steps (ECall op arg') e' (h++lt1) lt23 = step_ecall_steps in
      trans_history h lt1 lt23;
      lem_steps_transitive arg0 arg arg' h0 lt_acc lt1;
      trans_history h0 lt_acc lt1;
      let (val_arg, (| lt1', lt' |)) = destruct_steps_ecall_arg_comp op arg' e' (h++lt1) lt23 s2 arg0 h0 (lt_acc @ lt1) fs_arg0 in
      trans_history h lt1 lt1';
      lem_steps_transitive arg arg' val_arg h lt1 lt1';
      lem_steps_transitive (ECall op arg) (ECall op arg') (ECall op val_arg) h lt1 lt1';
      associative_history lt1 lt1' lt';
      (val_arg, (| (lt1 @ lt1'), lt' |))
      end
    | SCallReturn _ _ args _ -> begin
      lem_value_is_irred (as_e_io_args op args);
      (arg, (| [], lt |))
      end
    end
#pop-options

(* General helper - works for all ops without case analysis on op *)
#push-options "--fuel 2 --z3rlimit 10"
let helper_compat_ocomp_call_oval (op:io_ops) (e':closed_exp) (h:history) (lt:local_trace h)
  (fs_arg:fs_val (q_io_args op)) (arg:closed_exp) :
  Lemma
    (requires e_beh (ECall op arg) e' h lt /\
              (q_io_args op) ⊇ (h, fs_arg, arg))
    (ensures (exists (fs_r:fs_val (q_io_res op)). (q_io_res op) ∋ (h++lt, fs_r, e') /\
             fs_beh (fs_comp_call_val op fs_arg) h lt fs_r)) = admit ()
  (*let the_goal = exists (fs_r:fs_val (q_io_res op)). (q_io_res op) ∋ (h++lt, fs_r, e') /\ fs_beh (fs_comp_call_val op fs_arg) h lt fs_r in
  lem_forall_values_are_values (q_io_args op) h fs_arg;
  bind_squash (steps (ECall op arg) e' h lt) (fun steps_e_e' ->
    let (arg', (| lt1, lt' |)) = destruct_steps_ecall_arg_all op arg e' h lt fs_arg steps_e_e' in
    FStar.Squash.bind_squash #(steps (ECall op arg') e' (h++lt1) lt') #the_goal () (fun sts1 ->
      trans_history h lt1 lt';
      let (e_r, (| lt2, lt3 |)) = destruct_steps_ecall op arg' e' (h++lt1) lt' sts1 in
      lem_value_is_irred arg';
      lem_value_steps_gives_refl e_r e' ((h++lt1)++lt2) lt3;
      let goal_lemma () : Lemma the_goal =
        assert (e_beh arg arg' h lt1);
        assert (lt1 == []);
        assert ((q_io_args op) ∋ (h, fs_arg, arg'));
        eliminate exists (args:io_args op) (res:io_res op args).
          io_pre (h++lt1) op args /\ io_post (h++lt1) op args res /\
          arg' == as_e_io_args op args /\
          e_r == as_e_io_res op args res /\
          lt2 == [op_to_ev op args res]
        returns the_goal with _. begin
          match op with
          | OOpen -> begin
            lem_thetaP_call OOpen fs_arg res h;
            //let _ : either file_descr unit = res in
            //assert (fs_beh (fs_comp_call_val op fs_arg) h [op_to_ev op args res] res);
            //assert ((q_io_res op) ∋ (h++[op_to_ev op args res], res, e'));
            admit ()
            end
          | _ -> admit ()
          //lem_ecall_result_facts op fs_arg args res arg' e_r (h++lt1)
        end
      in
      goal_lemma ();
      get_squash the_goal))*)
#pop-options

(* General compat_ocomp_call_oval - works for all ops *)
let compat_ocomp_call_oval #g (op:io_ops) #preArgs (fs_arg:fs_oval g (q_io_args op) preArgs) (arg:exp)
  : Lemma
    (requires fs_arg ⊐ arg)
    (ensures fs_ocomp_call_oval op fs_arg ⊒ ECall op arg)
  = admit ()
  (*lem_fv_in_env_call g op arg;
  introduce forall b (s:gsub g b) (fsG:eval_env g) (h:history). (fsG `(∽) h` s /\ (spec_env_bind' #g #(q_io_args op) preArgs (fun a -> spec_env_return_comp #g #(q_io_res op) (fs_comp_call_val op a))) fsG) ==> (q_io_res op) ⫄ (h, io_call op (fs_arg fsG), gsubst s (ECall op arg)) with begin
    let fs_arg_v = fs_arg fsG in
    let fs_e = io_call op fs_arg_v in
    let e = ECall op (gsubst s arg) in
    assert (gsubst s (ECall op arg) == e);
    let ECall _ arg = e in
    introduce fsG `(∽) h` s ==> (q_io_res op) ⫄ (h, fs_e, e) with _. begin
      introduce forall (lt:local_trace h) (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:fs_val (q_io_res op)). (q_io_res op) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
        introduce e_beh e e' h lt ==> (exists (fs_r:fs_val (q_io_res op)). (q_io_res op) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
          lem_shift_type_value_environments h fsG s;
          helper_compat_ocomp_call_oval op e' h lt fs_arg_v arg
        end
      end
    end
  end*)

let compat_ocomp_unit g : Lemma (fs_ocomp_return_val g qUnit () ⊒ EUnit) =
  compat_oval_unit g;
  compat_ocomp_return (fs_oval_return g #qUnit ()) EUnit

let compat_ocomp_true g : Lemma (fs_ocomp_return_val g qBool true ⊒ ETrue) =
  compat_oval_true g;
  compat_ocomp_return (fs_oval_return g #qBool true) ETrue

let compat_ocomp_false g : Lemma (fs_ocomp_return_val g qBool false ⊒ EFalse) =
  compat_oval_false g;
  compat_ocomp_return (fs_oval_return g #qBool false) EFalse

let compat_ocomp_string g s : Lemma (fs_ocomp_return_val g qString s ⊒ EString s) =
  compat_oval_string g s;
  compat_ocomp_return (fs_oval_return g #qString s) (EString s)

open FStar.Tactics.V1

let compat_ocomp_if #g
  (#t:qType) #preC #preT #preE
  (fs_e1:fs_ocomp g qBool preC) (fs_e2:fs_ocomp g t preT) (fs_e3:fs_ocomp g t preE)
  (e1:exp) (e2:exp) (e3:exp)
  : Lemma
    (requires fs_e1 ⊒ e1 /\ fs_e2 ⊒ e2 /\ fs_e3 ⊒ e3)
    (ensures fs_ocomp_if fs_e1 fs_e2 fs_e3 ⊒ EIf e1 e2 e3) =
  lem_fv_in_env_if g e1 e2 e3;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(∽) h` s /\ (spec_env_bind' #g #qBool preC (fun c' -> if c' then preT else preE)) fsG) ==> t ⫄ (h, fs_ocomp_if fs_e1 fs_e2 fs_e3 fsG, gsubst s (EIf e1 e2 e3)) with begin
    introduce _ ==> _ with _. begin
      assert (preC fsG);
      let fs_e1' () : Pure (fs_comp qBool) (requires preC fsG) (ensures (fun _ -> True)) = fs_e1 fsG in
      let fs_e = fs_comp_bind (fs_e1' ()) (fun x -> if x then fs_e2 fsG else fs_e3 fsG) in
      assert (fs_e == fs_ocomp_if fs_e1 fs_e2 fs_e3 fsG) by (
        norm [delta_only [`%fs_ocomp_if;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_if_val]];
        simplify_stack_ops ();
        trefl ());
      let e = EIf (gsubst s e1) (gsubst s e2) (gsubst s e3) in
      assert (gsubst s (EIf e1 e2 e3) == e) by (trefl ());
      let EIf e1 e2 e3 = e in
      introduce fsG `(∽) h` s ==> t ⫄ (h, fs_e, e) with _. begin
        introduce forall lt (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:fs_val t). t ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
          introduce e_beh e e' h lt ==> (exists (fs_r:fs_val t). t ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
            lem_shift_type_value_environments h fsG s;
            bind_squash (steps e e' h lt) (fun sts1 ->
              let (e1', (| lt1, lt2 |)) = destruct_steps_eif e1 e2 e3 e' h lt sts1 in
              eliminate exists (fs_r_e1:fs_val qBool). qBool ∋ (h++lt1, fs_r_e1, e1') /\ fs_beh (fs_e1' ()) h lt1 fs_r_e1
              returns exists (fs_r:fs_val t). t ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r with _. begin
                lem_values_are_expressions qBool (h++lt1) fs_r_e1 e1';
                trans_history h lt1 lt2;
                assert (if fs_r_e1 then preT fsG else preE fsG);
                let fs_ex : fs_comp t = if fs_r_e1 then fs_e2 fsG else fs_e3 fsG in
                assert (if fs_r_e1 then t ⫄ (h++lt1, fs_ex, e2) else t ⫄ (h++lt1, fs_ex, e3));
                helper_compat_ocomp_if_val e' lt2 t fs_r_e1 fs_ex e1' e2 e3;
                eliminate exists (fs_r:fs_val t). t ∋ (h++lt1++lt2, fs_r, e') /\ fs_beh fs_ex (h++lt1) lt2 fs_r
                returns exists (fs_r:fs_val t). t ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r with _. begin
                  assert (fs_ex == (if fs_r_e1 then fs_e2 fsG else fs_e3 fsG));
                  lem_fs_beh_bind (fs_e1' ()) h lt1 fs_r_e1 (fun x -> if x then fs_e2 fsG else fs_e3 fsG) lt2 fs_r
                end
              end)
          end
        end
      end
    end
  end

let compat_ocomp_file_descr g fd : Lemma (fs_ocomp_return_val g qFileDescr fd ⊒ EFileDescr fd) =
  compat_oval_file_descr g fd;
  compat_ocomp_return (fs_oval_return g #qFileDescr fd) (EFileDescr fd)

let compat_ocomp_var g (x:var{Some? (g x)}) : Lemma (fs_ocomp_var g x ⊒ EVar x) =
  compat_oval_var g x;
  compat_ocomp_return (fs_oval_var g x) (EVar x)

let compat_ocomp_app #g (#a #b:qType) #preF #preX (fs_f:fs_ocomp g (a ^->!@ b) preF) (fs_x:fs_ocomp g a preX) (f x:exp)
  : Lemma
    (requires fs_f ⊒ f /\ fs_x ⊒ x)
    (ensures fs_ocomp_app fs_f fs_x ⊒ EApp f x)
  =
  lem_fv_in_env_app g f x;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(∽) h` s /\ (spec_env_bind' #g #(a ^->!@ b) preF (fun f' -> spec_env_bind' #g #a preX (fun x' -> spec_env_return_comp #g #b (f' x')))) fsG) ==> b ⫄ (h, fs_ocomp_app fs_f fs_x fsG, gsubst s (EApp f x)) with begin
    let e = EApp (gsubst s f) (gsubst s x) in
    assert (gsubst s (EApp f x) == e) by (trefl ());
    let EApp f x = e in
    introduce (fsG `(∽) h` s /\ (spec_env_bind' #g #(a ^->!@ b) preF (fun f' -> spec_env_bind' #g #a preX (fun x' -> spec_env_return_comp #g #b (f' x')))) fsG) ==> b ⫄ (h, fs_ocomp_app fs_f fs_x fsG, e) with _. begin
      assert (preF fsG);
      let fs_f' : fs_comp (a ^->!@ b) = fs_f fsG in
      let fs_e = fs_ocomp_app fs_f fs_x fsG in
      introduce forall lt (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:fs_val b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
        introduce e_beh e e' h lt ==> (exists (fs_r:fs_val b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
          bind_squash (steps e e' h lt) (fun sts1 ->
            let a_typ = type_quotation_to_typ (get_rel a) in
            let b_typ = type_quotation_to_typ (get_rel b) in
            let (f1, (| lt1, lt' |)) = destruct_steps_eapp_e1 f x e' h lt sts1 a_typ b_typ in
            assert ((a ^->!@ b) ⫄ (h, fs_f', f));
            eliminate forall lt1 f'. e_beh f f' h lt1 ==> (exists (fs_r_f:fs_val (a ^->!@ b)). (a ^->!@ b) ∋ (h++lt1, fs_r_f, f') /\ fs_beh fs_f' h lt1 fs_r_f) with lt1 (ELam f1);
            lem_value_is_irred (ELam f1);
            eliminate exists (fs_r_f:fs_val (a ^->!@ b)). (a ^->!@ b) ∋ (h++lt1, fs_r_f, (ELam f1)) /\ fs_beh fs_f' h lt1 fs_r_f
              returns exists (fs_r:fs_val b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r with _. begin
            let _ : fs_val a -> fs_comp b = fs_r_f in
            lem_values_are_expressions (a ^->!@ b) (h++lt1) fs_r_f (ELam f1);
            trans_history h lt1 lt';
            lem_shift_type_value_environments h fsG s;
            eliminate forall (lt:local_trace h). fsG `(∽) h` s ==> fsG `(∽) (h++lt)` s with lt1;
            lem_shift_type_value_environments (h++lt1) fsG s;
            assert (spec_env_bind' #g #a preX (fun x' -> spec_env_return_comp #g #b (fs_r_f x')) fsG);
            assert (preX fsG);
            let fs_x' : fs_comp a = fs_x fsG in
            helper_compat_ocomp_bind e' #(h++lt1) lt' #a #b fs_r_f fs_x' x f1;
            eliminate exists (fs_r:fs_val b). b ∋ ((h++lt1)++lt', fs_r, e') /\ fs_beh (fs_comp_bind fs_x' (fun x' -> fs_r_f x')) (h++lt1) lt' fs_r
              returns exists (fs_r:fs_val b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r with _. begin
            assert (fs_e == fs_comp_bind fs_f' (fun f' -> fs_comp_bind fs_x' (fun x' -> f' x'))) by (
              norm [delta_only [`%fs_ocomp_app;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_app_oval_oval]];
              simplify_stack_ops ();
              trefl ());
            lem_fs_beh_bind fs_f' h lt1 fs_r_f (fun f' -> fs_comp_bind fs_x' (fun x' -> f' x')) lt' fs_r
            end
            end)
          end
        end
      end
    end

let compat_ocomp_lambda #g (#t1:qType) (#t2:qType) (#preBody:spec_env (extend t1 g))
  (fs_body:fs_ocomp (extend t1 g) t2 preBody)
  (body:exp)
  : Lemma
    (requires fs_body ⊒ body)
    (ensures fs_ocomp_lambda fs_body ⊒ (ELam body))
  =
  compat_oval_lambda_ocomp #g #t1 #preBody #t2 fs_body body;
  compat_ocomp_return (fs_oval_lambda_ocomp fs_body) (ELam body)

let compat_ocomp_inl #g (t1 t2:qType) (#preP:spec_env g) (fs_e:fs_ocomp g t1 preP) (e:exp)
  : Lemma
    (requires fs_e ⊒ e)
    (ensures fs_ocomp_fmap #g #t1 #(t1 ^+ t2) fs_e Inl ⊒ (EInl e)) = admit ()
  (*lem_fv_in_env_inl g e;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(∽) h` s /\ (spec_env_bind #g #t1 preP (fun fsG -> (fun x -> (fun _ -> True)) (hd fsG) (tail fsG))) fsG) ==> (t1 ^+ t2) ⫄ (h, (fs_ocomp_fmap #g #t1 #(t1 ^+ t2) fs_e Inl) fsG, gsubst s (EInl e)) with begin
    introduce _ ==> _ with _. begin
      let fs_e' : fs_comp t1 = fs_e fsG in
      let fs_ex = fs_comp_bind #t1 #(t1 ^+ t2) fs_e' (fun e' -> return (Inl #(fs_val t1) #(fs_val t2) e')) in
      assert (fs_ex == (fs_ocomp_fmap #g #t1 #(t1 ^+ t2) fs_e Inl) fsG) by (
        norm [delta_only [`%fs_ocomp_fmap;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val]];
        simplify_stack_ops ();
        trefl ());
      let ex = EInl (gsubst s e) in
      assert (gsubst s (EInl e) == ex) by (trefl ());
      let EInl e = ex in
      introduce fsG `(∽) h` s ==> (t1 ^+ t2) ⫄ (h, fs_ex, ex) with _. begin
        introduce forall lt (ex':closed_exp). e_beh ex ex' h lt ==> (exists (fs_r:fs_val (t1 ^+ t2)). (t1 ^+ t2) ∋ (h++lt, fs_r, ex') /\ fs_beh fs_ex h lt fs_r) with begin
          introduce e_beh ex ex' h lt ==> (exists (fs_r:fs_val (t1 ^+ t2)). (t1 ^+ t2) ∋ (h++lt, fs_r, ex') /\ fs_beh fs_ex h lt fs_r) with _. begin
            lem_shift_type_value_environments h fsG s;
            bind_squash (steps ex ex' h lt) (fun sts1 ->
              lem_forall_values_are_values_prod t1 h;
              indexed_safety_comp fs_e' e h;
              let (e12', (| lt12, lt_f |)) = destruct_steps_einl e ex' h lt sts1 in
              trans_history h lt12 lt_f;
              lem_value_is_irred e12';
              lem_value_is_irred (EInl e12');
              assert (t1 ⫄ (h, fs_e', e));
              eliminate forall lt12 e12'. e_beh e e12' h lt12 ==> (exists (fs_r_e12:fs_val t1). t1 ∋ (h++lt12, fs_r_e12, e12') /\ fs_beh fs_e' h lt12 fs_r_e12) with lt12 e12';
              eliminate exists (fs_r_e12:fs_val t1). t1 ∋ (h++lt12, fs_r_e12, e12') /\ fs_beh fs_e' h lt12 fs_r_e12
                returns exists (fs_r:fs_val (t1 ^+ t2)). (t1 ^+ t2) ∋ (h++lt, fs_r, ex') /\ fs_beh fs_ex h lt fs_r with _. begin
              lem_destruct_steps_einl e12' ex' (h++lt12) lt_f;
              trans_history h lt12 [];
              lem_fs_beh_return #(t1 ^+ t2) (Inl #(fs_val t1) #(fs_val t2) fs_r_e12) (h++lt12);
              assert (fs_beh #(t1 ^+ t2) ((fun e' -> (return (Inl #(fs_val t1) #(fs_val t2) e'))) fs_r_e12) (h++lt12) [] (Inl #(fs_val t1) #(fs_val t2) fs_r_e12));
              lem_fs_beh_bind #t1 #(t1 ^+ t2) fs_e' h lt12 fs_r_e12 (fun e' -> (return (Inl #(fs_val t1) #(fs_val t2) e'))) [] (Inl #(fs_val t1) #(fs_val t2) fs_r_e12);
              unit_l lt12
            end)
          end
        end
      end
    end
  end*)

let compat_ocomp_inr #g (t1 t2:qType) #preP (fs_e:fs_ocomp g t2 preP) (e:exp)
  : Lemma
    (requires fs_e ⊒ e)
    (ensures fs_ocomp_fmap #g #t2 #(t1 ^+ t2) fs_e Inr ⊒ (EInr e)) = admit ()
  (*lem_fv_in_env_inr g e;
  introduce forall b' (s:gsub g b') fsG h. fsG `(∽) h` s ==> (t1 ^+ t2) ⫄ (h, (fs_ocomp_fmap #g #t2 #(t1 ^+ t2) fs_e Inr) fsG, gsubst s (EInr e)) with begin
    introduce _ ==> _ with _. begin
      let fs_e' : fs_comp t2 = fs_e fsG in
      let fs_ex = fs_comp_bind #t2 #(t1 ^+ t2) fs_e' (fun e' -> return (Inr #(fs_val t1) #(fs_val t2) e')) in
      assert (fs_ex == (fs_ocomp_fmap #g #t2 #(t1 ^+ t2) fs_e Inr) fsG) by (trefl ());
      let ex = EInr (gsubst s e) in
      assert (gsubst s (EInr e) == ex) by (trefl ());
      let EInr e = ex in
      introduce fsG `(∽) h` s ==> (t1 ^+ t2) ⫄ (h, fs_ex, ex) with _. begin
        introduce forall lt (ex':closed_exp). e_beh ex ex' h lt ==> (exists (fs_r:fs_val (t1 ^+ t2)). (t1 ^+ t2) ∋ (h++lt, fs_r, ex') /\ fs_beh fs_ex h lt fs_r) with begin
          introduce e_beh ex ex' h lt ==> (exists (fs_r:fs_val (t1 ^+ t2)). (t1 ^+ t2) ∋ (h++lt, fs_r, ex') /\ fs_beh fs_ex h lt fs_r) with _. begin
            lem_shift_type_value_environments h fsG s;
            bind_squash (steps ex ex' h lt) (fun sts1 ->
              lem_forall_values_are_values_prod t2 h;
              indexed_safety_comp fs_e' e h;
              let (e12', (| lt12, lt_f |)) = destruct_steps_einr e ex' h lt sts1 in
              trans_history h lt12 lt_f;
              lem_value_is_irred e12';
              lem_value_is_irred (EInr e12');
              assert (t2 ⫄ (h, fs_e', e));
              eliminate forall lt12 e12'. e_beh e e12' h lt12 ==> (exists (fs_r_e12:fs_val t2). t2 ∋ (h++lt12, fs_r_e12, e12') /\ fs_beh fs_e' h lt12 fs_r_e12) with lt12 e12';
              eliminate exists (fs_r_e12:fs_val t2). t2 ∋ (h++lt12, fs_r_e12, e12') /\ fs_beh fs_e' h lt12 fs_r_e12
                returns exists (fs_r:fs_val (t1 ^+ t2)). (t1 ^+ t2) ∋ (h++lt, fs_r, ex') /\ fs_beh fs_ex h lt fs_r with _. begin
              lem_destruct_steps_einr e12' ex' (h++lt12) lt_f;
              trans_history h lt12 [];
              lem_fs_beh_return #(t1 ^+ t2) (Inr #(fs_val t1) #(fs_val t2) fs_r_e12) (h++lt12);
              assert (fs_beh #(t1 ^+ t2) ((fun e' -> (return (Inr #(fs_val t1) #(fs_val t2) e'))) fs_r_e12) (h++lt12) [] (Inr #(fs_val t1) #(fs_val t2) fs_r_e12));
              lem_fs_beh_bind #t2 #(t1 ^+ t2) fs_e' h lt12 fs_r_e12 (fun e' -> (return (Inr #(fs_val t1) #(fs_val t2) e'))) [] (Inr #(fs_val t1) #(fs_val t2) fs_r_e12);
              unit_l lt12
            end)
          end
        end
      end
    end
  end*)

#push-options "--z3rlimit 64 --fuel 1 --ifuel 0"
let compat_ocomp_pair #g
  (#t1 #t2:qType) #preX #preY
  (fs_e1:fs_ocomp g t1 preX) (fs_e2:fs_ocomp g t2 preY)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊒ e1 /\ fs_e2 ⊒ e2)
    (ensures fs_ocomp_pair fs_e1 fs_e2 ⊒ EPair e1 e2) =
  lem_fv_in_env_pair g e1 e2;
  let t = (t1 ^* t2) in
  introduce forall b' (s:gsub g b') fsG h. (fsG `(∽) h` s /\ (spec_env_bind' #g #t1 preX (fun x' -> spec_env_bind' #g #t2 preY (fun y' -> spec_env_return_comp #g #(t1 ^* t2) (io_return (fs_val_pair x' y'))))) fsG) ==> t ⫄ (h, fs_ocomp_pair fs_e1 fs_e2 fsG, gsubst s (EPair e1 e2)) with begin
    introduce _ ==> _ with _. begin
      assert (preX fsG);
      let fs_e1' : fs_comp t1 = fs_e1 fsG in
      let fs_e2' () : Pure (fs_comp t2) (requires preY fsG) (ensures (fun _ -> True)) = fs_e2 fsG in
      let fs_e () : Pure (fs_comp t)
        (requires (preX fsG /\ preY fsG))
        (ensures (fun _ -> True))
        = fs_comp_bind fs_e1' (fun e1' -> fs_comp_bind #t2 #(t1 ^* t2) (fs_e2' ()) (fun e2' -> return (e1', e2'))) in
      let e = EPair (gsubst s e1) (gsubst s e2) in
      assert (gsubst s (EPair e1 e2) == e) by (trefl ());
      let EPair e1 e2 = e in
      introduce forall lt (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:fs_val t). t ∋ (h++lt, fs_r, e') /\ fs_beh (fs_ocomp_pair fs_e1 fs_e2 fsG) h lt fs_r) with begin
        introduce e_beh e e' h lt ==> (exists (fs_r:fs_val t). t ∋ (h++lt, fs_r, e') /\ fs_beh (fs_ocomp_pair fs_e1 fs_e2 fsG) h lt fs_r) with _. begin
          bind_squash (steps e e' h lt) (fun sts1 ->
            lem_forall_values_are_values_prod t1 h;
            lem_shift_type_value_environments h fsG s;
            assert (t1 ⫄ (h, fs_e1', e1));
            indexed_safety_comp fs_e1' e1 h;
            let (e1', (| lt1, lt' |)) = destruct_steps_epair_e1 e1 e2 e' h lt sts1 in
            eliminate forall lt1 e1'. e_beh e1 e1' h lt1 ==> (exists (fs_r_e1:fs_val t1). t1 ∋ (h++lt1, fs_r_e1, e1') /\ fs_beh fs_e1' h lt1 fs_r_e1) with lt1 e1';
            lem_value_is_irred e1';
            eliminate exists (fs_r_e1:fs_val t1). t1 ∋ (h++lt1, fs_r_e1, e1') /\ fs_beh fs_e1' h lt1 fs_r_e1
              returns exists (fs_r:fs_val t). t ∋ (h++lt, fs_r, e') /\ fs_beh (fs_ocomp_pair fs_e1 fs_e2 fsG) h lt fs_r with _. begin
            lem_values_are_expressions t1 (h++lt1) fs_r_e1 e1';
            trans_history h lt1 lt';
            eliminate forall (lt:local_trace h). fsG `(∽) h` s ==> fsG `(∽) (h++lt)` s with lt1;
            lem_shift_type_value_environments (h++lt1) fsG s;
            assert (spec_env_bind' #g #t2 preY (fun y' -> spec_env_return_comp #g #(t1 ^* t2) (io_return (fs_val_pair fs_r_e1 y'))) fsG);
            assert (preY fsG);
            assert (t2 ⫄ (h++lt1, fs_e2' (), e2));
            lem_forall_values_are_values_prod t2 (h++lt1);
            bind_squash (steps (EPair e1' e2) e' (h++lt1) lt') (fun sts2 ->
              indexed_safety_comp (fs_e2' ()) e2 (h++lt1);
              let (e2', (| lt2, lt'' |)) = destruct_steps_epair_e2 e1' e2 e' (h++lt1) lt' sts2 in
              trans_history h lt1 lt2;
              eliminate forall lt2 e2'. e_beh e2 e2' (h++lt1) lt2 ==> (exists (fs_r_e2:fs_val t2). t2 ∋ ((h++lt1)++lt2, fs_r_e2, e2') /\ fs_beh (fs_e2' ()) (h++lt1) lt2 fs_r_e2) with lt2 e2';
              lem_value_is_irred e2';
              eliminate exists (fs_r_e2:fs_val t2). t2 ∋ ((h++lt1)++lt2, fs_r_e2, e2') /\ fs_beh (fs_e2' ()) (h++lt1) lt2 fs_r_e2
                returns exists (fs_r:fs_val t). t ∋ (h++lt, fs_r, e') /\ fs_beh (fs_ocomp_pair fs_e1 fs_e2 fsG) h lt fs_r with _. begin
              let fs_e_bound = fs_e () in
              assert (fs_e_bound == fs_ocomp_pair fs_e1 fs_e2 fsG) by (
                norm [delta_only [`%fs_ocomp_pair;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val;`%fs_val_pair]];
                simplify_stack_ops ();
                trefl ());
              lem_fs_beh_return #(t1 ^* t2) (fs_r_e1, fs_r_e2) ((h++lt1)++lt2);
              lem_fs_beh_bind #t2 #(t1 ^* t2) (fs_e2' ()) (h++lt1) lt2 fs_r_e2 (fun e2' -> return (fs_r_e1, e2')) [] (fs_r_e1, fs_r_e2);
              unit_l lt2;
              lem_fs_beh_bind #t1 #(t1 ^* t2) fs_e1' h lt1 fs_r_e1 (fun e1' -> (fs_comp_bind #t2 #(t1 ^* t2) (fs_e2' ()) (fun e2' -> return (e1', e2')))) lt2 (fs_r_e1, fs_r_e2);
              lem_destruct_steps_epair e1' e2' e' ((h++lt1)++lt2) lt'';
              unit_l lt2;
              val_type_closed_under_history_extension t1 (h++lt1) (fst #(fs_val t1) #(fs_val t2) (fs_r_e1, fs_r_e2)) e1';
              assert (t1 ∋ (h++lt, fst #(fs_val t1) #(fs_val t2) (fs_r_e1, fs_r_e2), e1'));
              assert (t2 ∋ (h++lt, snd #(fs_val t1) #(fs_val t2) (fs_r_e1, fs_r_e2), e2'))
            end)
          end)
        end
      end
    end
  end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
private let helper_compat_ocomp_string_eq_inner
  (fs_e1':fs_comp qString) (fs_e2':fs_comp qString)
  (h:history)
  (lt1:local_trace h) (lt2:local_trace (h++lt1)) (lt'':local_trace ((h++lt1)++lt2))
  (s1:string) (s2:string) (e':closed_exp)
  (fs_r_e1:fs_val qString) (fs_r_e2:fs_val qString)
  (lt:local_trace h)
  (fs_e:fs_comp qBool)
  (sts3:steps (EStringEq (EString s1) (EString s2)) e' ((h++lt1)++lt2) lt'')
  : Lemma
    (requires
      fs_e == fs_comp_bind fs_e1' (fun x' -> fs_comp_bind #qString #qBool fs_e2' (fun y' -> return (x' = y'))) /\
      lt == lt1 @ lt2 @ lt'' /\
      fs_beh fs_e1' h lt1 fs_r_e1 /\
      qString ∋ (h++lt1, fs_r_e1, EString s1) /\
      fs_beh fs_e2' (h++lt1) lt2 fs_r_e2 /\
      qString ∋ ((h++lt1)++lt2, fs_r_e2, EString s2) /\
      indexed_irred e' (((h++lt1)++lt2)++lt''))
    (ensures exists (fs_r:fs_val qBool). qBool ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) =
  match sts3 with
  | SRefl _ _ ->
    let _ : step (EStringEq (EString s1) (EString s2)) (if s1 = s2 then ETrue else EFalse) ((h++lt1)++lt2) None = StringEqReturn s1 s2 ((h++lt1)++lt2) in
    false_elim ()
  | STrans step_seq step_rest ->
    match step_seq with
    | StringEqReturn _ _ _ ->
      lem_value_is_irred (if s1 = s2 then ETrue else EFalse);
      lem_irred_implies_srefl_steps step_rest;
      lem_fs_beh_return #qBool (fs_r_e1 = fs_r_e2) ((h++lt1)++lt2);
      lem_fs_beh_bind #qString #qBool fs_e2' (h++lt1) lt2 fs_r_e2 (fun y' -> return (fs_r_e1 = y')) [] (fs_r_e1 = fs_r_e2);
      unit_l lt2;
      lem_fs_beh_bind #qString #qBool fs_e1' h lt1 fs_r_e1 (fun x' -> (fs_comp_bind #qString #qBool fs_e2' (fun y' -> return (x' = y')))) lt2 (fs_r_e1 = fs_r_e2);
      unit_l lt2
    | StringEqLeft _ step_e1 ->
      lem_value_is_irred (EString s1);
      false_elim ()
    | StringEqRight _ step_e2 ->
      lem_value_is_irred (EString s2);
      false_elim ()
#pop-options

#push-options "--z3rlimit 64 --fuel 1 --ifuel 0 --split_queries always"
let compat_ocomp_string_eq #g #preX #preY
  (fs_e1:fs_ocomp g qString preX) (fs_e2:fs_ocomp g qString preY)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊒ e1 /\ fs_e2 ⊒ e2)
    (ensures fs_ocomp_string_eq fs_e1 fs_e2 ⊒ EStringEq e1 e2) =
  lem_fv_in_env_string_eq g e1 e2;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(∽) h` s /\ (spec_env_bind' #g #qString preX (fun x' -> spec_env_bind' #g #qString preY (fun y' -> spec_env_return_comp #g #qBool (io_return (x' = y'))))) fsG) ==> qBool ⫄ (h, fs_ocomp_string_eq fs_e1 fs_e2 fsG, gsubst s (EStringEq e1 e2)) with begin
    introduce _ ==> _ with _. begin
      assert (preX fsG);
      let fs_e1' : fs_comp qString = fs_e1 fsG in
      let fs_e2' () : Pure (fs_comp qString) (requires preY fsG) (ensures (fun _ -> True)) = fs_e2 fsG in
      let fs_e () : Pure (fs_comp qBool)
        (requires (preX fsG /\ preY fsG))
        (ensures (fun _ -> True))
        = fs_comp_bind fs_e1' (fun x' -> fs_comp_bind #qString #qBool (fs_e2' ()) (fun y' -> return (x' = y'))) in
      let e = EStringEq (gsubst s e1) (gsubst s e2) in
      assert (gsubst s (EStringEq e1 e2) == e) by (trefl ());
      let EStringEq e1 e2 = e in
      introduce forall lt (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:fs_val qBool). qBool ∋ (h++lt, fs_r, e') /\ fs_beh (fs_ocomp_string_eq fs_e1 fs_e2 fsG) h lt fs_r) with begin
        introduce e_beh e e' h lt ==> (exists (fs_r:fs_val qBool). qBool ∋ (h++lt, fs_r, e') /\ fs_beh (fs_ocomp_string_eq fs_e1 fs_e2 fsG) h lt fs_r) with _. begin
          bind_squash (steps e e' h lt) (fun sts1 ->
            lem_forall_values_are_values_prod qString h;
            lem_shift_type_value_environments h fsG s;
            assert (qString ⫄ (h, fs_e1', e1));
            indexed_safety_comp fs_e1' e1 h;
            let (e1v, (| lt1, lt' |)) = destruct_steps_estringeq_e1 e1 e2 e' h lt sts1 in
            eliminate forall lt1 e1'. e_beh e1 e1' h lt1 ==> (exists (fs_r_e1:fs_val qString). qString ∋ (h++lt1, fs_r_e1, e1') /\ fs_beh fs_e1' h lt1 fs_r_e1) with lt1 e1v;
            lem_value_is_irred e1v;
            eliminate exists (fs_r_e1:fs_val qString). qString ∋ (h++lt1, fs_r_e1, e1v) /\ fs_beh fs_e1' h lt1 fs_r_e1
              returns exists (fs_r:fs_val qBool). qBool ∋ (h++lt, fs_r, e') /\ fs_beh (fs_ocomp_string_eq fs_e1 fs_e2 fsG) h lt fs_r with _. begin
            lem_values_are_expressions qString (h++lt1) fs_r_e1 e1v;
            let EString s1 = e1v in
            trans_history h lt1 lt';
            eliminate forall (lt:local_trace h). fsG `(∽) h` s ==> fsG `(∽) (h++lt)` s with lt1;
            lem_shift_type_value_environments (h++lt1) fsG s;
            assert (spec_env_bind' #g #qString preY (fun y' -> spec_env_return_comp #g #qBool (io_return (fs_r_e1 = y'))) fsG);
            assert (preY fsG);
            assert (qString ⫄ (h++lt1, fs_e2' (), e2));
            lem_forall_values_are_values_prod qString (h++lt1);
            bind_squash (steps (EStringEq e1v e2) e' (h++lt1) lt') (fun sts2 ->
              indexed_safety_comp (fs_e2' ()) e2 (h++lt1);
              let (e2v, (| lt2, lt'' |)) = destruct_steps_estringeq_e2 e1v e2 e' (h++lt1) lt' sts2 in
              trans_history h lt1 lt2;
              eliminate forall lt2 e2'. e_beh e2 e2' (h++lt1) lt2 ==> (exists (fs_r_e2:fs_val qString). qString ∋ ((h++lt1)++lt2, fs_r_e2, e2') /\ fs_beh (fs_e2' ()) (h++lt1) lt2 fs_r_e2) with lt2 e2v;
              lem_value_is_irred e2v;
              eliminate exists (fs_r_e2:fs_val qString). qString ∋ ((h++lt1)++lt2, fs_r_e2, e2v) /\ fs_beh (fs_e2' ()) (h++lt1) lt2 fs_r_e2
                returns exists (fs_r:fs_val qBool). qBool ∋ (h++lt, fs_r, e') /\ fs_beh (fs_ocomp_string_eq fs_e1 fs_e2 fsG) h lt fs_r with _. begin
              lem_values_are_expressions qString ((h++lt1)++lt2) fs_r_e2 e2v;
              let EString s2 = e2v in
              trans_history (h++lt1) lt2 lt'';
              let fs_e_bound = fs_e () in
              assert (fs_e_bound == fs_ocomp_string_eq fs_e1 fs_e2 fsG) by (
                norm [delta_only [`%fs_ocomp_string_eq;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val]];
                simplify_stack_ops ();
                trefl ());
              bind_squash (steps (EStringEq (EString s1) (EString s2)) e' ((h++lt1)++lt2) lt'') (fun sts3 ->
                helper_compat_ocomp_string_eq_inner fs_e1' (fs_e2' ()) h lt1 lt2 lt'' s1 s2 e' fs_r_e1 fs_r_e2 lt fs_e_bound sts3)
            end)
          end)
        end
      end
    end
  end
#pop-options

let compat_ocomp_fst #g
  (#t1 #t2:qType)
  #preP
  (fs_e12:fs_ocomp g (t1 ^* t2) preP)
  (e12:exp)
  : Lemma
    (requires fs_e12 ⊒ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures fs_ocomp_fmap fs_e12 fst ⊒ (EFst e12)) = admit ()
  (*lem_fv_in_env_fst g e12;
  introduce forall b' (s:gsub g b') fsG h. fsG `(∽) h` s ==> t1 ⫄ (h, (fs_ocomp_fmap #g #(t1 ^* t2) #t1 fs_e12 fst) fsG, gsubst s (EFst e12)) with begin
    introduce _ ==> _ with _. begin
      let fs_e12' : fs_comp (t1 ^* t2) = fs_e12 fsG in
      let fs_e = fs_comp_bind #(t1 ^* t2) #t1 fs_e12' (fun e12' -> return (fst #(fs_val t1) #(fs_val t2) e12')) in
      assert (fs_e == (fs_ocomp_fmap #g #(t1 ^* t2) #t1 fs_e12 fst) fsG) by (
        norm [delta_only [`%fs_ocomp_fmap;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val]];
        simplify_stack_ops ();
        trefl ());
      let e = EFst (gsubst s e12) in
      assert (gsubst s (EFst e12) == e) by (trefl ());
      let EFst e12 = e in
      introduce fsG `(∽) h` s ==> t1 ⫄ (h, fs_e, e) with _. begin
        introduce forall lt (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:fs_val t1). t1 ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
          introduce e_beh e e' h lt ==> (exists (fs_r:fs_val t1). t1 ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
            lem_shift_type_value_environments h fsG s;
            bind_squash (steps e e' h lt) (fun sts1 ->
              lem_forall_values_are_values_prod (t1 ^* t2) h;
              let t1_typ = type_quotation_to_typ (get_rel t1) in
              let t2_typ = type_quotation_to_typ (get_rel t2) in
              let (e12', (| lt12, lt_f |)) = destruct_steps_epair_fst e12 e' h lt sts1 t1_typ t2_typ in
              trans_history h lt12 lt_f;
              lem_value_is_irred e12';
              let EPair e1 e2 = e12' in
              lem_value_is_irred e1;
              lem_value_is_irred e2;
              assert ((t1 ^* t2) ⫄ (h, fs_e12', e12));
              assert (e_beh e12 e12' h lt12);
              eliminate forall (lt':local_trace h) (e'':closed_exp). e_beh e12 e'' h lt' ==>
                (exists (fs_r:fs_val (t1 ^* t2)). (t1 ^* t2) ∋ (h++lt', fs_r, e'') /\ fs_beh fs_e12' h lt' fs_r) with lt12 e12';
              eliminate exists (fs_r_e12:fs_val (t1 ^* t2)). (t1 ^* t2) ∋ (h++lt12, fs_r_e12, e12') /\ fs_beh fs_e12' h lt12 fs_r_e12
                returns exists (fs_r:fs_val t1). t1 ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r with _. begin
              lem_destruct_steps_epair_fst e1 e2 e' (h++lt12) lt_f;
              trans_history h lt12 [];
              lem_fs_beh_return #t1 (fst #(fs_val t1) #(fs_val t2) fs_r_e12) (h++lt12);
              assert (fs_beh #t1 ((fun e12' -> (return (fst #(fs_val t1) #(fs_val t2) e12'))) fs_r_e12) (h++lt12) [] (fst #(fs_val t1) #(fs_val t2) fs_r_e12));
              lem_fs_beh_bind #(t1 ^* t2) #t1 fs_e12' h lt12 fs_r_e12 (fun e' -> (return (fst #(fs_val t1) #(fs_val t2) e'))) [] (fst #(fs_val t1) #(fs_val t2) fs_r_e12);
              unit_l lt12
            end)
          end
        end
      end
    end
  end*)

#push-options "--z3refresh --fuel 4 --z3rlimit 20"
let compat_ocomp_snd #g (#t1 #t2:qType) #preP (fs_e12:fs_ocomp g (t1 ^* t2) preP) (e12:exp)
  : Lemma
    (requires fs_e12 ⊒ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures fs_ocomp_fmap fs_e12 snd ⊒ (ESnd e12)) = admit ()
  (*lem_fv_in_env_snd g e12;
  introduce forall b' (s:gsub g b') fsG h. fsG `(∽) h` s ==> t2 ⫄ (h, (fs_ocomp_fmap #g #(t1 ^* t2) #t2 fs_e12 snd) fsG, gsubst s (ESnd e12)) with begin
  introduce _ ==> _ with _. begin
      let fs_e12' : fs_comp (t1 ^* t2) = fs_e12 fsG in
      let fs_e = fs_comp_bind #(t1 ^* t2) #t2 fs_e12' (fun e12' -> return (snd #(fs_val t1) #(fs_val t2) e12')) in
      assert (fs_e == (fs_ocomp_fmap #g #(t1 ^* t2) #t2 fs_e12 snd) fsG) by (
        norm [delta_only [`%fs_ocomp_fmap;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val]];
        simplify_stack_ops ();
        trefl ());
      let e = ESnd (gsubst s e12) in
      assert (gsubst s (ESnd e12) == e);
      let ESnd e12 = e in
      introduce fsG `(∽) h` s ==> t2 ⫄ (h, fs_e, e) with _. begin
        introduce forall lt (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:fs_val t2). t2 ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
          introduce e_beh e e' h lt ==> (exists (fs_r:fs_val t2). t2 ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
            lem_shift_type_value_environments h fsG s;
            bind_squash (steps e e' h lt) (fun sts1 ->
              lem_forall_values_are_values_prod (t1 ^* t2) h;
              let t1_typ = type_quotation_to_typ (get_rel t1) in
              let t2_typ = type_quotation_to_typ (get_rel t2) in
              let (e12', (| lt12, lt_f |)) = destruct_steps_epair_snd e12 e' h lt sts1 t1_typ t2_typ in
              trans_history h lt12 lt_f;
              lem_value_is_irred e12';
              let EPair e1 e2 = e12' in
              lem_value_is_irred e1;
              lem_value_is_irred e2;
              assert ((t1 ^* t2) ⫄ (h, fs_e12', e12));
              assert (e_beh e12 e12' h lt12);
              eliminate forall (lt':local_trace h) (e'':closed_exp). e_beh e12 e'' h lt' ==> (exists (fs_r:fs_val (t1 ^* t2)). (t1 ^* t2) ∋ (h++lt', fs_r, e'') /\ fs_beh fs_e12' h lt' fs_r) with lt12 e12';
              eliminate exists (fs_r_e12:fs_val (t1 ^* t2)). (t1 ^* t2) ∋ (h++lt12, fs_r_e12, e12') /\ fs_beh fs_e12' h lt12 fs_r_e12
                returns exists (fs_r:fs_val t2). t2 ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r with _. begin
              assert (e12' == EPair e1 e2);
              assert (t2 ∋ (h++lt12, snd #(fs_val t1) #(fs_val t2) fs_r_e12, e2));
              lem_destruct_steps_epair_snd e1 e2 e' (h++lt12) lt_f;
              trans_history h lt12 [];
              lem_fs_beh_return #t2 (snd #(fs_val t1) #(fs_val t2) fs_r_e12) (h++lt12);
              assert (fs_beh #t2 ((fun e12' -> (return (snd #(fs_val t1) #(fs_val t2) e12'))) fs_r_e12) (h++lt12) [] (snd #(fs_val t1) #(fs_val t2) fs_r_e12));
              lem_fs_beh_bind #(t1 ^* t2) #t2 fs_e12' h lt12 fs_r_e12 (fun e' -> (return (snd #(fs_val t1) #(fs_val t2) e'))) [] (snd #(fs_val t1) #(fs_val t2) fs_r_e12);
              unit_l lt12
            end)
          end
        end
      end
    end
  end*)
#pop-options

let helper_lemma_compat_ocomp_case #g #a #b (#preBody:spec_env (extend a g))
  (fs_e:fs_ocomp (extend a g) b preBody)
  (e:exp)
  #bo (s:gsub g bo) (fsG:eval_env g) (h:history)
  : Lemma
    (requires fs_e ⊒ e /\ fsG `(∽) h` s /\ fv_in_env g (ELam e) /\ (spec_env_lambda_tot preBody) fsG)
    (ensures (a ^->!@ b) ⊇ (h, fs_oval_lambda_ocomp fs_e fsG, gsubst s (ELam e)))
  =
  compat_oval_lambda_ocomp fs_e e;
  assert (fs_oval_lambda_ocomp fs_e ⊐ (ELam e));
  assert_norm (superset_oval #g (a ^->!@ b) (fs_oval_lambda_ocomp fs_e) (ELam e) ==
    (fv_in_env g (ELam e) /\
    (forall bo (s:gsub g bo) (fsG:eval_env g) (h:history).
      (fsG `(∽) h` s /\ (spec_env_lambda_tot preBody) fsG) ==>
        (a ^->!@ b) ⊇ (h, fs_oval_lambda_ocomp fs_e fsG, gsubst s (ELam e)))));
  eliminate forall bo (s:gsub g bo) (fsG:eval_env g) (h:history).
    (fsG `(∽) h` s /\ (spec_env_lambda_tot preBody) fsG) ==>
      (a ^->!@ b) ⊇ (h, fs_oval_lambda_ocomp fs_e fsG, gsubst s (ELam e))
  with bo s fsG h

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2 --split_queries always"
let compat_ocomp_case #g (#a #b #c:qType) #preCond
  (fs_cond:fs_ocomp g (a ^+ b) preCond)
  (#preInlc:spec_env (extend a g))
  (fs_inlc:fs_ocomp (extend a g) c preInlc)
  (#preInrc:spec_env (extend b g))
  (fs_inrc:fs_ocomp (extend b g) c preInrc)
  (cond inlc inrc:exp)
  : Lemma
    (requires fs_cond ⊒ cond /\ fs_inlc ⊒ inlc /\ fs_inrc ⊒ inrc)
    (ensures (fs_ocomp_case fs_cond fs_inlc fs_inrc) ⊒ (ECase cond inlc inrc)) =
  lem_fv_in_env_case g a b cond inlc inrc;
  lem_fv_in_env_lam g a inlc;
  lem_fv_in_env_lam g b inrc;
  compat_ocomp_lambda fs_inlc inlc;
  compat_ocomp_lambda fs_inrc inrc;
  compat_oval_lambda_ocomp fs_inlc inlc;
  compat_oval_lambda_ocomp fs_inrc inrc;
  introduce forall b' (s:gsub g b') fsG h.
    (fsG `(∽) h` s /\
     (spec_env_bind' #g #(a ^+ b) preCond
        (fun cond' -> fun fsG -> match cond' with
                             | Inl x -> preInlc (stack fsG x)
                             | Inr x -> preInrc (stack fsG x))) fsG) ==>
    c ⫄ (h, fs_ocomp_case fs_cond fs_inlc fs_inrc fsG, gsubst s (ECase cond inlc inrc))
  with begin
    introduce _ ==> _ with _. begin
      assert (preCond fsG);
      assert (forall (cond':fs_val (a ^+ b)).
        (match cond' with | Inl x -> preInlc (stack fsG x) | Inr x -> preInrc (stack fsG x)));
      introduce forall (x:fs_val a). preInlc (stack fsG x) with begin
        eliminate forall (cond':fs_val (a ^+ b)).
          (match cond' with | Inl x -> preInlc (stack fsG x) | Inr x -> preInrc (stack fsG x))
        with (Inl x <: fs_val (a ^+ b))
      end;
      introduce forall (x:fs_val b). preInrc (stack fsG x) with begin
        eliminate forall (cond':fs_val (a ^+ b)).
          (match cond' with | Inl x -> preInlc (stack fsG x) | Inr x -> preInrc (stack fsG x))
        with (Inr x <: fs_val (a ^+ b))
      end;
      assert ((spec_env_lambda_tot preInlc) fsG);
      assert ((spec_env_lambda_tot preInrc) fsG);
      let fs_sc () : Pure (fs_comp (a ^+ b)) (requires preCond fsG) (ensures (fun _ -> True)) = fs_cond fsG in
      let fs_il : fs_val (a ^->!@ c) = fun x -> fs_inlc (stack fsG x) in
      let fs_ir : fs_val (b ^->!@ c) = fun x -> fs_inrc (stack fsG x) in
      let fs_e = fs_comp_bind (fs_sc ()) (fun fs_sc' -> fs_ocomp_case_val fs_sc' fs_inlc fs_inrc fsG) in
      assert (fs_e == fs_ocomp_case fs_cond fs_inlc fs_inrc fsG) by (
        norm [delta_only [`%fs_ocomp_case;`%fs_ocomp_bind';`%fs_ocomp_bind]];
        simplify_stack_ops ();
        trefl ());
      let e = ECase (gsubst s cond) (LambdaIO.subst (LambdaIO.sub_elam s) inlc) (LambdaIO.subst (LambdaIO.sub_elam s) inrc) in
      assert (gsubst s (ECase cond inlc inrc) == e) by (trefl ());
      let ECase e_sc e_il e_ir = e in
      introduce (fsG `(∽) h` s /\
        (spec_env_bind' #g #(a ^+ b) preCond
          (fun cond' -> fun fsG -> match cond' with
                               | Inl x -> preInlc (stack fsG x)
                               | Inr x -> preInrc (stack fsG x))) fsG) ==>
        c ⫄ (h, fs_e, e) with _. begin
        introduce forall lt (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:fs_val c). c ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
          introduce e_beh e e' h lt ==> (exists (fs_r:fs_val c). c ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
            lem_shift_type_value_environments h fsG s;
            bind_squash (steps e e' h lt) (fun sts1 ->
              let a_typ = type_quotation_to_typ (get_rel a) in
              let b_typ = type_quotation_to_typ (get_rel b) in
              lem_forall_values_are_values_prod (a ^+ b) h;
              sem_expr_shape_comp (fs_sc ()) e_sc h;
              assert (indexed_sem_expr_shape (TSum a_typ b_typ) e_sc h);
              let (e_sc', (| lt1, lt2 |)) = destruct_steps_ecase e_sc e_il e_ir e' h lt sts1 a_typ b_typ in
              assert ((a ^+ b) ⫄ (h, fs_sc (), e_sc));
              eliminate forall lt1 e_sc'. e_beh e_sc e_sc' h lt1 ==> (exists (fs_r_cond:fs_val (a ^+ b)). (a ^+ b) ∋ (h++lt1, fs_r_cond, e_sc') /\ fs_beh (fs_sc ()) h lt1 fs_r_cond) with lt1 e_sc';
              lem_value_is_irred e_sc';
              trans_history h lt1 lt2;
              eliminate exists (fs_r_cond:fs_val (a ^+ b)). (a ^+ b) ∋ (h++lt1, fs_r_cond, e_sc') /\ fs_beh (fs_sc ()) h lt1 fs_r_cond
                returns exists (fs_r:fs_val c). c ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r with _. begin
              lem_values_are_expressions (a ^+ b) (h++lt1) fs_r_cond e_sc';
              let fs_r_comp : fs_comp c = fs_ocomp_case_val fs_r_cond fs_inlc fs_inrc fsG in
              (* Establish the Inl branch precondition *)
              introduce Inl? fs_r_cond ==>
                (forall (v:value). a ∋ (h++lt1, Inl?.v fs_r_cond, v) ==>
                                   c ⫄ (h++lt1, fs_r_comp, subst_beta v e_il)) with _. begin
                let prove_inl_branch () : Lemma
                  (requires Inl? fs_r_cond)
                  (ensures forall (v:value). a ∋ (h++lt1, Inl?.v fs_r_cond, v) ==>
                                             c ⫄ (h++lt1, fs_r_comp, subst_beta v e_il)) =
                  introduce forall (v:value). a ∋ (h++lt1, Inl?.v fs_r_cond, v) ==>
                                              c ⫄ (h++lt1, fs_r_comp, subst_beta v e_il) with begin
                    introduce _ ==> _ with _. begin
                      let s' = gsub_extend s a v in
                      let fsG' = stack fsG (Inl?.v fs_r_cond) in
                      assert ((fsG' `(∽) (h++lt1)` s' /\ preInlc fsG') ==>
                                c ⫄ (h++lt1, fs_inlc fsG', gsubst s' inlc));
                      lem_shift_type_value_environments h fsG s;
                      assert (fsG `(∽) (h++lt1)` s);
                      assert (a ∋ (h++lt1, Inl?.v fs_r_cond, v));
                      lem_values_are_values a (h++lt1) (Inl?.v fs_r_cond) v;
                      assert (stack fsG (Inl?.v fs_r_cond) `(∽) (h++lt1)` gsub_extend s a v);
                      assert (preInlc fsG');
                      assert (c ⫄ (h++lt1, fs_inlc fsG', gsubst s' inlc));
                      lem_substitution s a v inlc;
                      assert (subst_beta v e_il == gsubst s' inlc);
                      assert (fs_r_comp == fs_inlc fsG');
                      assert (c ⫄ (h++lt1, fs_r_comp, subst_beta v e_il))
                    end
                  end in
                prove_inl_branch ()
              end;
              (* Establish the Inr branch precondition *)
              introduce Inr? fs_r_cond ==>
                (forall (v:value). b ∋ (h++lt1, Inr?.v fs_r_cond, v) ==>
                                   c ⫄ (h++lt1, fs_r_comp, subst_beta v e_ir)) with _. begin
                let prove_inr_branch () : Lemma
                  (requires Inr? fs_r_cond)
                  (ensures forall (v:value). b ∋ (h++lt1, Inr?.v fs_r_cond, v) ==>
                                             c ⫄ (h++lt1, fs_r_comp, subst_beta v e_ir)) =
                  introduce forall (v:value). b ∋ (h++lt1, Inr?.v fs_r_cond, v) ==>
                                              c ⫄ (h++lt1, fs_r_comp, subst_beta v e_ir) with begin
                    introduce _ ==> _ with _. begin
                      let s' = gsub_extend s b v in
                      let fsG' = stack fsG (Inr?.v fs_r_cond) in
                      assert ((fsG' `(∽) (h++lt1)` s' /\ preInrc fsG') ==>
                                c ⫄ (h++lt1, fs_inrc fsG', gsubst s' inrc));
                      lem_shift_type_value_environments h fsG s;
                      assert (fsG `(∽) (h++lt1)` s);
                      assert (b ∋ (h++lt1, Inr?.v fs_r_cond, v));
                      lem_values_are_values b (h++lt1) (Inr?.v fs_r_cond) v;
                      assert (stack fsG (Inr?.v fs_r_cond) `(∽) (h++lt1)` gsub_extend s b v);
                      assert (preInrc fsG');
                      assert (c ⫄ (h++lt1, fs_inrc fsG', gsubst s' inrc));
                      lem_substitution s b v inrc;
                      assert (subst_beta v e_ir == gsubst s' inrc);
                      assert (fs_r_comp == fs_inrc fsG');
                      assert (c ⫄ (h++lt1, fs_r_comp, subst_beta v e_ir))
                    end
                  end in
                prove_inr_branch ()
              end;
              helper_compat_prod_case_val e' #(h++lt1) lt2 fs_r_cond fs_r_comp e_sc' e_il e_ir;
              eliminate exists (fs_r:fs_val c). c ∋ ((h++lt1)++lt2, fs_r, e') /\ fs_beh fs_r_comp (h++lt1) lt2 fs_r
                returns exists (fs_r:fs_val c). c ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r with _. begin
                lem_fs_beh_bind (fs_sc ()) h lt1 fs_r_cond (fun x -> fs_ocomp_case_val x fs_inlc fs_inrc fsG) lt2 fs_r
              end
            end)
          end
        end
      end
    end
  end
#pop-options

let compat_ocomp_call #g (op:io_ops) #preArgs (fs_arg:fs_ocomp g (q_io_args op) preArgs) (arg:exp)
  : Lemma
    (requires fs_arg ⊒ arg)
    (ensures fs_ocomp_call op fs_arg ⊒ ECall op arg) = admit ()
  (*lem_fv_in_env_call g op arg;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(∽) h` s /\ (spec_env_bind' #g #(q_io_args op) preArgs (fun a -> spec_env_return_comp #g #(q_io_res op) (fs_comp_call_val op a))) fsG) ==> (q_io_res op) ⫄ (h, (fs_ocomp_call op fs_arg) fsG, gsubst s (ECall op arg)) with begin
    introduce _ ==> _ with _. begin
      let fs_arg' : fs_comp (q_io_args op) = fs_arg fsG in
      let fs_e = fs_comp_bind #(q_io_args op) #(q_io_res op) fs_arg' (fun arg' -> fs_comp_call_val op arg') in
      assert (fs_e == (fs_ocomp_call op fs_arg) fsG) by (trefl ());
      let e = ECall op (gsubst s arg) in
      assert (gsubst s (ECall op arg) == e);
      let ECall _ arg = e in
      introduce fsG `(∽) h` s ==> (q_io_res op) ⫄ (h, fs_e, e) with _. begin
        introduce forall lt (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:fs_val (q_io_res op)). (q_io_res op) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
          introduce e_beh e e' h lt ==> (exists (fs_r:fs_val (q_io_res op)). (q_io_res op) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
            lem_shift_type_value_environments h fsG s;
            bind_squash (steps e e' h lt) (fun sts1 ->
              assert ((q_io_args op) ⫄ (h, fs_arg', arg));
              let (arg_val, (| lt1, lt' |)) = destruct_steps_ecall_arg_comp op arg e' h lt sts1 arg h [] fs_arg' in
              eliminate forall lt1 arg_val. e_beh arg arg_val h lt1 ==> (exists (fs_r_arg:fs_val (q_io_args op)). (q_io_args op) ∋ (h++lt1, fs_r_arg, arg_val) /\ fs_beh fs_arg' h lt1 fs_r_arg) with lt1 arg_val;
              lem_value_is_irred arg_val;
              eliminate exists (fs_r_arg:fs_val (q_io_args op)). (q_io_args op) ∋ (h++lt1, fs_r_arg, arg_val) /\ fs_beh fs_arg' h lt1 fs_r_arg
                returns exists (fs_r:fs_val (q_io_res op)). (q_io_res op) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r with _. begin
              lem_values_are_expressions (q_io_args op) (h++lt1) fs_r_arg arg_val;
              trans_history h lt1 lt';
              helper_compat_ocomp_call_oval op e' (h++lt1) lt' fs_r_arg arg_val;
              eliminate exists (fs_r:fs_val (q_io_res op)). (q_io_res op) ∋ ((h++lt1)++lt', fs_r, e') /\ fs_beh (fs_comp_call_val op fs_r_arg) (h++lt1) lt' fs_r
                returns exists (fs_r:fs_val (q_io_res op)). (q_io_res op) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r with _. begin
                lem_fs_beh_bind #(q_io_args op) #(q_io_res op) fs_arg' h lt1 fs_r_arg (fun x -> fs_comp_call_val op x) lt' fs_r
              end
            end)
          end
        end
      end
    end
  end*)
