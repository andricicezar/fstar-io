module LogRelSourceTarget.CompatibilityLemmas

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open QTyp
open IO
open Trace
open LogRelSourceTarget

let bind_squash (a #b:Type) (f:a -> GTot (squash b)) : Pure (squash b) (requires a) (ensures fun _ -> True) = 
  FStar.Squash.bind_squash #a () f

let equiv_oval_unit g : Lemma (fs_oval_return g qUnit () ⊏ EUnit) =
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> qUnit ⊆ (h, (), gsubst s EUnit) with begin
    introduce _ ==> _ with _. begin
      assert (qUnit ∈ (h, (), EUnit));
      lem_values_are_expressions qUnit h () EUnit
    end
  end

let equiv_oval_true g : Lemma (fs_oval_return g qBool true ⊏ ETrue) =
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> qBool ⊆ (h, true, gsubst s ETrue) with begin
    introduce _ ==> _ with _. begin
      assert (qBool ∈ (h, true, ETrue));
      lem_values_are_expressions qBool h true ETrue
    end
  end

let equiv_oval_false g : Lemma (fs_oval_return g qBool false ⊏ EFalse) =
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> qBool ⊆ (h, false, gsubst s EFalse) with begin
    introduce _ ==> _ with _. begin
      assert (qBool ∈ (h, false, EFalse));
      lem_values_are_expressions qBool h false EFalse
    end
  end

let equiv_oval_file_descr g fd : Lemma (fs_oval_return g qFileDescr fd ⊏ EFileDescr fd) =
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> qFileDescr ⊆ (h, fd, gsubst s (EFileDescr fd)) with begin
    introduce _ ==> _ with _. begin
      assert (qFileDescr ∈ (h, fd, (EFileDescr fd)));
      lem_values_are_expressions qFileDescr h fd (EFileDescr fd)
    end
  end

let equiv_oval_string g (str:string) : Lemma (fs_oval_return g qString str ⊏ EString str) =
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> qString ⊆ (h, str, gsubst s (EString str)) with begin
    introduce _ ==> _ with _. begin
      assert (qString ∈ (h, str, EString str));
      lem_values_are_expressions qString h str (EString str)
    end
  end

#push-options "--z3rlimit 10"
let helper_equiv_oval_string_eq_steps (h:history) (fs_e1:fs_val qString) (fs_e2:fs_val qString) (e1 e2:closed_exp) :
  Lemma
    (requires qString ⊆ (h, fs_e1, e1) /\
              qString ⊆ (h, fs_e2, e2))
    (ensures exists (e':closed_exp). e_beh (EStringEq e1 e2) e' h [] /\ qBool ∈ (h, (fs_e1 = fs_e2), e')) =
  eliminate exists (e1':closed_exp). e_beh e1 e1' h [] /\ qString ∈ (h, fs_e1, e1')
    returns exists (e':closed_exp). e_beh (EStringEq e1 e2) e' h [] /\ qBool ∈ (h, (fs_e1 = fs_e2), e') with _. begin
  eliminate exists (e2':closed_exp). e_beh e2 e2' h [] /\ qString ∈ (h, fs_e2, e2')
    returns exists (e':closed_exp). e_beh (EStringEq e1 e2) e' h [] /\ qBool ∈ (h, (fs_e1 = fs_e2), e') with _. begin
  let EString s1 = e1' in
  let EString s2 = e2' in
  lem_values_are_values qString h fs_e1 e1';
  lem_values_are_values qString h fs_e2 e2';
  lem_value_is_irred e1';
  lem_value_is_irred e2';
  let result = if s1 = s2 then ETrue else EFalse in
  let _ : step (EStringEq (EString s1) (EString s2)) result h None = StringEqReturn s1 s2 h in
  lem_step_implies_steps (EStringEq (EString s1) (EString s2)) result h None;
  lem_value_is_irred result;
  FStar.Squash.bind_squash #(steps e1 e1' h []) #(squash (exists (e':closed_exp). e_beh (EStringEq e1 e2) e' h [] /\ qBool ∈ (h, (fs_e1 = fs_e2), e'))) () (fun (sts1:steps e1 e1' h []) ->
  FStar.Squash.bind_squash #(steps e2 e2' h []) #(squash (exists (e':closed_exp). e_beh (EStringEq e1 e2) e' h [] /\ qBool ∈ (h, (fs_e1 = fs_e2), e'))) () (fun (sts2:steps e2 e2' h []) ->
  construct_steps_estringeq e1 e1' e2 e2' h [] [] sts1 sts2;
  lem_steps_transitive (EStringEq e1 e2) (EStringEq (EString s1) (EString s2)) result h [] [];
  assert (qBool ∈ (h, (fs_e1 = fs_e2), result))
  ))
  end
  end
#pop-options

let equiv_oval_string_eq #g
  (fs_e1:fs_oval g qString) (fs_e2:fs_oval g qString)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊏ e1 /\ fs_e2 ⊏ e2)
    (ensures fs_oval_eq_string fs_e1 fs_e2 ⊏ EStringEq e1 e2) =
  lem_fv_in_env_string_eq g e1 e2;
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> qBool ⊆ (h, (fs_e1 fsG = fs_e2 fsG), gsubst s (EStringEq e1 e2)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e2 = fs_e2 fsG in
    let fs_e = (fs_e1 = fs_e2) in
    let e = EStringEq (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EStringEq e1 e2) == e);
    let EStringEq e1 e2 = e in
    introduce fsG `(≍) h` s ==> qBool ⊆ (h, fs_e, e) with _. begin
      helper_equiv_oval_string_eq_steps h fs_e1 fs_e2 e1 e2
    end
  end

(** Used in backtranslation **)
let equiv_oval_var g (x:var{Some? (g x)}) : Lemma (fs_oval_var g x ⊏ EVar x) =
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> Some?.v (g x) ⊆ (h, index fsG x, gsubst s (EVar x)) with begin
    introduce _ ==> _ with _. begin
      assert (Some?.v (g x) ∈ (h, index fsG x, s x));
      lem_values_are_expressions (Some?.v (g x)) h (index fsG x) (s x)
    end
  end

(** Used in compilation **)
let equiv_oval_var0 (g:typ_env) (t:qType) : Lemma (fs_oval_var0 g t ⊏ EVar 0) =
  introduce forall b (s:gsub (extend t g) b) fsG h. fsG `(≍) h` s ==>  t ⊆ (h, hd fsG, gsubst s (EVar 0)) with begin
    introduce _ ==> _ with _. begin
      index_0_hd fsG;
      assert (t ∈ (h, hd fsG, s 0));
      lem_values_are_expressions t h (hd fsG) (s 0)
    end
  end

#push-options "--split_queries always --z3rlimit 32"
 (** Used in compilation **)
let equiv_varS (#g:typ_env) #a #t (s:fs_oval g a) (e:exp)
  : Lemma
      (requires (s ⊏ e))
      (ensures (fs_oval_varS t s ⊏ subst sub_inc e))
  =
  lem_fv_in_env_varS g t e;
  introduce forall b (s':gsub (extend t g) b) (fsG:eval_env (extend t g)) (h:history). fsG `(≍) h` s' ==> a ⊆ (h, s (tail fsG), gsubst s' (subst sub_inc e)) with begin
    introduce fsG `(≍) h` s' ==> a ⊆ (h, s (tail fsG), gsubst s' (subst sub_inc e)) with _. begin
      lem_index_tail fsG;
      let f : var -> exp = fun (y:var) -> s' (y+1) in
      introduce (forall (x:var{x>0}). EVar? (s' x)) ==> a ⊆ (h, s (tail fsG), gsubst s' (subst sub_inc e)) with _. begin
        eliminate forall b_ (s_:gsub g b_) (fsG_:eval_env g) (h_:history). fsG_ `(≍) h_` s_ ==> a ⊆ (h_, s fsG_, gsubst s_ e) with true f (tail fsG) h;
        shift_sub_equiv_sub_inc_rename #t s' e f
      end;
      introduce (~(forall (x:var{x>0}). EVar? (s' x))) ==> a ⊆ (h, s (tail fsG), gsubst s' (subst sub_inc e)) with _. begin
        eliminate forall b_ (s_:gsub g b_) (fsG_:eval_env g) (h_:history). fsG_ `(≍) h_` s_  ==> a ⊆ (h_, s fsG_, gsubst s_ e) with false f (tail fsG) h;
        shift_sub_equiv_sub_inc_no_rename #t #g s' e f
      end
    end
  end
#pop-options

let equiv_oval_lambda #g (#t1:qType) (#t2:qType) (fs_body:fs_oval (extend t1 g) t2) (body:exp) : Lemma
  (requires fs_body ⊏ body)
  (ensures (fs_oval_lambda fs_body ⊏ ELam body)) =
  lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  let f : fs_oval g (t1 ^-> t2) = fun fsG x -> fs_body (stack fsG x) in
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> (t1 ^-> t2) ⊆ (h, f fsG, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∈ (h++lt_v, fs_v, v) ==> t2 ⊆ (h++lt_v, f fsG fs_v, subst_beta v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fsG' = stack fsG fs_v in
          let h' = h++lt_v in
          eliminate forall b (s':gsub g' b) (fsG':eval_env g') h'. fsG' `(≍) h'` s' ==> t2 ⊆ (h', f (tail #t1 fsG') (hd #t1 #g fsG'), gsubst s' body)
            with false s' fsG' h';
          assert (fsG `(≍) h` s);
          assert (t1 ∈ (h++lt_v, fs_v, v));
          introduce forall (x:var). Some? (g x) ==> Some?.v (g x) ∈ (h++lt_v, index fsG x, s x) with begin
            introduce _ ==> _ with _. begin
              val_type_closed_under_history_extension (Some?.v (g x)) h (index fsG x) (s x)
            end
          end;
          assert (stack fsG fs_v `(≍) h'` gsub_extend s t1 v);
          assert (t2 ⊆ (h', f (tail fsG') (hd fsG'), (gsubst s' body)));
          assert (hd (stack fsG fs_v) == fs_v);
          assert (t2 ⊆ (h', f (tail fsG') fs_v, (gsubst s' body)));
          assert (t2 ⊆ (h', f fsG fs_v, (gsubst s' body)));
          lem_substitution s t1 v body;
          assert (t2 ⊆ (h', f fsG fs_v, subst_beta v body'))
        end
      end;
      assert ((t1 ^-> t2) ∈ (h, f fsG, gsubst s (ELam body)));
      lem_values_are_expressions (t1 ^-> t2) h (f fsG) (gsubst s (ELam body));
      assert ((t1 ^-> t2) ⊆ (h, f fsG, gsubst s (ELam body)))
    end
  end

let helper_equiv_oval_app_steps (h:history) (lt:local_trace h) (t1 t2:qType) (fs_e1:fs_val (t1 ^-> t2)) (fs_e2:fs_val t1) (e1 e2:closed_exp) :
  Lemma 
    (requires (t1 ^-> t2) ⊆ (h, fs_e1, e1) /\
              (forall (lt:local_trace h). t1 ⊆ (h++lt, fs_e2, e2)))
    (ensures exists (e':closed_exp). e_beh (EApp e1 e2) e' h [] /\ t2 ∈ (h, fs_e1 fs_e2, e')) =
  eliminate exists (e1':closed_exp). e_beh e1 e1' h [] /\ (t1 ^-> t2) ∈ (h, fs_e1, e1')
    returns exists (e':closed_exp). e_beh (EApp e1 e2) e' h [] /\ t2 ∈ (h, fs_e1 fs_e2, e') with _. begin
  let ELam e11 = e1' in
  unfold_member_of_arrow t1 t2 h fs_e1 e11;
  lem_forall_values_are_values t1 h fs_e2;
  eliminate exists (e2':closed_exp). e_beh e2 e2' h [] /\ t1 ∈ (h, fs_e2, e2')
    returns exists (e':closed_exp). e_beh (EApp e1 e2) e' h [] /\ t2 ∈ (h, fs_e1 fs_e2, e') with _. begin
  eliminate forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∈ (h++lt_v, fs_v, v) ==> t2 ⊆ (h++lt_v, fs_e1 fs_v, subst_beta v e11) with e2' fs_e2 [];
  eliminate exists (e':closed_exp). e_beh (subst_beta e2' e11) e' h [] /\ t2 ∈ (h, fs_e1 fs_e2, e')
    returns exists (e':closed_exp). e_beh (EApp e1 e2) e' h [] /\ t2 ∈ (h, fs_e1 fs_e2, e') with _. begin
  FStar.Squash.bind_squash #(steps e1 (ELam e11) h []) () (fun sts1 ->
  FStar.Squash.bind_squash #(steps e2 e2' h []) () (fun sts2 ->
  FStar.Squash.bind_squash #(steps (subst_beta e2' e11) e' h []) () (fun sts3 ->
  construct_steps_eapp e1 e11 e2 e2' e' h [] [] [] sts1 sts2 sts3
  )))
  end
  end
  end

let equiv_oval_app #g
  (#t1:qType) (#t2:qType)
  (fs_e1:fs_oval g (t1 ^-> t2)) (fs_e2:fs_oval g t1)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊏ e1 /\ fs_e2 ⊏ e2)
    (ensures fs_oval_app fs_e1 fs_e2 ⊏ EApp e1 e2) =
  lem_fv_in_env_app g e1 e2;
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> t2 ⊆ (h, (fs_e1 fsG) (fs_e2 fsG), gsubst s (EApp e1 e2)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e2 = fs_e2 fsG in
    let fs_e = fs_e1 fs_e2 in
    let e = EApp (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EApp e1 e2) == e);
    let EApp e1 e2 = e in
    introduce fsG `(≍) h` s ==> t2 ⊆ (h, fs_e, e) with _. begin
      lem_shift_type_value_environments h fsG s;
      helper_equiv_oval_app_steps h [] t1 t2 fs_e1 fs_e2 e1 e2
    end
  end

let helper_equiv_oval_if_steps (h:history) (t:qType) (fs_c:fs_val qBool) (fs_t fs_f:fs_val t) (c e_t e_f:closed_exp) :
  Lemma
    (requires qBool ⊆ (h, fs_c, c) /\
              t ⊆ (h, fs_t, e_t) /\
              t ⊆ (h, fs_f, e_f))
    (ensures exists (e':closed_exp). e_beh (EIf c e_t e_f) e' h [] /\ t ∈ (h, (if fs_c then fs_t else fs_f), e')) =
  eliminate exists (c':closed_exp). e_beh c c' h [] /\ qBool ∈ (h, fs_c, c')
    returns exists (e':closed_exp). e_beh (EIf c e_t e_f) e' h [] /\ t ∈ (h, (if fs_c then fs_t else fs_f), e') with _. begin
  eliminate exists (e':closed_exp). e_beh (if fs_c then e_t else e_f) e' h [] /\ t ∈ (h, (if fs_c then fs_t else fs_f), e')
    returns exists (e':closed_exp). e_beh (EIf c e_t e_f) e' h [] /\ t ∈ (h, (if fs_c then fs_t else fs_f), e') with _. begin
  FStar.Squash.bind_squash #(steps c c' h []) () (fun sts1 ->
    FStar.Squash.bind_squash #(steps (if fs_c then e_t else e_f) e' h []) () (fun sts2 ->
      construct_steps_eif c c' e_t e_f e' h [] [] sts1 sts2))
    end
  end

let equiv_oval_if #g
  (#t:qType)
  (fs_e1:fs_oval g qBool) (fs_e2:fs_oval g t) (fs_e3:fs_oval g t)
  (e1:exp) (e2:exp) (e3:exp)
  : Lemma
    (requires fs_e1 ⊏ e1 /\ fs_e2 ⊏ e2 /\ fs_e3 ⊏ e3)
    (ensures fs_oval_if fs_e1 fs_e2 fs_e3 ⊏ EIf e1 e2 e3) =
  lem_fv_in_env_if g e1 e2 e3;
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> t ⊆ (h, (if fs_e1 fsG then fs_e2 fsG else fs_e3 fsG), gsubst s (EIf e1 e2 e3)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e2 = fs_e2 fsG in
    let fs_e3 = fs_e3 fsG in
    let fs_e = if fs_e1 then fs_e2 else fs_e3 in
    let e = EIf (gsubst s e1) (gsubst s e2) (gsubst s e3) in
    assert (gsubst s (EIf e1 e2 e3) == e);
    let EIf e1 e2 e3 = e in
    introduce fsG `(≍) h` s ==> t ⊆ (h, fs_e, e) with _. begin
      helper_equiv_oval_if_steps h t fs_e1 fs_e2 fs_e3 e1 e2 e3
    end
  end

#push-options "--z3rlimit 10"
let helper_equiv_oval_pair_steps (h:history) (t1 t2:qType) (fs_e1:fs_val t1) (fs_e2:fs_val t2) (e1 e2:closed_exp) :
  Lemma
    (requires t1 ⊆ (h, fs_e1, e1) /\
              t2 ⊆ (h, fs_e2, e2))
    (ensures (t1 ^* t2) ⊆ (h, (fs_e1, fs_e2), EPair e1 e2)) =
  let t = t1 ^* t2 in
  eliminate exists (e1':closed_exp). e_beh e1 e1' h [] /\ t1 ∈ (h, fs_e1, e1')
    returns t ⊆ (h, (fs_e1, fs_e2), EPair e1 e2) with _. begin
  eliminate exists (e2':closed_exp). e_beh e2 e2' h [] /\ t2 ∈ (h, fs_e2, e2')
    returns t ⊆ (h, (fs_e1, fs_e2), EPair e1 e2) with _. begin
  lem_values_are_values t1 h fs_e1 e1';
  lem_values_are_values t2 h fs_e2 e2';
  lem_value_is_irred e1';
  lem_value_is_irred e2';
  assert (is_value (EPair e1' e2'));
  lem_value_is_irred (EPair e1' e2');
  assert (t ∈ (h, (fs_e1, fs_e2), EPair e1' e2'));
  FStar.Squash.bind_squash #(steps e1 e1' h []) #(squash (t ⊆ (h, (fs_e1, fs_e2), EPair e1 e2))) () (fun (sts1:steps e1 e1' h []) ->
  FStar.Squash.bind_squash #(steps e2 e2' h []) #(squash (t ⊆ (h, (fs_e1, fs_e2), EPair e1 e2))) () (fun (sts2:steps e2 e2' h []) ->
  construct_steps_epair e1 e1' e2 e2' h [] [] sts1 sts2))
  end
  end
#pop-options

let equiv_oval_pair #g
  (#t1 #t2:qType)
  (fs_e1:fs_oval g t1) (fs_e2:fs_oval g t2)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊏ e1 /\ fs_e2 ⊏ e2)
    (ensures fs_oval_pair fs_e1 fs_e2 ⊏ EPair e1 e2) =
  lem_fv_in_env_pair g e1 e2;
  let t = t1 ^* t2 in
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==>  t ⊆ (h, (fs_e1 fsG, fs_e2 fsG), gsubst s (EPair e1 e2)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e2 = fs_e2 fsG in
    let fs_e = (fs_e1, fs_e2) in
    let e = EPair (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EPair e1 e2) == e);
    let EPair e1 e2 = e in
    introduce fsG `(≍) h` s ==>  t ⊆ (h, fs_e, e) with _. begin
      helper_equiv_oval_pair_steps h t1 t2 fs_e1 fs_e2 e1 e2
    end
  end

let helper_equiv_oval_fst_steps (h:history) (t1 t2:qType) (fs_e12:fs_val (t1 ^* t2)) (e12:closed_exp) :
  Lemma
    (requires (t1 ^* t2) ⊆ (h, fs_e12, e12))
    (ensures t1 ⊆ (h, fst fs_e12, EFst e12)) =
  eliminate exists (e12':closed_exp). e_beh e12 e12' h [] /\ (t1 ^* t2) ∈ (h, fs_e12, e12')
    returns t1 ⊆ (h, fst fs_e12, EFst e12) with _. begin
  let EPair e1' e2' = e12' in
  assert (t1 ∈ (h, fst fs_e12, e1'));
  assert (t2 ∈ (h, snd fs_e12, e2'));
  lem_values_are_values t1 h (fst fs_e12) e1';
  lem_values_are_values t2 h (snd fs_e12) e2';
  lem_value_is_irred e1';
  lem_value_is_irred e2';
  lem_value_is_irred (EPair e1' e2');
  let fst_ret : step (EFst (EPair e1' e2')) e1' h None = FstPairReturn h in
  lem_step_implies_steps (EFst (EPair e1' e2')) e1' h None;
  FStar.Squash.bind_squash #(steps e12 (EPair e1' e2') h []) #(squash (t1 ⊆ (h, fst fs_e12, EFst e12))) () (fun (sts12:steps e12 (EPair e1' e2') h []) ->
    construct_steps_efst e12 (EPair e1' e2') h [] sts12;
    lem_steps_transitive (EFst e12) (EFst (EPair e1' e2')) e1' h [] []
  )
  end

let helper_equiv_oval_snd_steps (h:history) (t1 t2:qType) (fs_e12:fs_val (t1 ^* t2)) (e12:closed_exp) :
  Lemma
    (requires (t1 ^* t2) ⊆ (h, fs_e12, e12))
    (ensures t2 ⊆ (h, snd fs_e12, ESnd e12)) =
  eliminate exists (e12':closed_exp). e_beh e12 e12' h [] /\ (t1 ^* t2) ∈ (h, fs_e12, e12')
    returns t2 ⊆ (h, snd fs_e12, ESnd e12) with _. begin
  let EPair e1' e2' = e12' in
  assert (t1 ∈ (h, fst fs_e12, e1'));
  assert (t2 ∈ (h, snd fs_e12, e2'));
  lem_values_are_values t1 h (fst fs_e12) e1';
  lem_values_are_values t2 h (snd fs_e12) e2';
  lem_value_is_irred e1';
  lem_value_is_irred e2';
  lem_value_is_irred (EPair e1' e2');
  let snd_ret : step (ESnd (EPair e1' e2')) e2' h None = SndPairReturn h in
  lem_step_implies_steps (ESnd (EPair e1' e2')) e2' h None;
  FStar.Squash.bind_squash #(steps e12 (EPair e1' e2') h []) #(squash (t2 ⊆ (h, snd fs_e12, ESnd e12))) () (fun (sts12:steps e12 (EPair e1' e2') h []) ->
    construct_steps_esnd e12 (EPair e1' e2') h [] sts12;
    lem_steps_transitive (ESnd e12) (ESnd (EPair e1' e2')) e2' h [] []
  )
  end

let equiv_oval_pair_fst #g
  (#t1 #t2:qType)
  (fs_e12:fs_oval g (t1 ^* t2))
  (e12:exp)
  : Lemma
    (requires fs_e12 ⊏ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures fs_oval_fmap fs_e12 fst ⊏ (EFst e12)) =
  lem_fv_in_env_fst g e12;
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==>  t1 ⊆ (h, fst (fs_e12 fsG), gsubst s (EFst e12)) with begin
    let fs_e12 = fs_e12 fsG in
    let fs_e = fst fs_e12 in
    let e = EFst (gsubst s e12) in
    assert (gsubst s (EFst e12) == e);
    let EFst e12 = e in
    introduce fsG `(≍) h` s ==> t1 ⊆ (h, fs_e, e) with _. begin
      helper_equiv_oval_fst_steps h t1 t2 fs_e12 e12
    end
  end

let equiv_oval_pair_snd #g (#t1 #t2:qType) (fs_e12:fs_oval g (t1 ^* t2)) (e12:exp)
  : Lemma
    (requires fs_e12 ⊏ e12)
    (ensures fs_oval_fmap fs_e12 snd ⊏ (ESnd e12)) =
  lem_fv_in_env_snd g e12;
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> t2 ⊆ (h, snd (fs_e12 fsG), gsubst s (ESnd e12)) with begin
    let fs_e12 = fs_e12 fsG in
    let fs_e = snd fs_e12 in
    let e = ESnd (gsubst s e12) in
    assert (gsubst s (ESnd e12) == e);
    let ESnd e12 = e in
    introduce fsG `(≍) h` s ==> t2 ⊆ (h, fs_e, e) with _. begin
      helper_equiv_oval_snd_steps h t1 t2 fs_e12 e12
    end
  end

let helper_equiv_oval_inl_steps (h:history) (t1 t2:qType) (fs_e:fs_val t1) (e:closed_exp) :
  Lemma
    (requires t1 ⊆ (h, fs_e, e))
    (ensures (t1 ^+ t2) ⊆ (h, Inl #(get_Type t1) #(get_Type t2) fs_e, EInl e)) =
  eliminate exists (e':closed_exp). e_beh e e' h [] /\ t1 ∈ (h, fs_e, e')
    returns (t1 ^+ t2) ⊆ (h, Inl #(get_Type t1) #(get_Type t2) fs_e, EInl e) with _. begin
  lem_values_are_values t1 h fs_e e';
  lem_value_is_irred e';
  lem_value_is_irred (EInl e');
  assert ((t1 ^+ t2) ∈ (h, Inl #(get_Type t1) #(get_Type t2) fs_e, EInl e'));
  assert (e_beh (EInl e') (EInl e') h []);
  FStar.Squash.bind_squash #(steps e e' h []) #(squash ((t1 ^+ t2) ⊆ (h, Inl #(get_Type t1) #(get_Type t2) fs_e, EInl e))) () (fun (sts:steps e e' h []) ->
    construct_steps_einl e e' h [] sts;
    lem_steps_transitive (EInl e) (EInl e') (EInl e') h [] [])
  end

let helper_equiv_oval_inr_steps (h:history) (t1 t2:qType) (fs_e:fs_val t2) (e:closed_exp) :
  Lemma
    (requires t2 ⊆ (h, fs_e, e))
    (ensures (t1 ^+ t2) ⊆ (h, Inr #(get_Type t1) #(get_Type t2) fs_e, EInr e)) =
  eliminate exists (e':closed_exp). e_beh e e' h [] /\ t2 ∈ (h, fs_e, e')
    returns (t1 ^+ t2) ⊆ (h, Inr #(get_Type t1) #(get_Type t2) fs_e, EInr e) with _. begin
  lem_values_are_values t2 h fs_e e';
  lem_value_is_irred e';
  lem_value_is_irred (EInr e');
  assert ((t1 ^+ t2) ∈ (h, Inr #(get_Type t1) #(get_Type t2) fs_e, EInr e'));
  assert (e_beh (EInr e') (EInr e') h []);
  FStar.Squash.bind_squash #(steps e e' h []) #(squash ((t1 ^+ t2) ⊆ (h, Inr #(get_Type t1) #(get_Type t2) fs_e, EInr e))) () (fun (sts:steps e e' h []) ->
    construct_steps_einr e e' h [] sts;
    lem_steps_transitive (EInr e) (EInr e') (EInr e') h [] [])
  end

let equiv_oval_inl #g (#t1 t2:qType) (fs_e:fs_oval g t1) (e:exp) : Lemma
  (requires fs_e ⊏ e)
  (ensures fs_oval_fmap #g #t1 #(t1 ^+ t2) fs_e Inl ⊏ (EInl e)) =
  lem_fv_in_env_inl g e;
  let t = t1 ^+ t2 in
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> (t1 ^+ t2) ⊆ (h, Inl (fs_e fsG), gsubst s (EInl e)) with begin
    let fs_e = fs_e fsG in
    let fs_ex = Inl #(get_Type t1) #(get_Type t2) fs_e in
    let ex = EInl (gsubst s e) in
    assert (gsubst s (EInl e) == ex);
    let EInl e = ex in
    introduce fsG `(≍) h` s ==> t ⊆ (h, fs_ex, ex) with _. begin
      helper_equiv_oval_inl_steps h t1 t2 fs_e e
    end
  end

let equiv_oval_inr #g (t1 #t2:qType) (fs_e:fs_oval g t2) (e:exp) : Lemma
  (requires fs_e ⊏ e)
  (ensures fs_oval_fmap #g #t2 #(t1 ^+ t2) fs_e Inr ⊏ (EInr e)) =
  lem_fv_in_env_inr g e;
  let t = t1 ^+ t2 in
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> (t1 ^+ t2) ⊆ (h, Inr (fs_e fsG), gsubst s (EInr e)) with begin
    let fs_e = fs_e fsG in
    let fs_ex = Inr #(get_Type t1) #(get_Type t2) fs_e in
    let ex = EInr (gsubst s e) in
    assert (gsubst s (EInr e) == ex);
    let EInr e = ex in
    introduce fsG `(≍) h` s ==> t ⊆ (h, fs_ex, ex) with _. begin
      helper_equiv_oval_inr_steps h t1 t2 fs_e e
    end
  end

#push-options "--z3rlimit 15"
let helper_equiv_oval_case_steps (h:history) (t1 t2 t3:qType)
  (fs_case:fs_val (t1 ^+ t2))
  (fs_lc_lam:fs_val (t1 ^-> t3))
  (fs_rc_lam:fs_val (t2 ^-> t3))
  (e_case:closed_exp)
  (e_lc:exp{is_closed (ELam e_lc)})
  (e_rc:exp{is_closed (ELam e_rc)}) :
  Lemma
    (requires (t1 ^+ t2) ⊆ (h, fs_case, e_case) /\
              (t1 ^-> t3) ⊆ (h, fs_lc_lam, ELam e_lc) /\
              (t2 ^-> t3) ⊆ (h, fs_rc_lam, ELam e_rc))
    (ensures t3 ⊆ (h, fs_val_case fs_case fs_lc_lam fs_rc_lam, ECase e_case e_lc e_rc)) =
  eliminate exists (ec':closed_exp). e_beh e_case ec' h [] /\ (t1 ^+ t2) ∈ (h, fs_case, ec')
    returns t3 ⊆ (h, fs_val_case fs_case fs_lc_lam fs_rc_lam, ECase e_case e_lc e_rc) with _. begin
  lem_values_are_values (t1 ^+ t2) h fs_case ec';
  match fs_case with
  | Inl x -> begin
    let EInl v = ec' in
    lem_values_are_values t1 h x v;
    eliminate exists (elc':closed_exp). e_beh (ELam e_lc) elc' h [] /\ (t1 ^-> t3) ∈ (h, fs_lc_lam, elc')
      returns t3 ⊆ (h, fs_lc_lam x, ECase e_case e_lc e_rc) with _. begin
    steps_val_id (ELam e_lc) elc' h;
    unfold_member_of_arrow t1 t3 h fs_lc_lam e_lc;
    eliminate forall (v':value) (fs_v:fs_val t1) (lt_v:local_trace h).
      t1 ∈ (h++lt_v, fs_v, v') ==> t3 ⊆ (h++lt_v, fs_lc_lam fs_v, subst_beta v' e_lc) with v x [];
    eliminate exists (e':closed_exp). e_beh (subst_beta v e_lc) e' h [] /\ t3 ∈ (h, fs_lc_lam x, e')
      returns t3 ⊆ (h, fs_lc_lam x, ECase e_case e_lc e_rc) with _. begin
    FStar.Squash.bind_squash #(steps e_case (EInl v) h []) #(squash (t3 ⊆ (h, fs_lc_lam x, ECase e_case e_lc e_rc))) () (fun (sts1:steps e_case (EInl v) h []) ->
    FStar.Squash.bind_squash #(steps (subst_beta v e_lc) e' h []) #(squash (t3 ⊆ (h, fs_lc_lam x, ECase e_case e_lc e_rc))) () (fun (sts2:steps (subst_beta v e_lc) e' h []) ->
      construct_steps_ecase_inl e_case v e_lc e_rc e' h [] [] sts1 sts2))
    end
    end
  end
  | Inr x -> begin
    let EInr v = ec' in
    lem_values_are_values t2 h x v;
    eliminate exists (erc':closed_exp). e_beh (ELam e_rc) erc' h [] /\ (t2 ^-> t3) ∈ (h, fs_rc_lam, erc')
      returns t3 ⊆ (h, fs_rc_lam x, ECase e_case e_lc e_rc) with _. begin
    steps_val_id (ELam e_rc) erc' h;
    unfold_member_of_arrow t2 t3 h fs_rc_lam e_rc;
    eliminate forall (v':value) (fs_v:fs_val t2) (lt_v:local_trace h).
      t2 ∈ (h++lt_v, fs_v, v') ==> t3 ⊆ (h++lt_v, fs_rc_lam fs_v, subst_beta v' e_rc) with v x [];
    eliminate exists (e':closed_exp). e_beh (subst_beta v e_rc) e' h [] /\ t3 ∈ (h, fs_rc_lam x, e')
      returns t3 ⊆ (h, fs_rc_lam x, ECase e_case e_lc e_rc) with _. begin
    FStar.Squash.bind_squash #(steps e_case (EInr v) h []) #(squash (t3 ⊆ (h, fs_rc_lam x, ECase e_case e_lc e_rc))) () (fun (sts1:steps e_case (EInr v) h []) ->
    FStar.Squash.bind_squash #(steps (subst_beta v e_rc) e' h []) #(squash (t3 ⊆ (h, fs_rc_lam x, ECase e_case e_lc e_rc))) () (fun (sts2:steps (subst_beta v e_rc) e' h []) ->
      construct_steps_ecase_inr e_case v e_lc e_rc e' h [] [] sts1 sts2))
    end
    end
  end
  end
#pop-options

let equiv_oval_case
  #g
  (#t1 #t2 #t3:qType)
  (fs_case:fs_oval g (t1 ^+ t2))
  (fs_lc:fs_oval (extend t1 g) t3)
  (fs_rc:fs_oval (extend t2 g) t3)
  (e_case e_lc e_rc:exp)
  : Lemma
    (requires fs_case ⊏ e_case /\ fs_lc ⊏ e_lc /\ fs_rc ⊏ e_rc)
    (ensures fs_oval_case fs_case fs_lc fs_rc ⊏ ECase e_case e_lc e_rc) =
  lem_fv_in_env_case g t1 t2 e_case e_lc e_rc;
  lem_fv_in_env_lam g t1 e_lc;
  lem_fv_in_env_lam g t2 e_rc;
  equiv_oval_lambda #g #t1 #t3 fs_lc e_lc;
  equiv_oval_lambda #g #t2 #t3 fs_rc e_rc;
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> t3 ⊆ (h, fs_oval_case fs_case fs_lc fs_rc fsG, gsubst s (ECase e_case e_lc e_rc)) with begin
    let fs_case = fs_case fsG in
    let fs_lc_lam : fs_val (t1 ^-> t3) = fun x -> fs_lc (stack fsG x) in
    let fs_rc_lam : fs_val (t2 ^-> t3) = fun  x -> fs_rc (stack fsG x) in
    let fs_e = (fs_val_case fs_case fs_lc_lam fs_rc_lam) in
    let e = ECase (gsubst s e_case) (subst (sub_elam s) e_lc) (subst (sub_elam s) e_rc) in
    assert (gsubst s (ECase e_case e_lc e_rc) == e);
    let ECase e_case e_lc e_rc = e in
    introduce fsG `(≍) h` s ==> t3 ⊆ (h, fs_e, e) with _. begin
      helper_equiv_oval_case_steps h t1 t2 t3 fs_case fs_lc_lam fs_rc_lam e_case e_lc e_rc
    end
  end

let equiv_oval_lambda_oprod #g (#t1:qType) (#t2:qType) (fs_body:fs_oprod (extend t1 g) t2) (body:exp)
  : Lemma
    (requires fs_body ⊑ body)
    (ensures fs_oval_lambda_oprod fs_body ⊏ (ELam body)) =
  lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  let f : fs_oval g (t1 ^->!@ t2) = fun fsG x -> fs_body (stack fsG x) in
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> (t1 ^->!@ t2) ⊆ (h, f fsG, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∈ (h++lt_v, fs_v, v) ==> t2 ⫃ (h++lt_v, (f fsG) fs_v, subst_beta v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fsG' = stack fsG fs_v in
          let h' = h++lt_v in
          eliminate forall b (s':gsub g' b) (fsG':eval_env g') h'. fsG' `(≍) h'` s' ==> t2 ⫃ (h', f (tail #t1 fsG') (hd #t1 #g fsG'), gsubst s' body)
            with false s' fsG' h';
          assert (fsG `(≍) h` s);
          assert (t1 ∈ (h++lt_v, fs_v, v));
          introduce forall (x:var). Some? (g x) ==> Some?.v (g x) ∈ (h++lt_v, index fsG x, s x) with begin
            introduce _ ==> _ with _. begin
              val_type_closed_under_history_extension (Some?.v (g x)) h (index fsG x) (s x)
            end
          end;
          assert (stack fsG fs_v `(≍) h'` gsub_extend s t1 v);
          assert (t2 ⫃ (h', f (tail fsG') (hd fsG'), gsubst s' body));
          assert (hd (stack fsG fs_v) == fs_v);
          assert (t2 ⫃ (h', f (tail fsG') fs_v, gsubst s' body));
          assert (t2 ⫃ (h', f fsG fs_v, gsubst s' body));
          lem_substitution s t1 v body;
          assert (t2 ⫃ (h', f fsG fs_v, subst_beta v body'))
        end
      end;
      assert ((t1 ^->!@ t2) ∈ (h, f fsG, gsubst s (ELam body)));
      lem_values_are_expressions (t1 ^->!@ t2) h (f fsG) (gsubst s (ELam body));
      assert ((t1 ^->!@ t2) ⊆ (h, f fsG, gsubst s (ELam body)))
    end
  end

let equiv_oprod_return #g (#t:qType) (fs_x:fs_oval g t) (x:exp)
  : Lemma
    (requires fs_x ⊏ x)
    (ensures fs_oprod_return fs_x ⊑ x) =
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> t ⫃ (h, return (fs_x fsG), gsubst s x) with begin
    introduce _ ==> _ with _. begin
      let fs_x = fs_x fsG in
      let fs_e = return fs_x in
      let e = gsubst s x in
      introduce forall lt (fs_r:get_Type t). fs_beh fs_e h lt fs_r ==>
        (exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt) with begin
        introduce fs_beh fs_e h lt fs_r ==>
          (exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt) with _. begin
          theta_monad_morphism_ret fs_x;
          let p : hist_post h (get_Type t) = fun lt' r' -> lt' == [] /\ r' == fs_x in
          assert (hist_return fs_x h p);
          assert (theta (io_return fs_x) h p);
          assert (thetaP (io_return fs_x) h lt fs_r);
          assert (p lt fs_r);
          assert (lt == []);
          assert (fs_r == fs_x)
        end
      end
    end
  end

#push-options "--z3rlimit 15"
let helper_equiv_oprod_bind_steps (h:history) (lt:local_trace h) (a b:qType)
  (fs_m:fs_prod a) (fs_k:fs_val a -> fs_prod b) (fs_r:fs_val b)
  (m:closed_exp) (k:exp{is_closed (ELam k)}) :
  Lemma
    (requires fs_beh (fs_prod_bind fs_m fs_k) h lt fs_r /\
              a ⫃ (h, fs_m, m) /\
              (a ^->!@ b) ⊆ (h, fs_k, ELam k))
    (ensures exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp (ELam k) m) e' h lt) =
  destruct_fs_beh fs_m fs_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m_val:fs_val a).
    lt == (lt1@lt2) /\ fs_beh fs_m h lt1 fs_m_val /\ fs_beh (fs_k fs_m_val) (h++lt1) lt2 fs_r
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp (ELam k) m) e' h lt with _. begin
  // From a ⫃ (h, fs_m, m)
  eliminate forall (lt':local_trace h) (fs_r':get_Type a). fs_beh fs_m h lt' fs_r' ==> exists em'. a ∈ (h++lt', fs_r', em') /\ e_beh m em' h lt' with lt1 fs_m_val;
  eliminate exists em'. a ∈ (h++lt1, fs_m_val, em') /\ e_beh m em' h lt1
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp (ELam k) m) e' h lt with _. begin
  // Unfold IO arrow: (a ^->!@ b) ⊆ (h, fs_k, ELam k)
  eliminate exists (lam':closed_exp). e_beh (ELam k) lam' h [] /\ (a ^->!@ b) ∈ (h, fs_k, lam')
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp (ELam k) m) e' h lt with _. begin
  steps_val_id (ELam k) lam' h;
  unfold_member_of_io_arrow a b fs_k k h;
  lem_values_are_values a (h++lt1) fs_m_val em';
  eliminate forall (v:value) (fs_v:fs_val a) (lt_v:local_trace h).
    a ∈ (h++lt_v, fs_v, v) ==> b ⫃ (h++lt_v, fs_k fs_v, subst_beta v k) with em' fs_m_val lt1;
  // From b ⫃ (h++lt1, fs_k fs_m_val, subst_beta em' k)
  eliminate forall (lt':local_trace (h++lt1)) (fs_r':get_Type b). fs_beh (fs_k fs_m_val) (h++lt1) lt' fs_r' ==> exists e'. b ∈ ((h++lt1)++lt', fs_r', e') /\ e_beh (subst_beta em' k) e' (h++lt1) lt' with lt2 fs_r;
  eliminate exists e'. b ∈ ((h++lt1)++lt2, fs_r, e') /\ e_beh (subst_beta em' k) e' (h++lt1) lt2
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp (ELam k) m) e' h lt with _. begin
  // Construct steps: EApp (ELam k) m --> e'
  FStar.Squash.bind_squash #(steps m em' h lt1) () (fun sts_m ->
  FStar.Squash.bind_squash #(steps (subst_beta em' k) e' (h++lt1) lt2) () (fun sts_k ->
  construct_steps_eapp (ELam k) k m em' e' h [] lt1 lt2 (SRefl (ELam k) h) sts_m sts_k;
  trans_history h lt1 lt2))
  end
  end
  end
  end
#pop-options

let equiv_oprod_bind #g (#a #b:qType) (fs_m:fs_oprod g a) (fs_k:fs_oprod (extend a g) b) (m k:exp)
  : Lemma
    (requires fs_m ⊑ m /\ fs_k ⊑ k)
    (ensures (fs_oprod_bind fs_m fs_k) ⊑ (EApp (ELam k) m)) =
  lem_fv_in_env_lam g a k;
  lem_fv_in_env_app g (ELam k) m;
  equiv_oval_lambda_oprod fs_k k;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> b ⫃ (h, fs_oprod_bind fs_m fs_k fsG, gsubst s (EApp (ELam k) m)) with begin
    let fs_m' = fs_m fsG in
    let fs_k' : fs_val a -> fs_prod b = fun x -> fs_k (stack fsG x) in
    let fs_e = fs_prod_bind fs_m' fs_k' in
    assert ((fs_oprod_bind fs_m fs_k fsG) == fs_e);
    let k' = subst (sub_elam s) k in
    assert (gsubst s (ELam k) == ELam k');
    let e = EApp (ELam k') (gsubst s m) in
    assert (gsubst s (EApp (ELam k) m) == e);
    let EApp (ELam k') m = e in
    introduce fsG `(≍) h` s ==> b ⫃ (h, fs_e, e) with _. begin
      introduce forall lt (fs_r:fs_val b). fs_beh fs_e h lt fs_r ==> exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce fs_beh fs_e h lt fs_r ==> exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          lem_shift_type_value_environments h fsG s;
          helper_equiv_oprod_bind_steps h lt a b fs_m' fs_k' fs_r m k'
        end
      end
    end
  end

let helper_equiv_oprod_app_oval_oval_steps (h:history) (lt:local_trace h) (a b:qType) (fs_f:fs_val (a ^->!@ b)) (fs_x:fs_val a) (f x:closed_exp) (fs_r:fs_val b) :
  Lemma
    (requires (fs_beh (fs_f fs_x) h lt fs_r) /\
              (a ^->!@ b) ⊆ (h, fs_f, f) /\
              (forall (lt:local_trace h). a ⊆ (h++lt, fs_x, x)))
    (ensures exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt) =
  eliminate exists (f':closed_exp). e_beh f f' h [] /\ (a ^->!@ b) ∈ (h, fs_f, f')
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
  let ELam f1 = f' in
  unfold_member_of_io_arrow a b fs_f f1 h;
  lem_forall_values_are_values a h fs_x;
  eliminate exists (x':closed_exp). e_beh x x' h [] /\ a ∈ (h, fs_x, x')
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
  eliminate forall (v:value) (fs_v:fs_val a) (lt_v:local_trace h). a ∈ (h++lt_v, fs_v, v) ==> b ⫃ (h++lt_v, fs_f fs_v, subst_beta v f1) with x' fs_x [];
  eliminate forall (lt:local_trace h) (fs_r:get_Type b). fs_beh (fs_f fs_x) h lt fs_r ==> exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (subst_beta x' f1) e' h lt with lt fs_r;
  eliminate exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (subst_beta x' f1) e' h lt
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
  FStar.Squash.bind_squash #(steps f (ELam f1) h []) () (fun sts1 ->
  FStar.Squash.bind_squash #(steps x x' h []) () (fun sts2 ->
  FStar.Squash.bind_squash #(steps (subst_beta x' f1) e' h lt) () (fun sts3 ->
  construct_steps_eapp f f1 x x' e' h [] [] lt sts1 sts2 sts3
  )))
  end
  end
  end

let equiv_oprod_app_oval_oval #g (#a #b:qType) (fs_f:fs_oval g (a ^->!@ b)) (fs_x:fs_oval g a) (f x:exp)
  : Lemma
    (requires fs_f ⊏ f /\ fs_x ⊏ x)
    (ensures (fs_oprod_app_oval_oval fs_f fs_x) ⊑ (EApp f x)) =
  lem_fv_in_env_app g f x;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> b ⫃ (h, (fs_f fsG) (fs_x fsG), gsubst s (EApp f x)) with begin
    let fs_f = fs_f fsG in
    let fs_x = fs_x fsG in
    let fs_e = fs_f fs_x in
    let e = EApp (gsubst s f) (gsubst s x) in
    assert (gsubst s (EApp f x) == e);
    let EApp f x = e in
    introduce fsG `(≍) h` s ==> b ⫃ (h, fs_e, e) with _. begin
      introduce forall (lt:local_trace h) (fs_r:get_Type b). fs_beh fs_e h lt fs_r ==> exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce _ ==> _ with _. begin
          lem_shift_type_value_environments h fsG s;
          helper_equiv_oprod_app_oval_oval_steps h lt a b fs_f fs_x f x fs_r
        end
      end
    end
  end

let helper_equiv_oprod_if_val (#h:history) (lt:local_trace h) (#a:qType) (fs_c:fs_val qBool) (fs_t:fs_prod a) (fs_e:fs_prod a) (fs_r:fs_val a) (c t e:closed_exp) :
  Lemma
    (requires (fs_beh (if fs_c then fs_t else fs_e) h lt fs_r) /\
              (qBool ⊆ (h, fs_c, c)) /\
              (a ⫃ (h, fs_t, t)) /\
              (a ⫃ (h, fs_e, e)))
    (ensures (exists ex'. a ∈ (h++lt, fs_r, ex') /\ e_beh (EIf c t e) ex' h lt)) =
  eliminate exists (c':closed_exp). e_beh c c' h [] /\ qBool ∈ (h, fs_c, c')
    returns exists ex'. a ∈ (h++lt, fs_r, ex') /\ e_beh (EIf c t e) ex' h lt with _. begin
  eliminate forall (lt:local_trace h) (fs_r:fs_val a). fs_beh (if fs_c then fs_t else fs_e) h lt fs_r ==> exists ex'. a ∈ (h++lt, fs_r, ex') /\ e_beh (if fs_c then t else e) ex' h lt with lt fs_r;
  eliminate exists ex'. a ∈ (h++lt, fs_r, ex') /\ e_beh (if fs_c then t else e) ex' h lt
    returns exists ex'. a ∈ (h++lt, fs_r, ex') /\ e_beh (EIf c t e) ex' h lt with _. begin
  FStar.Squash.bind_squash #(steps c c' h []) () (fun sts1 ->
  FStar.Squash.bind_squash #(steps (if fs_c then t else e) ex' h lt) () (fun sts2 ->
  construct_steps_eif c c' t e ex' h [] lt sts1 sts2))
  end
  end

let equiv_oprod_if_oval #g (#a:qType) (fs_c:fs_oval g qBool) (fs_t fs_e:fs_oprod g a) (c t e:exp)
  : Lemma
    (requires fs_c ⊏ c /\ fs_t ⊑ t /\ fs_e ⊑ e)
    (ensures (fs_oprod_if_oval fs_c fs_t fs_e) ⊑ (EIf c t e)) =
  lem_fv_in_env_if g c t e;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> a ⫃ (h, (if (fs_c fsG) then (fs_t fsG) else (fs_e fsG)), gsubst s (EIf c t e)) with begin
    let fs_c = fs_c fsG in
    let fs_t = fs_t fsG in
    let fs_e = fs_e fsG in
    let fs_ex = if fs_c then fs_t else fs_e in
    let ex = EIf (gsubst s c) (gsubst s t) (gsubst s e) in
    assert (gsubst s (EIf c t e) == ex);
    let EIf c t e = ex in
    introduce fsG `(≍) h` s ==> a ⫃ (h, fs_ex, ex) with _. begin
      introduce forall (lt:local_trace h) (fs_r:fs_val a). fs_beh fs_ex h lt fs_r ==> exists ex'. a ∈ (h++lt, fs_r, ex') /\ e_beh ex ex' h lt with begin
        introduce fs_beh fs_ex h lt fs_r ==> exists ex'. a ∈ (h++lt, fs_r, ex') /\ e_beh ex ex' h lt with _. begin
          helper_equiv_oprod_if_val lt fs_c fs_t fs_e fs_r c t e
        end
      end
    end
  end

#push-options "--z3rlimit 15"
let helper_equiv_oprod_case_oval_steps (h:history) (lt:local_trace h) (a b c:qType)
  (fs_cond:fs_val (a ^+ b))
  (fs_inlc:fs_val (a ^->!@ c))
  (fs_inrc:fs_val (b ^->!@ c))
  (fs_r:fs_val c)
  (e_cond:closed_exp)
  (e_lc:exp{is_closed (ELam e_lc)})
  (e_rc:exp{is_closed (ELam e_rc)}) :
  Lemma
    (requires (a ^+ b) ⊆ (h, fs_cond, e_cond) /\
              (a ^->!@ c) ⊆ (h, fs_inlc, ELam e_lc) /\
              (b ^->!@ c) ⊆ (h, fs_inrc, ELam e_rc) /\
              fs_beh (fs_prod_case_val fs_cond fs_inlc fs_inrc) h lt fs_r)
    (ensures exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt) =
  eliminate exists (ec':closed_exp). e_beh e_cond ec' h [] /\ (a ^+ b) ∈ (h, fs_cond, ec')
    returns exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt with _. begin
  lem_values_are_values (a ^+ b) h fs_cond ec';
  match fs_cond with
  | Inl x -> begin
    let EInl v = ec' in
    lem_values_are_values a h x v;
    eliminate exists (elc':closed_exp). e_beh (ELam e_lc) elc' h [] /\ (a ^->!@ c) ∈ (h, fs_inlc, elc')
      returns exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt with _. begin
    steps_val_id (ELam e_lc) elc' h;
    unfold_member_of_io_arrow a c fs_inlc e_lc h;
    eliminate forall (v':value) (fs_v:fs_val a) (lt_v:local_trace h).
      a ∈ (h++lt_v, fs_v, v') ==> c ⫃ (h++lt_v, fs_inlc fs_v, subst_beta v' e_lc) with v x [];
    eliminate forall (lt':local_trace h) (fs_r':get_Type c). fs_beh (fs_inlc x) h lt' fs_r' ==>
      exists e'. c ∈ (h++lt', fs_r', e') /\ e_beh (subst_beta v e_lc) e' h lt' with lt fs_r;
    eliminate exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (subst_beta v e_lc) e' h lt
      returns exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt with _. begin
    FStar.Squash.bind_squash #(steps e_cond (EInl v) h []) #(squash (exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt)) () (fun (sts1:steps e_cond (EInl v) h []) ->
    FStar.Squash.bind_squash #(steps (subst_beta v e_lc) e' h lt) #(squash (exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt)) () (fun (sts2:steps (subst_beta v e_lc) e' h lt) ->
      construct_steps_ecase_inl e_cond v e_lc e_rc e' h [] lt sts1 sts2))
    end
    end
  end
  | Inr x -> begin
    let EInr v = ec' in
    lem_values_are_values b h x v;
    eliminate exists (erc':closed_exp). e_beh (ELam e_rc) erc' h [] /\ (b ^->!@ c) ∈ (h, fs_inrc, erc')
      returns exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt with _. begin
    steps_val_id (ELam e_rc) erc' h;
    unfold_member_of_io_arrow b c fs_inrc e_rc h;
    eliminate forall (v':value) (fs_v:fs_val b) (lt_v:local_trace h).
      b ∈ (h++lt_v, fs_v, v') ==> c ⫃ (h++lt_v, fs_inrc fs_v, subst_beta v' e_rc) with v x [];
    eliminate forall (lt':local_trace h) (fs_r':get_Type c). fs_beh (fs_inrc x) h lt' fs_r' ==>
      exists e'. c ∈ (h++lt', fs_r', e') /\ e_beh (subst_beta v e_rc) e' h lt' with lt fs_r;
    eliminate exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (subst_beta v e_rc) e' h lt
      returns exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt with _. begin
    FStar.Squash.bind_squash #(steps e_cond (EInr v) h []) #(squash (exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt)) () (fun (sts1:steps e_cond (EInr v) h []) ->
    FStar.Squash.bind_squash #(steps (subst_beta v e_rc) e' h lt) #(squash (exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt)) () (fun (sts2:steps (subst_beta v e_rc) e' h lt) ->
      construct_steps_ecase_inr e_cond v e_lc e_rc e' h [] lt sts1 sts2))
    end
    end
  end
  end
#pop-options

#push-options "--z3rlimit 15"
let equiv_oprod_case_oval #g (#a #b #c:qType) (fs_cond:fs_oval g (a ^+ b)) (fs_inlc:fs_oprod (extend a g) c) (fs_inrc:fs_oprod (extend b g) c) (cond inlc inrc:exp)
  : Lemma
    (requires fs_cond ⊏ cond /\ fs_inlc ⊑ inlc /\ fs_inrc ⊑ inrc)
    (ensures (fs_oprod_case_oval fs_cond fs_inlc fs_inrc) ⊑ (ECase cond inlc inrc)) =
  lem_fv_in_env_case g a b cond inlc inrc;
  lem_fv_in_env_lam g a inlc;
  lem_fv_in_env_lam g b inrc;
  equiv_oval_lambda_oprod fs_inlc inlc;
  equiv_oval_lambda_oprod fs_inrc inrc;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> c ⫃ (h, fs_oprod_case_oval fs_cond fs_inlc fs_inrc fsG, gsubst s (ECase cond inlc inrc)) with begin
    let fs_cond = fs_cond fsG in
    let fs_inlc' : fs_val (a ^->!@ c) = fun x -> fs_inlc (stack fsG x) in
    let fs_inrc' : fs_val (b ^->!@ c) = fun x -> fs_inrc (stack fsG x) in
    let fs_e = fs_prod_case_val fs_cond fs_inlc' fs_inrc' in
    let e = ECase (gsubst s cond) (subst (sub_elam s) inlc) (subst (sub_elam s) inrc) in
    assert (gsubst s (ECase cond inlc inrc) == e);
    let ECase cond inlc inrc = e in
    introduce fsG `(≍) h` s ==> c ⫃ (h, fs_e, e) with _. begin
      introduce forall (lt:local_trace h) (fs_r:fs_val c). fs_beh fs_e h lt fs_r ==> exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce fs_beh fs_e h lt fs_r ==> exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          helper_equiv_oprod_case_oval_steps h lt a b c fs_cond fs_inlc' fs_inrc' fs_r cond inlc inrc
        end
      end
    end
  end
#pop-options

#push-options "--z3rlimit 15"
let helper_equiv_oprod_openfile_oval_steps (h:history) (lt:local_trace h) (fs_fnm:fs_val qString) (fnm:closed_exp) (fs_r:fs_val (qFileDescr ^+ qUnit)) :
  Lemma
    (requires fs_beh (openfile fs_fnm) h lt fs_r /\
              qString ⊆ (h, fs_fnm, fnm))
    (ensures exists e'. (qFileDescr ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EOpen fnm) e' h lt) =
  // Extract the value witness from qString ⊆
  eliminate exists (fnm':closed_exp). e_beh fnm fnm' h [] /\ qString ∈ (h, fs_fnm, fnm')
    returns exists e'. (qFileDescr ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EOpen fnm) e' h lt with _. begin
  // fnm' must be EString fs_fnm
  lem_values_are_values qString h fs_fnm fnm';
  let EString s = fnm' in
  assert (s == fs_fnm);
  // Determine what lt and fs_r must be from thetaP
  destruct_thetaP_open fs_fnm h lt fs_r;
  // Get steps fnm (EString fs_fnm) h [] and construct EOpen congruence steps
  FStar.Squash.bind_squash #(steps fnm fnm' h []) () (fun sts_fnm ->
  construct_steps_eopen fnm fnm' h [] sts_fnm;
  // Case 1: fs_r = Inl (fresh_fd h), lt = [EvOpen fs_fnm (Inl (fresh_fd h))]
  let st_succ : step (EOpen (EString fs_fnm)) (EInl (EFileDescr (fresh_fd h))) h (Some (EvOpen fs_fnm (Inl (fresh_fd h)))) = SOpenReturnSuccess (EString fs_fnm) h in
  lem_step_implies_steps (EOpen (EString fs_fnm)) (EInl (EFileDescr (fresh_fd h))) h (Some (EvOpen fs_fnm (Inl (fresh_fd h))));
  lem_steps_transitive (EOpen fnm) (EOpen (EString fs_fnm)) (EInl (EFileDescr (fresh_fd h))) h [] [EvOpen fs_fnm (Inl (fresh_fd h))];
  // Case 2: fs_r = Inr (), lt = [EvOpen fs_fnm (Inr ())]
  let st_fail : step (EOpen (EString fs_fnm)) (EInr EUnit) h (Some (EvOpen fs_fnm (Inr ()))) = SOpenReturnFail (EString fs_fnm) h in
  lem_step_implies_steps (EOpen (EString fs_fnm)) (EInr EUnit) h (Some (EvOpen fs_fnm (Inr ())));
  lem_steps_transitive (EOpen fnm) (EOpen (EString fs_fnm)) (EInr EUnit) h [] [EvOpen fs_fnm (Inr ())];
  // Irred witnesses for both cases
  lem_value_is_irred (EFileDescr (fresh_fd h));
  lem_value_is_irred (EInl (EFileDescr (fresh_fd h)));
  lem_value_is_irred EUnit;
  lem_value_is_irred (EInr EUnit))
  end
#pop-options

let equiv_oprod_openfile_oval #g (fs_fnm:fs_oval g qString) (fnm:exp)
  : Lemma
    (requires fs_fnm ⊏ fnm)
    (ensures fs_oprod_openfile_oval fs_fnm ⊑ EOpen fnm)
  =
  lem_fv_in_env_openfile g fnm;
  introduce forall b (s:gsub g b) (fsG:eval_env g) (h:history). fsG `(≍) h` s ==> (qFileDescr ^+ qUnit) ⫃ (h, openfile (fs_fnm fsG), gsubst s (EOpen fnm)) with begin
    let fs_fnm = fs_fnm fsG in
    let fs_e = openfile fs_fnm in
    let e = EOpen (gsubst s fnm) in
    assert (gsubst s (EOpen fnm) == e);
    let EOpen fnm = e in
    introduce fsG `(≍) h` s ==> (qFileDescr ^+ qUnit) ⫃ (h, fs_e, e) with _. begin
      lem_shift_type_value_environments h fsG s;
      introduce forall lt (fs_r:fs_val (qFileDescr ^+ qUnit)). fs_beh fs_e h lt fs_r ==> exists e'. (qFileDescr ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce fs_beh fs_e h lt fs_r ==> exists e'. (qFileDescr ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          helper_equiv_oprod_openfile_oval_steps h lt fs_fnm fnm fs_r
        end
      end
    end
  end

#push-options "--z3rlimit 15"
let helper_equiv_oprod_read_oval_steps (h:history) (lt:local_trace h) (fs_fd:fs_val qFileDescr) (fd:closed_exp) (fs_r:fs_val (qString ^+ qUnit)) :
  Lemma
    (requires fs_beh (read fs_fd) h lt fs_r /\
              qFileDescr ⊆ (h, fs_fd, fd))
    (ensures exists e'. (qString ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (ERead fd) e' h lt) =
  eliminate exists (fd':closed_exp). e_beh fd fd' h [] /\ qFileDescr ∈ (h, fs_fd, fd')
    returns exists e'. (qString ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (ERead fd) e' h lt with _. begin
  lem_values_are_values qFileDescr h fs_fd fd';
  assert (fd' == EFileDescr fs_fd);
  destruct_thetaP_read fs_fd h lt fs_r;
  FStar.Squash.bind_squash #(steps fd fd' h []) () (fun sts_fd ->
  construct_steps_eread fd fd' h [] sts_fd;
  let st_read : step (ERead (EFileDescr fs_fd)) (get_resexn_string fs_r) h (Some (EvRead fs_fd fs_r)) = SReadReturn h fs_fd fs_r in
  lem_step_implies_steps (ERead (EFileDescr fs_fd)) (get_resexn_string fs_r) h (Some (EvRead fs_fd fs_r));
  lem_steps_transitive (ERead fd) (ERead (EFileDescr fs_fd)) (get_resexn_string fs_r) h [] [EvRead fs_fd fs_r];
  (match fs_r with
  | Inl s ->
    lem_value_is_irred (EString s);
    lem_value_is_irred (EInl (EString s))
  | Inr () ->
    lem_value_is_irred EUnit;
    lem_value_is_irred (EInr EUnit)))
  end
#pop-options

let equiv_oprod_read_oval #g (fs_fd:fs_oval g qFileDescr) (fd:exp)
  : Lemma
    (requires fs_fd ⊏ fd)
    (ensures fs_oprod_read_oval fs_fd ⊑ ERead fd)
  =
  lem_fv_in_env_read g fd;
  introduce forall b (s:gsub g b) (fsG:eval_env g) (h:history). fsG `(≍) h` s ==> (qString ^+ qUnit) ⫃ (h, read (fs_fd fsG), gsubst s (ERead fd)) with begin
    let fs_fd = fs_fd fsG in
    let fs_e = read fs_fd in
    let e = ERead (gsubst s fd) in
    assert (gsubst s (ERead fd) == e);
    let ERead fd = e in
    introduce fsG `(≍) h` s ==> (qString ^+ qUnit) ⫃ (h, fs_e, e) with _. begin
      lem_shift_type_value_environments h fsG s;
      introduce forall lt (fs_r:fs_val (qString ^+ qUnit)). fs_beh fs_e h lt fs_r ==> exists e'. (qString ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce fs_beh fs_e h lt fs_r ==> exists e'. (qString ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          helper_equiv_oprod_read_oval_steps h lt fs_fd fd fs_r
        end
      end
    end
  end

#push-options "--z3rlimit 15"
let helper_equiv_oprod_write_oval_steps (h:history) (lt:local_trace h) (fs_fd:fs_val qFileDescr) (fs_msg:fs_val qString) (fd msg:closed_exp) (fs_r:fs_val (qUnit ^+ qUnit)) :
  Lemma
    (requires fs_beh (write (fs_fd, fs_msg)) h lt fs_r /\
              qFileDescr ⊆ (h, fs_fd, fd) /\
              qString ⊆ (h, fs_msg, msg))
    (ensures exists e'. (qUnit ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EWrite fd msg) e' h lt) =
  eliminate exists (fd':closed_exp). e_beh fd fd' h [] /\ qFileDescr ∈ (h, fs_fd, fd')
    returns exists e'. (qUnit ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EWrite fd msg) e' h lt with _. begin
  lem_values_are_values qFileDescr h fs_fd fd';
  assert (fd' == EFileDescr fs_fd);
  eliminate exists (msg':closed_exp). e_beh msg msg' h [] /\ qString ∈ (h, fs_msg, msg')
    returns exists e'. (qUnit ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EWrite fd msg) e' h lt with _. begin
  lem_values_are_values qString h fs_msg msg';
  let EString ms = msg' in
  assert (ms == fs_msg);
  destruct_thetaP_write (fs_fd, fs_msg) h lt fs_r;
  FStar.Squash.bind_squash #(steps fd fd' h []) () (fun sts_fd ->
  FStar.Squash.bind_squash #(steps msg msg' h []) () (fun sts_msg ->
  construct_steps_ewrite_fd fd fd' msg h [] sts_fd;
  construct_steps_ewrite_arg fd' msg msg' h [] sts_msg;
  lem_steps_transitive (EWrite fd msg) (EWrite fd' msg) (EWrite fd' msg') h [] [];
  let st_wr : step (EWrite (EFileDescr fs_fd) (EString fs_msg)) (get_resexn_unit fs_r) h (Some (EvWrite (fs_fd, fs_msg) fs_r)) = SWriteReturn h fs_fd (EString fs_msg) fs_r in
  lem_step_implies_steps (EWrite (EFileDescr fs_fd) (EString fs_msg)) (get_resexn_unit fs_r) h (Some (EvWrite (fs_fd, fs_msg) fs_r));
  lem_steps_transitive (EWrite fd msg) (EWrite (EFileDescr fs_fd) (EString fs_msg)) (get_resexn_unit fs_r) h [] [EvWrite (fs_fd, fs_msg) fs_r];
  (match fs_r with
  | Inl () ->
    lem_value_is_irred EUnit;
    lem_value_is_irred (EInl EUnit)
  | Inr () ->
    lem_value_is_irred EUnit;
    lem_value_is_irred (EInr EUnit))))
  end end
#pop-options

let equiv_oprod_write_oval #g (fs_fd:fs_oval g qFileDescr) (fs_msg:fs_oval g qString) (fd msg:exp)
  : Lemma
    (requires fs_fd ⊏ fd /\ fs_msg ⊏ msg)
    (ensures fs_oprod_write_oval fs_fd fs_msg ⊑ EWrite fd msg)
  =
  lem_fv_in_env_write g fd msg;
  introduce forall b (s:gsub g b) (fsG:eval_env g) (h:history). fsG `(≍) h` s ==> (qUnit ^+ qUnit) ⫃ (h, write (fs_fd fsG, fs_msg fsG), gsubst s (EWrite fd msg)) with begin
    let fs_fd = fs_fd fsG in
    let fs_msg = fs_msg fsG in
    let fs_e = write (fs_fd, fs_msg) in
    let e = EWrite (gsubst s fd) (gsubst s msg) in
    assert (gsubst s (EWrite fd msg) == e);
    let EWrite fd msg = e in
    introduce fsG `(≍) h` s ==> (qUnit ^+ qUnit) ⫃ (h, fs_e, e) with _. begin
      lem_shift_type_value_environments h fsG s;
      introduce forall lt (fs_r:fs_val (qUnit ^+ qUnit)). fs_beh fs_e h lt fs_r ==> exists e'. (qUnit ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce fs_beh fs_e h lt fs_r ==> exists e'. (qUnit ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          helper_equiv_oprod_write_oval_steps h lt fs_fd fs_msg fd msg fs_r
        end
      end
    end
  end

#push-options "--z3rlimit 15"
let helper_equiv_oprod_close_oval_steps (h:history) (lt:local_trace h) (fs_fd:fs_val qFileDescr) (fd:closed_exp) (fs_r:fs_val (qUnit ^+ qUnit)) :
  Lemma
    (requires fs_beh (close fs_fd) h lt fs_r /\
              qFileDescr ⊆ (h, fs_fd, fd))
    (ensures exists e'. (qUnit ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EClose fd) e' h lt) =
  eliminate exists (fd':closed_exp). e_beh fd fd' h [] /\ qFileDescr ∈ (h, fs_fd, fd')
    returns exists e'. (qUnit ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EClose fd) e' h lt with _. begin
  lem_values_are_values qFileDescr h fs_fd fd';
  assert (fd' == EFileDescr fs_fd);
  destruct_thetaP_close fs_fd h lt fs_r;
  FStar.Squash.bind_squash #(steps fd fd' h []) () (fun sts_fd ->
  construct_steps_eclose fd fd' h [] sts_fd;
  let st_cl : step (EClose (EFileDescr fs_fd)) (get_resexn_unit fs_r) h (Some (EvClose fs_fd fs_r)) = SCloseReturn h fs_fd fs_r in
  lem_step_implies_steps (EClose (EFileDescr fs_fd)) (get_resexn_unit fs_r) h (Some (EvClose fs_fd fs_r));
  lem_steps_transitive (EClose fd) (EClose (EFileDescr fs_fd)) (get_resexn_unit fs_r) h [] [EvClose fs_fd fs_r];
  (match fs_r with
  | Inl () ->
    lem_value_is_irred EUnit;
    lem_value_is_irred (EInl EUnit)
  | Inr () ->
    lem_value_is_irred EUnit;
    lem_value_is_irred (EInr EUnit)))
  end
#pop-options

let equiv_oprod_close_oval #g (fs_fd:fs_oval g qFileDescr) (fd:exp)
  : Lemma
    (requires fs_fd ⊏ fd)
    (ensures fs_oprod_close_oval fs_fd ⊑ EClose fd)
  =
  lem_fv_in_env_close g fd;
  introduce forall b (s:gsub g b) (fsG:eval_env g) (h:history). fsG `(≍) h` s ==> (qUnit ^+ qUnit) ⫃ (h, close (fs_fd fsG), gsubst s (EClose fd)) with begin
    let fs_fd = fs_fd fsG in
    let fs_e = close fs_fd in
    let e = EClose (gsubst s fd) in
    assert (gsubst s (EClose fd) == e);
    let EClose fd = e in
    introduce fsG `(≍) h` s ==> (qUnit ^+ qUnit) ⫃ (h, fs_e, e) with _. begin
      lem_shift_type_value_environments h fsG s;
      introduce forall lt (fs_r:fs_val (qUnit ^+ qUnit)). fs_beh fs_e h lt fs_r ==> exists e'. (qUnit ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce fs_beh fs_e h lt fs_r ==> exists e'. (qUnit ^+ qUnit) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          helper_equiv_oprod_close_oval_steps h lt fs_fd fd fs_r
        end
      end
    end
  end

let equiv_oprod_unit g : Lemma (fs_oprod_return_val g qUnit () ⊑ EUnit) =
  equiv_oval_unit g;
  equiv_oprod_return (fs_oval_return g qUnit ()) EUnit

let equiv_oprod_true g : Lemma (fs_oprod_return_val g qBool true ⊑ ETrue) =
  equiv_oval_true g;
  equiv_oprod_return (fs_oval_return g qBool true) ETrue

let equiv_oprod_false g : Lemma (fs_oprod_return_val g qBool false ⊑ EFalse) =
  equiv_oval_false g;
  equiv_oprod_return (fs_oval_return g qBool false) EFalse

let equiv_oprod_string g s : Lemma (fs_oprod_return_val g qString s ⊑ EString s) =
  equiv_oval_string g s;
  equiv_oprod_return (fs_oval_return g qString s) (EString s)

let helper_equiv_oprod_if_steps_pre (g:typ_env) (e:closed_exp) (h:history) (lt:local_trace h) (t:qType) (fs_e1:fs_prod qBool) (fs_e2 fs_e3:fs_oprod g t) (fs_e:fs_prod t) (fs_r:fs_val t) (e1 e2 e3:closed_exp) (fsG:eval_env g) =
  (fs_e == (io_bind fs_e1 (fun x -> (if (hd (stack fsG x)) then (fs_e2 (tail (stack fsG x))) else (fs_e3 (tail (stack fsG x))))))) /\
  (e == (EIf e1 e2 e3)) /\
  (fs_beh fs_e h lt fs_r) /\
  (qBool ⫃ (h, fs_e1, e1)) /\
  (forall (lt:local_trace h). t ⫃ (h++lt, (fs_e2 fsG), e2)) /\
  (forall (lt:local_trace h). t ⫃ (h++lt, (fs_e3 fsG), e3))

#push-options "--z3rlimit 15 --split_queries always"
let helper_equiv_oprod_if_steps (h:history) (lt:local_trace h) (t:qType)
  (fs_e1:fs_prod qBool) (fs_e2 fs_e3:fs_prod t) (fs_r:fs_val t)
  (e1 e2 e3:closed_exp) :
  Lemma
    (requires fs_beh (fs_prod_bind fs_e1 (fun x -> fs_prod_if_val x fs_e2 fs_e3)) h lt fs_r /\
              qBool ⫃ (h, fs_e1, e1) /\
              (forall (lt':local_trace h). t ⫃ (h++lt', fs_e2, e2)) /\
              (forall (lt':local_trace h). t ⫃ (h++lt', fs_e3, e3)))
    (ensures exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh (EIf e1 e2 e3) e' h lt) =
  let fs_k : fs_val qBool -> fs_prod t = fun x -> fs_prod_if_val x fs_e2 fs_e3 in
  assert (fs_prod_bind fs_e1 fs_k == io_bind fs_e1 fs_k) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_e1 fs_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_b:fs_val qBool).
    lt == (lt1@lt2) /\ fs_beh fs_e1 h lt1 fs_b /\ fs_beh (fs_k fs_b) (h++lt1) lt2 fs_r
    returns exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh (EIf e1 e2 e3) e' h lt with _. begin
  // From qBool ⫃ (h, fs_e1, e1), get the boolean value expression
  eliminate forall (lt':local_trace h) (fs_r':get_Type qBool). fs_beh fs_e1 h lt' fs_r' ==> exists e1'. qBool ∈ (h++lt', fs_r', e1') /\ e_beh e1 e1' h lt' with lt1 fs_b;
  eliminate exists e1'. qBool ∈ (h++lt1, fs_b, e1') /\ e_beh e1 e1' h lt1
    returns exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh (EIf e1 e2 e3) e' h lt with _. begin
  lem_values_are_values qBool (h++lt1) fs_b e1';
  lem_value_is_irred e1';
  trans_history h lt1 lt2;
  if fs_b then begin
    assert (e1' == ETrue);
    assert (fs_beh fs_e2 (h++lt1) lt2 fs_r);
    // From forall lt'. t ⫃ (h++lt', fs_e2, e2), specialize with lt1
    assert (t ⫃ (h++lt1, fs_e2, e2));
    eliminate forall (lt'':local_trace (h++lt1)) (fs_r':get_Type t).
      fs_beh fs_e2 (h++lt1) lt'' fs_r' ==> exists e'. t ∈ ((h++lt1)++lt'', fs_r', e') /\ e_beh e2 e' (h++lt1) lt'' with lt2 fs_r;
    eliminate exists e'. t ∈ ((h++lt1)++lt2, fs_r, e') /\ e_beh e2 e' (h++lt1) lt2
      returns exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh (EIf e1 e2 e3) e' h lt with _. begin
    FStar.Squash.bind_squash #(steps e1 e1' h lt1) () (fun sts_e1 ->
    FStar.Squash.bind_squash #(steps e2 e' (h++lt1) lt2) () (fun sts_branch ->
    construct_steps_eif e1 ETrue e2 e3 e' h lt1 lt2 sts_e1 sts_branch))
    end
  end else begin
    assert (e1' == EFalse);
    assert (fs_beh fs_e3 (h++lt1) lt2 fs_r);
    assert (t ⫃ (h++lt1, fs_e3, e3));
    eliminate forall (lt'':local_trace (h++lt1)) (fs_r':get_Type t).
      fs_beh fs_e3 (h++lt1) lt'' fs_r' ==> exists e'. t ∈ ((h++lt1)++lt'', fs_r', e') /\ e_beh e3 e' (h++lt1) lt'' with lt2 fs_r;
    eliminate exists e'. t ∈ ((h++lt1)++lt2, fs_r, e') /\ e_beh e3 e' (h++lt1) lt2
      returns exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh (EIf e1 e2 e3) e' h lt with _. begin
    FStar.Squash.bind_squash #(steps e1 e1' h lt1) () (fun sts_e1 ->
    FStar.Squash.bind_squash #(steps e3 e' (h++lt1) lt2) () (fun sts_branch ->
    construct_steps_eif e1 EFalse e2 e3 e' h lt1 lt2 sts_e1 sts_branch))
    end
  end
  end
  end
#pop-options

#push-options "--split_queries always"
let equiv_oprod_if #g
  (#t:qType)
  (fs_e1:fs_oprod g qBool) (fs_e2:fs_oprod g t) (fs_e3:fs_oprod g t)
  (e1:exp) (e2:exp) (e3:exp)
  : Lemma
    (requires fs_e1 ⊑ e1 /\ fs_e2 ⊑ e2 /\ fs_e3 ⊑ e3)
    (ensures fs_oprod_if fs_e1 fs_e2 fs_e3 ⊑ EIf e1 e2 e3) =
  lem_fv_in_env_if g e1 e2 e3;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> t ⫃ (h, fs_oprod_if fs_e1 fs_e2 fs_e3 fsG, gsubst s (EIf e1 e2 e3)) with begin
    introduce _ ==> _ with _. begin
      let fs_e1' : fs_prod qBool = fs_e1 fsG in
      let fs_e2' : fs_prod t = fs_e2 fsG in
      let fs_e3' : fs_prod t = fs_e3 fsG in
      let fs_e = fs_prod_bind fs_e1' (fun x -> fs_prod_if_val x fs_e2' fs_e3') in
      assert (fs_e == fs_oprod_if fs_e1 fs_e2 fs_e3 fsG) by (
        norm [delta_only [`%fs_oprod_if;`%fs_oprod_bind';`%fs_oprod_bind;`%fs_oprod_if_val]];
        l_to_r [`lem_hd_stack;`tail_stack_inverse];
        trefl ());
      let e = EIf (gsubst s e1) (gsubst s e2) (gsubst s e3) in
      assert (gsubst s (EIf e1 e2 e3) == e);
      let EIf e1 e2 e3 = e in
      introduce fsG `(≍) h` s ==> t ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val t). fs_beh fs_e h lt fs_r ==> exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            helper_equiv_oprod_if_steps h lt t fs_e1' fs_e2' fs_e3' fs_r e1 e2 e3
          end
        end
      end
    end
  end
#pop-options

let equiv_oprod_file_descr g fd : Lemma (fs_oprod_return_val g qFileDescr fd ⊑ EFileDescr fd) =
  equiv_oval_file_descr g fd;
  equiv_oprod_return (fs_oval_return g qFileDescr fd) (EFileDescr fd)

let equiv_oprod_var g (x:var{Some? (g x)}) : Lemma (fs_oprod_var g x ⊑ EVar x) =
  equiv_oval_var g x;
  equiv_oprod_return (fs_oval_var g x) (EVar x)

#push-options "--z3rlimit 15 --split_queries always"
let helper_equiv_oprod_app_steps (h:history) (lt:local_trace h) (a b:qType)
  (fs_f':fs_prod (a ^->!@ b)) (fs_x':fs_prod a) (fs_r:fs_val b)
  (f x:closed_exp) :
  Lemma
    (requires fs_beh (fs_prod_bind fs_f' (fun f' -> fs_prod_bind fs_x' (fun x' -> f' x'))) h lt fs_r /\
              (a ^->!@ b) ⫃ (h, fs_f', f) /\
              (forall (lt':local_trace h). a ⫃ (h++lt', fs_x', x)))
    (ensures exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt) =
  let fs_outer_k : fs_val (a ^->!@ b) -> fs_prod b = fun f' -> fs_prod_bind fs_x' (fun x' -> f' x') in
  assert (fs_prod_bind fs_f' fs_outer_k == io_bind fs_f' fs_outer_k) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_f' fs_outer_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_r_f:fs_val (a ^->!@ b)).
    lt == (lt1@lt2) /\ fs_beh fs_f' h lt1 fs_r_f /\ fs_beh (fs_outer_k fs_r_f) (h++lt1) lt2 fs_r
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
  // From (a ^->!@ b) ⫃ (h, fs_f', f), get the function value
  eliminate forall (lt':local_trace h) (fs_r':get_Type (a ^->!@ b)). fs_beh fs_f' h lt' fs_r' ==> exists e'. (a ^->!@ b) ∈ (h++lt', fs_r', e') /\ e_beh f e' h lt' with lt1 fs_r_f;
  eliminate exists f'. (a ^->!@ b) ∈ (h++lt1, fs_r_f, f') /\ e_beh f f' h lt1
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
  let ELam f1 = f' in
  // Decompose the inner bind: fs_prod_bind fs_x' (fun x' -> fs_r_f x') at h++lt1
  assert (fs_prod_bind fs_x' (fun x' -> fs_r_f x') == io_bind fs_x' (fun x' -> fs_r_f x')) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_x' (fun x' -> fs_r_f x') (h++lt1) lt2 fs_r;
  eliminate exists (lt2a:local_trace (h++lt1)) (lt2b:local_trace ((h++lt1)++lt2a)) (fs_r_x:fs_val a).
    lt2 == (lt2a@lt2b) /\ fs_beh fs_x' (h++lt1) lt2a fs_r_x /\ fs_beh (fs_r_f fs_r_x) ((h++lt1)++lt2a) lt2b fs_r
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
  // From a ⫃ (h++lt1, fs_x', x), get the argument value
  assert (a ⫃ (h++lt1, fs_x', x));
  eliminate forall (lt':local_trace (h++lt1)) (fs_r':get_Type a). fs_beh fs_x' (h++lt1) lt' fs_r' ==> exists e'. a ∈ ((h++lt1)++lt', fs_r', e') /\ e_beh x e' (h++lt1) lt' with lt2a fs_r_x;
  eliminate exists x'. a ∈ ((h++lt1)++lt2a, fs_r_x, x') /\ e_beh x x' (h++lt1) lt2a
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
  // Unfold IO arrow and get application result
  unfold_member_of_io_arrow a b fs_r_f f1 (h++lt1);
  lem_values_are_values a ((h++lt1)++lt2a) fs_r_x x';
  eliminate forall (v:value) (fs_v:fs_val a) (lt_v:local_trace (h++lt1)).
    a ∈ ((h++lt1)++lt_v, fs_v, v) ==> b ⫃ ((h++lt1)++lt_v, fs_r_f fs_v, subst_beta v f1) with x' fs_r_x lt2a;
  // From b ⫃ ((h++lt1)++lt2a, fs_r_f fs_r_x, subst_beta x' f1)
  eliminate forall (lt':local_trace ((h++lt1)++lt2a)) (fs_r':get_Type b).
    fs_beh (fs_r_f fs_r_x) ((h++lt1)++lt2a) lt' fs_r' ==> exists e'. b ∈ (((h++lt1)++lt2a)++lt', fs_r', e') /\ e_beh (subst_beta x' f1) e' ((h++lt1)++lt2a) lt' with lt2b fs_r;
  eliminate exists e'. b ∈ (((h++lt1)++lt2a)++lt2b, fs_r, e') /\ e_beh (subst_beta x' f1) e' ((h++lt1)++lt2a) lt2b
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
  // Construct steps: EApp f x -->* e'
  FStar.Squash.bind_squash #(steps f (ELam f1) h lt1) () (fun sts_f ->
  FStar.Squash.bind_squash #(steps x x' (h++lt1) lt2a) () (fun sts_x ->
  FStar.Squash.bind_squash #(steps (subst_beta x' f1) e' ((h++lt1)++lt2a) lt2b) () (fun sts_body ->
  construct_steps_eapp f f1 x x' e' h lt1 lt2a lt2b sts_f sts_x sts_body;
  trans_history (h++lt1) lt2a lt2b;
  trans_history h lt1 (lt2a@lt2b))))
  end
  end
  end
  end
  end
#pop-options

let equiv_oprod_app #g (#a #b:qType) (fs_f:fs_oprod g (a ^->!@ b)) (fs_x:fs_oprod g a) (f x:exp)
  : Lemma
    (requires fs_f ⊑ f /\ fs_x ⊑ x)
    (ensures fs_oprod_app fs_f fs_x ⊑ EApp f x) =
  lem_fv_in_env_app g f x;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> b ⫃ (h, fs_oprod_app fs_f fs_x fsG, gsubst s (EApp f x)) with begin
    introduce _ ==> _ with _. begin
      let fs_f' : fs_prod (a ^->!@ b) = fs_f fsG in
      let fs_x' : fs_prod a = fs_x fsG in
      let fs_e = fs_prod_bind fs_f' (fun f' -> fs_prod_bind fs_x' (fun x' -> f' x')) in
      assert (fs_e == fs_oprod_app fs_f fs_x fsG) by (
        norm [delta_only [`%fs_oprod_app;`%fs_oprod_bind';`%fs_oprod_bind;`%fs_oprod_app_oval_oval]];
        l_to_r [`lem_hd_stack;`tail_stack_inverse];
        trefl ());
      let e = EApp (gsubst s f) (gsubst s x) in
      assert (gsubst s (EApp f x) == e);
      let EApp f x = e in
      introduce fsG `(≍) h` s ==> b ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val b). fs_beh fs_e h lt fs_r ==> exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            helper_equiv_oprod_app_steps h lt a b fs_f' fs_x' fs_r f x
          end
        end
      end
    end
  end

let equiv_oprod_lambda #g (#t1:qType) (#t2:qType)
  (fs_body:fs_oprod (extend t1 g) t2)
  (body:exp)
  : Lemma
    (requires fs_body ⊑ body)
    (ensures fs_oprod_lambda fs_body ⊑ (ELam body))
  =
  equiv_oval_lambda_oprod #g #t1 #t2 fs_body body;
  equiv_oprod_return (fs_oval_lambda_oprod fs_body) (ELam body)

(** ---- Helpers for fmap-based lemmas (inl, inr, fst, snd) ---- **)

#push-options "--z3rlimit 15"
let helper_equiv_oprod_fmap_inl_steps (h:history) (lt:local_trace h) (t1 t2:qType)
  (fs_e':fs_prod t1) (fs_r:fs_val (t1 ^+ t2)) (e:closed_exp) :
  Lemma
    (requires fs_beh (fs_prod_bind fs_e' (fun v -> return (Inl #(fs_val t1) #(fs_val t2) v))) h lt fs_r /\
              t1 ⫃ (h, fs_e', e))
    (ensures exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh (EInl e) e' h lt) =
  let fs_k : fs_val t1 -> fs_prod (t1 ^+ t2) = fun v -> return (Inl #(fs_val t1) #(fs_val t2) v) in
  assert (fs_prod_bind fs_e' fs_k == io_bind fs_e' fs_k) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_e' fs_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_v:fs_val t1).
    lt == (lt1@lt2) /\ fs_beh fs_e' h lt1 fs_v /\ fs_beh (return (Inl #(fs_val t1) #(fs_val t2) fs_v)) (h++lt1) lt2 fs_r
    returns exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh (EInl e) e' h lt with _. begin
  let val_ = Inl #(fs_val t1) #(fs_val t2) fs_v in
  theta_monad_morphism_ret val_;
  let p : hist_post (h++lt1) (get_Type (t1 ^+ t2)) = fun lt' r' -> lt' == [] /\ r' == val_ in
  assert (hist_return val_ (h++lt1) p);
  assert (theta (io_return val_) (h++lt1) p);
  assert (thetaP (io_return val_) (h++lt1) lt2 fs_r);
  assert (p lt2 fs_r);
  assert (lt2 == []);
  assert (fs_r == val_);
  unit_l lt1;
  eliminate forall (lt':local_trace h) (fs_r':get_Type t1). fs_beh fs_e' h lt' fs_r' ==> exists em'. t1 ∈ (h++lt', fs_r', em') /\ e_beh e em' h lt' with lt1 fs_v;
  eliminate exists em'. t1 ∈ (h++lt1, fs_v, em') /\ e_beh e em' h lt1
    returns exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh (EInl e) e' h lt with _. begin
  lem_values_are_values t1 (h++lt1) fs_v em';
  lem_value_is_irred em';
  lem_value_is_irred (EInl em');
  FStar.Squash.bind_squash #(steps e em' h lt1) () (fun sts ->
  construct_steps_einl e em' h lt1 sts)
  end
  end
#pop-options

#push-options "--z3rlimit 15"
let helper_equiv_oprod_fmap_inr_steps (h:history) (lt:local_trace h) (t1 t2:qType)
  (fs_e':fs_prod t2) (fs_r:fs_val (t1 ^+ t2)) (e:closed_exp) :
  Lemma
    (requires fs_beh (fs_prod_bind fs_e' (fun v -> return (Inr #(fs_val t1) #(fs_val t2) v))) h lt fs_r /\
              t2 ⫃ (h, fs_e', e))
    (ensures exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh (EInr e) e' h lt) =
  let fs_k : fs_val t2 -> fs_prod (t1 ^+ t2) = fun v -> return (Inr #(fs_val t1) #(fs_val t2) v) in
  assert (fs_prod_bind fs_e' fs_k == io_bind fs_e' fs_k) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_e' fs_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_v:fs_val t2).
    lt == (lt1@lt2) /\ fs_beh fs_e' h lt1 fs_v /\ fs_beh (return (Inr #(fs_val t1) #(fs_val t2) fs_v)) (h++lt1) lt2 fs_r
    returns exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh (EInr e) e' h lt with _. begin
  let val_ = Inr #(fs_val t1) #(fs_val t2) fs_v in
  theta_monad_morphism_ret val_;
  let p : hist_post (h++lt1) (get_Type (t1 ^+ t2)) = fun lt' r' -> lt' == [] /\ r' == val_ in
  assert (hist_return val_ (h++lt1) p);
  assert (theta (io_return val_) (h++lt1) p);
  assert (thetaP (io_return val_) (h++lt1) lt2 fs_r);
  assert (p lt2 fs_r);
  assert (lt2 == []);
  assert (fs_r == val_);
  unit_l lt1;
  eliminate forall (lt':local_trace h) (fs_r':get_Type t2). fs_beh fs_e' h lt' fs_r' ==> exists em'. t2 ∈ (h++lt', fs_r', em') /\ e_beh e em' h lt' with lt1 fs_v;
  eliminate exists em'. t2 ∈ (h++lt1, fs_v, em') /\ e_beh e em' h lt1
    returns exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh (EInr e) e' h lt with _. begin
  lem_values_are_values t2 (h++lt1) fs_v em';
  lem_value_is_irred em';
  lem_value_is_irred (EInr em');
  FStar.Squash.bind_squash #(steps e em' h lt1) () (fun sts ->
  construct_steps_einr e em' h lt1 sts)
  end
  end
#pop-options

#push-options "--z3rlimit 15"
let helper_equiv_oprod_fmap_fst_steps (h:history) (lt:local_trace h) (t1 t2:qType)
  (fs_e12':fs_prod (t1 ^* t2)) (fs_r:fs_val t1) (e12:closed_exp) :
  Lemma
    (requires fs_beh (fs_prod_bind fs_e12' (fun v -> return (fst #(fs_val t1) #(fs_val t2) v))) h lt fs_r /\
              (t1 ^* t2) ⫃ (h, fs_e12', e12))
    (ensures exists e'. t1 ∈ (h++lt, fs_r, e') /\ e_beh (EFst e12) e' h lt) =
  let fs_k : fs_val (t1 ^* t2) -> fs_prod t1 = fun v -> return (fst #(fs_val t1) #(fs_val t2) v) in
  assert (fs_prod_bind fs_e12' fs_k == io_bind fs_e12' fs_k) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_e12' fs_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_pair:fs_val (t1 ^* t2)).
    lt == (lt1@lt2) /\ fs_beh fs_e12' h lt1 fs_pair /\ fs_beh (return (fst #(fs_val t1) #(fs_val t2) fs_pair)) (h++lt1) lt2 fs_r
    returns exists e'. t1 ∈ (h++lt, fs_r, e') /\ e_beh (EFst e12) e' h lt with _. begin
  let val_ = fst #(fs_val t1) #(fs_val t2) fs_pair in
  theta_monad_morphism_ret val_;
  let p : hist_post (h++lt1) (get_Type t1) = fun lt' r' -> lt' == [] /\ r' == val_ in
  assert (hist_return val_ (h++lt1) p);
  assert (theta (io_return val_) (h++lt1) p);
  assert (thetaP (io_return val_) (h++lt1) lt2 fs_r);
  assert (p lt2 fs_r);
  assert (lt2 == []);
  assert (fs_r == val_);
  unit_l lt1;
  eliminate forall (lt':local_trace h) (fs_r':get_Type (t1 ^* t2)). fs_beh fs_e12' h lt' fs_r' ==> exists em'. (t1 ^* t2) ∈ (h++lt', fs_r', em') /\ e_beh e12 em' h lt' with lt1 fs_pair;
  eliminate exists em'. (t1 ^* t2) ∈ (h++lt1, fs_pair, em') /\ e_beh e12 em' h lt1
    returns exists e'. t1 ∈ (h++lt, fs_r, e') /\ e_beh (EFst e12) e' h lt with _. begin
  lem_values_are_values (t1 ^* t2) (h++lt1) fs_pair em';
  let EPair e1' e2' = em' in
  lem_value_is_irred e1';
  lem_value_is_irred e2';
  // Construct: EFst e12 -->* EFst (EPair e1' e2') --> e1'
  FStar.Squash.bind_squash #(steps e12 em' h lt1) () (fun sts ->
  construct_steps_efst e12 em' h lt1 sts;
  let _ : step (EFst (EPair e1' e2')) e1' (h++lt1) None = FstPairReturn (h++lt1) in
  lem_step_implies_steps (EFst (EPair e1' e2')) e1' (h++lt1) None;
  lem_steps_transitive (EFst e12) (EFst em') e1' h lt1 [];
  unit_l lt1)
  end
  end
#pop-options

#push-options "--z3rlimit 15"
let helper_equiv_oprod_fmap_snd_steps (h:history) (lt:local_trace h) (t1 t2:qType)
  (fs_e12':fs_prod (t1 ^* t2)) (fs_r:fs_val t2) (e12:closed_exp) :
  Lemma
    (requires fs_beh (fs_prod_bind fs_e12' (fun v -> return (snd #(fs_val t1) #(fs_val t2) v))) h lt fs_r /\
              (t1 ^* t2) ⫃ (h, fs_e12', e12))
    (ensures exists e'. t2 ∈ (h++lt, fs_r, e') /\ e_beh (ESnd e12) e' h lt) =
  let fs_k : fs_val (t1 ^* t2) -> fs_prod t2 = fun v -> return (snd #(fs_val t1) #(fs_val t2) v) in
  assert (fs_prod_bind fs_e12' fs_k == io_bind fs_e12' fs_k) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_e12' fs_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_pair:fs_val (t1 ^* t2)).
    lt == (lt1@lt2) /\ fs_beh fs_e12' h lt1 fs_pair /\ fs_beh (return (snd #(fs_val t1) #(fs_val t2) fs_pair)) (h++lt1) lt2 fs_r
    returns exists e'. t2 ∈ (h++lt, fs_r, e') /\ e_beh (ESnd e12) e' h lt with _. begin
  let val_ = snd #(fs_val t1) #(fs_val t2) fs_pair in
  theta_monad_morphism_ret val_;
  let p : hist_post (h++lt1) (get_Type t2) = fun lt' r' -> lt' == [] /\ r' == val_ in
  assert (hist_return val_ (h++lt1) p);
  assert (theta (io_return val_) (h++lt1) p);
  assert (thetaP (io_return val_) (h++lt1) lt2 fs_r);
  assert (p lt2 fs_r);
  assert (lt2 == []);
  assert (fs_r == val_);
  unit_l lt1;
  eliminate forall (lt':local_trace h) (fs_r':get_Type (t1 ^* t2)). fs_beh fs_e12' h lt' fs_r' ==> exists em'. (t1 ^* t2) ∈ (h++lt', fs_r', em') /\ e_beh e12 em' h lt' with lt1 fs_pair;
  eliminate exists em'. (t1 ^* t2) ∈ (h++lt1, fs_pair, em') /\ e_beh e12 em' h lt1
    returns exists e'. t2 ∈ (h++lt, fs_r, e') /\ e_beh (ESnd e12) e' h lt with _. begin
  lem_values_are_values (t1 ^* t2) (h++lt1) fs_pair em';
  let EPair e1' e2' = em' in
  lem_value_is_irred e1';
  lem_value_is_irred e2';
  FStar.Squash.bind_squash #(steps e12 em' h lt1) () (fun sts ->
  construct_steps_esnd e12 em' h lt1 sts;
  let _ : step (ESnd (EPair e1' e2')) e2' (h++lt1) None = SndPairReturn (h++lt1) in
  lem_step_implies_steps (ESnd (EPair e1' e2')) e2' (h++lt1) None;
  lem_steps_transitive (ESnd e12) (ESnd em') e2' h lt1 [];
  unit_l lt1)
  end
  end
#pop-options

#push-options "--z3rlimit 15 --split_queries always"
let helper_equiv_oprod_pair_steps (h:history) (lt:local_trace h) (t1 t2:qType)
  (fs_e1':fs_prod t1) (fs_e2':fs_prod t2) (fs_r:fs_val (t1 ^* t2)) (e1 e2:closed_exp) :
  Lemma
    (requires fs_beh (fs_prod_bind fs_e1' (fun v1 -> fs_prod_bind #t2 #(t1 ^* t2) fs_e2' (fun v2 -> return (v1, v2)))) h lt fs_r /\
              t1 ⫃ (h, fs_e1', e1) /\
              (forall (lt':local_trace h). t2 ⫃ (h++lt', fs_e2', e2)))
    (ensures exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh (EPair e1 e2) e' h lt) =
  let fs_k1 : fs_val t1 -> fs_prod (t1 ^* t2) = fun v1 -> fs_prod_bind #t2 #(t1 ^* t2) fs_e2' (fun v2 -> return (v1, v2)) in
  assert (fs_prod_bind fs_e1' fs_k1 == io_bind fs_e1' fs_k1) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_e1' fs_k1 h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_v1:fs_val t1).
    lt == (lt1@lt2) /\ fs_beh fs_e1' h lt1 fs_v1 /\ fs_beh (fs_k1 fs_v1) (h++lt1) lt2 fs_r
    returns exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh (EPair e1 e2) e' h lt with _. begin
  // Get e1 value
  eliminate forall (lt':local_trace h) (fs_r':get_Type t1). fs_beh fs_e1' h lt' fs_r' ==> exists em'. t1 ∈ (h++lt', fs_r', em') /\ e_beh e1 em' h lt' with lt1 fs_v1;
  eliminate exists em1. t1 ∈ (h++lt1, fs_v1, em1) /\ e_beh e1 em1 h lt1
    returns exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh (EPair e1 e2) e' h lt with _. begin
  lem_values_are_values t1 (h++lt1) fs_v1 em1;
  lem_value_is_irred em1;
  // Decompose inner bind: fs_prod_bind fs_e2' (fun v2 -> return (fs_v1, v2))
  let fs_k2 : fs_val t2 -> fs_prod (t1 ^* t2) = fun v2 -> return (fs_v1, v2) in
  assert (fs_prod_bind #t2 #(t1 ^* t2) fs_e2' fs_k2 == io_bind fs_e2' fs_k2) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_e2' fs_k2 (h++lt1) lt2 fs_r;
  eliminate exists (lt2a:local_trace (h++lt1)) (lt2b:local_trace ((h++lt1)++lt2a)) (fs_v2:fs_val t2).
    lt2 == (lt2a@lt2b) /\ fs_beh fs_e2' (h++lt1) lt2a fs_v2 /\ fs_beh (return (fs_v1, fs_v2)) ((h++lt1)++lt2a) lt2b fs_r
    returns exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh (EPair e1 e2) e' h lt with _. begin
  let val_ = (fs_v1, fs_v2) in
  theta_monad_morphism_ret val_;
  let p : hist_post ((h++lt1)++lt2a) (get_Type (t1 ^* t2)) = fun lt' r' -> lt' == [] /\ r' == val_ in
  assert (hist_return val_ ((h++lt1)++lt2a) p);
  assert (theta (io_return val_) ((h++lt1)++lt2a) p);
  assert (thetaP (io_return val_) ((h++lt1)++lt2a) lt2b fs_r);
  assert (p lt2b fs_r);
  assert (lt2b == []);
  assert (fs_r == val_);
  unit_l lt2a;
  // Get e2 value
  assert (t2 ⫃ (h++lt1, fs_e2', e2));
  eliminate forall (lt':local_trace (h++lt1)) (fs_r':get_Type t2). fs_beh fs_e2' (h++lt1) lt' fs_r' ==> exists em'. t2 ∈ ((h++lt1)++lt', fs_r', em') /\ e_beh e2 em' (h++lt1) lt' with lt2a fs_v2;
  eliminate exists em2. t2 ∈ ((h++lt1)++lt2a, fs_v2, em2) /\ e_beh e2 em2 (h++lt1) lt2a
    returns exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh (EPair e1 e2) e' h lt with _. begin
  lem_values_are_values t2 ((h++lt1)++lt2a) fs_v2 em2;
  lem_value_is_irred em2;
  trans_history h lt1 lt2a;
  val_type_closed_under_history_extension t1 (h++lt1) fs_v1 em1;
  lem_value_is_irred (EPair em1 em2);
  // Construct: EPair e1 e2 -->* EPair em1 em2
  FStar.Squash.bind_squash #(steps e1 em1 h lt1) () (fun sts1 ->
  FStar.Squash.bind_squash #(steps e2 em2 (h++lt1) lt2a) () (fun sts2 ->
  construct_steps_epair e1 em1 e2 em2 h lt1 lt2a sts1 sts2;
  assert (steps (EPair e1 e2) (EPair em1 em2) h (lt1@lt2a))))
  end
  end
  end
  end
#pop-options

(** ---- Helpers for IO operation bind decomposition ---- **)

#push-options "--z3rlimit 15"
let helper_equiv_oprod_openfile_steps (h:history) (lt:local_trace h)
  (fs_fnm':fs_prod qString) (fs_r:fs_val (qResexn qFileDescr)) (fnm:closed_exp) :
  Lemma
    (requires fs_beh (fs_prod_bind fs_fnm' (fun fnm' -> openfile fnm')) h lt fs_r /\
              qString ⫃ (h, fs_fnm', fnm))
    (ensures exists e'. (qResexn qFileDescr) ∈ (h++lt, fs_r, e') /\ e_beh (EOpen fnm) e' h lt) =
  let fs_k : fs_val qString -> fs_prod (qResexn qFileDescr) = fun fnm' -> openfile fnm' in
  assert (fs_prod_bind fs_fnm' fs_k == io_bind fs_fnm' fs_k) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_fnm' fs_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_fnm_val:fs_val qString).
    lt == (lt1@lt2) /\ fs_beh fs_fnm' h lt1 fs_fnm_val /\ fs_beh (openfile fs_fnm_val) (h++lt1) lt2 fs_r
    returns exists e'. (qResexn qFileDescr) ∈ (h++lt, fs_r, e') /\ e_beh (EOpen fnm) e' h lt with _. begin
  eliminate forall (lt':local_trace h) (fs_r':get_Type qString). fs_beh fs_fnm' h lt' fs_r' ==> exists em'. qString ∈ (h++lt', fs_r', em') /\ e_beh fnm em' h lt' with lt1 fs_fnm_val;
  eliminate exists em'. qString ∈ (h++lt1, fs_fnm_val, em') /\ e_beh fnm em' h lt1
    returns exists e'. (qResexn qFileDescr) ∈ (h++lt, fs_r, e') /\ e_beh (EOpen fnm) e' h lt with _. begin
  lem_values_are_values qString (h++lt1) fs_fnm_val em';
  trans_history h lt1 lt2;
  helper_equiv_oprod_openfile_oval_steps (h++lt1) lt2 fs_fnm_val em' fs_r;
  eliminate exists e'. (qResexn qFileDescr) ∈ ((h++lt1)++lt2, fs_r, e') /\ e_beh (EOpen em') e' (h++lt1) lt2
    returns exists e'. (qResexn qFileDescr) ∈ (h++lt, fs_r, e') /\ e_beh (EOpen fnm) e' h lt with _. begin
  FStar.Squash.bind_squash #(steps fnm em' h lt1) () (fun sts_fnm ->
  FStar.Squash.bind_squash #(steps (EOpen em') e' (h++lt1) lt2) () (fun sts_open ->
  construct_steps_eopen fnm em' h lt1 sts_fnm;
  lem_steps_transitive (EOpen fnm) (EOpen em') e' h lt1 lt2))
  end
  end
  end
#pop-options

#push-options "--z3rlimit 15"
let helper_equiv_oprod_read_steps (h:history) (lt:local_trace h)
  (fs_fd':fs_prod qFileDescr) (fs_r:fs_val (qResexn qString)) (fd:closed_exp) :
  Lemma
    (requires fs_beh (fs_prod_bind fs_fd' (fun fd' -> read fd')) h lt fs_r /\
              qFileDescr ⫃ (h, fs_fd', fd))
    (ensures exists e'. (qResexn qString) ∈ (h++lt, fs_r, e') /\ e_beh (ERead fd) e' h lt) =
  let fs_k : fs_val qFileDescr -> fs_prod (qResexn qString) = fun fd' -> read fd' in
  assert (fs_prod_bind fs_fd' fs_k == io_bind fs_fd' fs_k) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_fd' fs_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_fd_val:fs_val qFileDescr).
    lt == (lt1@lt2) /\ fs_beh fs_fd' h lt1 fs_fd_val /\ fs_beh (read fs_fd_val) (h++lt1) lt2 fs_r
    returns exists e'. (qResexn qString) ∈ (h++lt, fs_r, e') /\ e_beh (ERead fd) e' h lt with _. begin
  eliminate forall (lt':local_trace h) (fs_r':get_Type qFileDescr). fs_beh fs_fd' h lt' fs_r' ==> exists em'. qFileDescr ∈ (h++lt', fs_r', em') /\ e_beh fd em' h lt' with lt1 fs_fd_val;
  eliminate exists em'. qFileDescr ∈ (h++lt1, fs_fd_val, em') /\ e_beh fd em' h lt1
    returns exists e'. (qResexn qString) ∈ (h++lt, fs_r, e') /\ e_beh (ERead fd) e' h lt with _. begin
  lem_values_are_values qFileDescr (h++lt1) fs_fd_val em';
  trans_history h lt1 lt2;
  helper_equiv_oprod_read_oval_steps (h++lt1) lt2 fs_fd_val em' fs_r;
  eliminate exists e'. (qResexn qString) ∈ ((h++lt1)++lt2, fs_r, e') /\ e_beh (ERead em') e' (h++lt1) lt2
    returns exists e'. (qResexn qString) ∈ (h++lt, fs_r, e') /\ e_beh (ERead fd) e' h lt with _. begin
  FStar.Squash.bind_squash #(steps fd em' h lt1) () (fun sts_fd ->
  FStar.Squash.bind_squash #(steps (ERead em') e' (h++lt1) lt2) () (fun sts_read ->
  construct_steps_eread fd em' h lt1 sts_fd;
  lem_steps_transitive (ERead fd) (ERead em') e' h lt1 lt2))
  end
  end
  end
#pop-options

#push-options "--z3rlimit 15"
let helper_equiv_oprod_close_steps (h:history) (lt:local_trace h)
  (fs_fd':fs_prod qFileDescr) (fs_r:fs_val (qResexn qUnit)) (fd:closed_exp) :
  Lemma
    (requires fs_beh (fs_prod_bind fs_fd' (fun fd' -> close fd')) h lt fs_r /\
              qFileDescr ⫃ (h, fs_fd', fd))
    (ensures exists e'. (qResexn qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EClose fd) e' h lt) =
  let fs_k : fs_val qFileDescr -> fs_prod (qResexn qUnit) = fun fd' -> close fd' in
  assert (fs_prod_bind fs_fd' fs_k == io_bind fs_fd' fs_k) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_fd' fs_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_fd_val:fs_val qFileDescr).
    lt == (lt1@lt2) /\ fs_beh fs_fd' h lt1 fs_fd_val /\ fs_beh (close fs_fd_val) (h++lt1) lt2 fs_r
    returns exists e'. (qResexn qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EClose fd) e' h lt with _. begin
  eliminate forall (lt':local_trace h) (fs_r':get_Type qFileDescr). fs_beh fs_fd' h lt' fs_r' ==> exists em'. qFileDescr ∈ (h++lt', fs_r', em') /\ e_beh fd em' h lt' with lt1 fs_fd_val;
  eliminate exists em'. qFileDescr ∈ (h++lt1, fs_fd_val, em') /\ e_beh fd em' h lt1
    returns exists e'. (qResexn qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EClose fd) e' h lt with _. begin
  lem_values_are_values qFileDescr (h++lt1) fs_fd_val em';
  trans_history h lt1 lt2;
  helper_equiv_oprod_close_oval_steps (h++lt1) lt2 fs_fd_val em' fs_r;
  eliminate exists e'. (qResexn qUnit) ∈ ((h++lt1)++lt2, fs_r, e') /\ e_beh (EClose em') e' (h++lt1) lt2
    returns exists e'. (qResexn qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EClose fd) e' h lt with _. begin
  FStar.Squash.bind_squash #(steps fd em' h lt1) () (fun sts_fd ->
  FStar.Squash.bind_squash #(steps (EClose em') e' (h++lt1) lt2) () (fun sts_close ->
  construct_steps_eclose fd em' h lt1 sts_fd;
  lem_steps_transitive (EClose fd) (EClose em') e' h lt1 lt2))
  end
  end
  end
#pop-options

#push-options "--z3rlimit 15 --split_queries always"
let helper_equiv_oprod_write_steps (h:history) (lt:local_trace h)
  (fs_fd':fs_prod qFileDescr) (fs_msg':fs_prod qString) (fs_r:fs_val (qResexn qUnit)) (fd msg:closed_exp) :
  Lemma
    (requires fs_beh (fs_prod_bind fs_fd' (fun fd' -> fs_prod_bind #qString #(qResexn qUnit) fs_msg' (fun msg' -> write (fd', msg')))) h lt fs_r /\
              qFileDescr ⫃ (h, fs_fd', fd) /\
              (forall (lt':local_trace h). qString ⫃ (h++lt', fs_msg', msg)))
    (ensures exists e'. (qResexn qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EWrite fd msg) e' h lt) =
  let fs_k1 : fs_val qFileDescr -> fs_prod (qResexn qUnit) = fun fd' -> fs_prod_bind #qString #(qResexn qUnit) fs_msg' (fun msg' -> write (fd', msg')) in
  assert (fs_prod_bind fs_fd' fs_k1 == io_bind fs_fd' fs_k1) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_fd' fs_k1 h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_fd_val:fs_val qFileDescr).
    lt == (lt1@lt2) /\ fs_beh fs_fd' h lt1 fs_fd_val /\ fs_beh (fs_k1 fs_fd_val) (h++lt1) lt2 fs_r
    returns exists e'. (qResexn qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EWrite fd msg) e' h lt with _. begin
  // Get fd value
  eliminate forall (lt':local_trace h) (fs_r':get_Type qFileDescr). fs_beh fs_fd' h lt' fs_r' ==> exists em'. qFileDescr ∈ (h++lt', fs_r', em') /\ e_beh fd em' h lt' with lt1 fs_fd_val;
  eliminate exists em_fd. qFileDescr ∈ (h++lt1, fs_fd_val, em_fd) /\ e_beh fd em_fd h lt1
    returns exists e'. (qResexn qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EWrite fd msg) e' h lt with _. begin
  lem_values_are_values qFileDescr (h++lt1) fs_fd_val em_fd;
  lem_value_is_irred em_fd;
  // Decompose inner bind: fs_prod_bind fs_msg' (fun msg' -> write (fs_fd_val, msg'))
  let fs_k2 : fs_val qString -> fs_prod (qResexn qUnit) = fun msg' -> write (fs_fd_val, msg') in
  assert (fs_prod_bind #qString #(qResexn qUnit) fs_msg' fs_k2 == io_bind fs_msg' fs_k2) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_msg' fs_k2 (h++lt1) lt2 fs_r;
  eliminate exists (lt2a:local_trace (h++lt1)) (lt2b:local_trace ((h++lt1)++lt2a)) (fs_msg_val:fs_val qString).
    lt2 == (lt2a@lt2b) /\ fs_beh fs_msg' (h++lt1) lt2a fs_msg_val /\ fs_beh (write (fs_fd_val, fs_msg_val)) ((h++lt1)++lt2a) lt2b fs_r
    returns exists e'. (qResexn qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EWrite fd msg) e' h lt with _. begin
  // Get msg value
  assert (qString ⫃ (h++lt1, fs_msg', msg));
  eliminate forall (lt':local_trace (h++lt1)) (fs_r':get_Type qString). fs_beh fs_msg' (h++lt1) lt' fs_r' ==> exists em'. qString ∈ ((h++lt1)++lt', fs_r', em') /\ e_beh msg em' (h++lt1) lt' with lt2a fs_msg_val;
  eliminate exists em_msg. qString ∈ ((h++lt1)++lt2a, fs_msg_val, em_msg) /\ e_beh msg em_msg (h++lt1) lt2a
    returns exists e'. (qResexn qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EWrite fd msg) e' h lt with _. begin
  lem_values_are_values qString ((h++lt1)++lt2a) fs_msg_val em_msg;
  trans_history h lt1 lt2a;
  trans_history (h++lt1) lt2a lt2b;
  trans_history h lt1 lt2;
  associative_history lt1 lt2a lt2b;
  // Use existing write oval helper at history (h++lt1)++lt2a
  val_type_closed_under_history_extension qFileDescr (h++lt1) fs_fd_val em_fd;
  helper_equiv_oprod_write_oval_steps ((h++lt1)++lt2a) lt2b fs_fd_val fs_msg_val em_fd em_msg fs_r;
  eliminate exists e'. (qResexn qUnit) ∈ (((h++lt1)++lt2a)++lt2b, fs_r, e') /\ e_beh (EWrite em_fd em_msg) e' ((h++lt1)++lt2a) lt2b
    returns exists e'. (qResexn qUnit) ∈ (h++lt, fs_r, e') /\ e_beh (EWrite fd msg) e' h lt with _. begin
  // Construct: EWrite fd msg -->* EWrite em_fd msg -->* EWrite em_fd em_msg -->* e'
  FStar.Squash.bind_squash #(steps fd em_fd h lt1) () (fun sts_fd ->
  construct_steps_ewrite_fd fd em_fd msg h lt1 sts_fd;
  FStar.Squash.bind_squash #(steps msg em_msg (h++lt1) lt2a) () (fun sts_msg ->
  construct_steps_ewrite_arg em_fd msg em_msg (h++lt1) lt2a sts_msg;
  lem_steps_transitive (EWrite fd msg) (EWrite em_fd msg) (EWrite em_fd em_msg) h lt1 lt2a;
  FStar.Squash.bind_squash #(steps (EWrite em_fd em_msg) e' ((h++lt1)++lt2a) lt2b) () (fun sts_wr ->
  lem_steps_transitive (EWrite fd msg) (EWrite em_fd em_msg) e' h (lt1@lt2a) lt2b)))
  end
  end
  end
  end
  end
#pop-options

(** ---- Case helper for bind decomposition ---- **)

#push-options "--z3rlimit 15"
let helper_equiv_oprod_case_steps (h:history) (lt:local_trace h) (a b c:qType)
  (fs_sc':fs_prod (a ^+ b))
  (fs_inlc:fs_val (a ^->!@ c))
  (fs_inrc:fs_val (b ^->!@ c))
  (fs_r:fs_val c)
  (e_sc:closed_exp)
  (e_lc:exp{is_closed (ELam e_lc)})
  (e_rc:exp{is_closed (ELam e_rc)}) :
  Lemma
    (requires fs_beh (fs_prod_bind fs_sc' (fun x -> fs_prod_case_val x fs_inlc fs_inrc)) h lt fs_r /\
              (a ^+ b) ⫃ (h, fs_sc', e_sc) /\
              (a ^->!@ c) ⊆ (h, fs_inlc, ELam e_lc) /\
              (b ^->!@ c) ⊆ (h, fs_inrc, ELam e_rc))
    (ensures exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_sc e_lc e_rc) e' h lt) =
  let fs_k : fs_val (a ^+ b) -> fs_prod c = fun x -> fs_prod_case_val x fs_inlc fs_inrc in
  assert (fs_prod_bind fs_sc' fs_k == io_bind fs_sc' fs_k) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_sc' fs_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_cond_val:fs_val (a ^+ b)).
    lt == (lt1@lt2) /\ fs_beh fs_sc' h lt1 fs_cond_val /\ fs_beh (fs_prod_case_val fs_cond_val fs_inlc fs_inrc) (h++lt1) lt2 fs_r
    returns exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_sc e_lc e_rc) e' h lt with _. begin
  // Get condition value
  eliminate forall (lt':local_trace h) (fs_r':get_Type (a ^+ b)). fs_beh fs_sc' h lt' fs_r' ==> exists em'. (a ^+ b) ∈ (h++lt', fs_r', em') /\ e_beh e_sc em' h lt' with lt1 fs_cond_val;
  eliminate exists em'. (a ^+ b) ∈ (h++lt1, fs_cond_val, em') /\ e_beh e_sc em' h lt1
    returns exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_sc e_lc e_rc) e' h lt with _. begin
  lem_values_are_values (a ^+ b) (h++lt1) fs_cond_val em';
  trans_history h lt1 lt2;
  // Convert (a ^+ b) ∈ to ⊆ at h++lt1
  lem_values_are_expressions (a ^+ b) (h++lt1) fs_cond_val em';
  // Shift ⊆ for inlc from h to h++lt1
  eliminate exists (elc':closed_exp). e_beh (ELam e_lc) elc' h [] /\ (a ^->!@ c) ∈ (h, fs_inlc, elc')
    returns (a ^->!@ c) ⊆ (h++lt1, fs_inlc, ELam e_lc) with _. begin
  steps_val_id (ELam e_lc) elc' h;
  val_type_closed_under_history_extension (a ^->!@ c) h fs_inlc (ELam e_lc);
  lem_values_are_expressions (a ^->!@ c) (h++lt1) fs_inlc (ELam e_lc)
  end;
  // Shift ⊆ for inrc from h to h++lt1
  eliminate exists (erc':closed_exp). e_beh (ELam e_rc) erc' h [] /\ (b ^->!@ c) ∈ (h, fs_inrc, erc')
    returns (b ^->!@ c) ⊆ (h++lt1, fs_inrc, ELam e_rc) with _. begin
  steps_val_id (ELam e_rc) erc' h;
  val_type_closed_under_history_extension (b ^->!@ c) h fs_inrc (ELam e_rc);
  lem_values_are_expressions (b ^->!@ c) (h++lt1) fs_inrc (ELam e_rc)
  end;
  helper_equiv_oprod_case_oval_steps (h++lt1) lt2 a b c fs_cond_val fs_inlc fs_inrc fs_r em' e_lc e_rc;
  eliminate exists e'. c ∈ ((h++lt1)++lt2, fs_r, e') /\ e_beh (ECase em' e_lc e_rc) e' (h++lt1) lt2
    returns exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_sc e_lc e_rc) e' h lt with _. begin
  FStar.Squash.bind_squash #(steps e_sc em' h lt1) () (fun sts_cond ->
  FStar.Squash.bind_squash #(steps (ECase em' e_lc e_rc) e' (h++lt1) lt2) () (fun sts_case ->
  construct_steps_ecase_cond e_sc em' e_lc e_rc h lt1 sts_cond;
  lem_steps_transitive (ECase e_sc e_lc e_rc) (ECase em' e_lc e_rc) e' h lt1 lt2))
  end
  end
  end
#pop-options

(** ---- Main compatibility lemma proofs ---- **)

#push-options "--split_queries always"
let equiv_oprod_pair #g
  (#t1 #t2:qType)
  (fs_e1:fs_oprod g t1) (fs_e2:fs_oprod g t2)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊑ e1 /\ fs_e2 ⊑ e2)
    (ensures fs_oprod_pair fs_e1 fs_e2 ⊑ EPair e1 e2) =
  lem_fv_in_env_pair g e1 e2;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> (t1 ^* t2) ⫃ (h, fs_oprod_pair fs_e1 fs_e2 fsG, gsubst s (EPair e1 e2)) with begin
    introduce _ ==> _ with _. begin
      let fs_e1' : fs_prod t1 = fs_e1 fsG in
      let fs_e2' : fs_prod t2 = fs_e2 fsG in
      let fs_e = fs_prod_bind fs_e1' (fun v1 -> fs_prod_bind #t2 #(t1 ^* t2) fs_e2' (fun v2 -> return (v1, v2))) in
      assert (fs_e == fs_oprod_pair fs_e1 fs_e2 fsG) by (
        norm [delta_only [`%fs_oprod_pair;`%fs_oprod_bind';`%fs_oprod_bind;`%fs_oprod_return_val;`%fs_val_pair]];
        l_to_r [`lem_hd_stack;`tail_stack_inverse];
        trefl ());
      let e = EPair (gsubst s e1) (gsubst s e2) in
      assert (gsubst s (EPair e1 e2) == e);
      let EPair e1 e2 = e in
      introduce fsG `(≍) h` s ==> (t1 ^* t2) ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val (t1 ^* t2)). fs_beh fs_e h lt fs_r ==> exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            helper_equiv_oprod_pair_steps h lt t1 t2 fs_e1' fs_e2' fs_r e1 e2
          end
        end
      end
    end
  end
#pop-options

#push-options "--z3rlimit 30 --split_queries always"
let helper_equiv_oprod_string_eq_steps (h:history) (lt:local_trace h)
  (fs_e1':fs_prod qString) (fs_e2':fs_prod qString) (fs_r:fs_val qBool) (e1 e2:closed_exp) :
  Lemma
    (requires fs_beh (fs_prod_bind fs_e1' (fun v1 -> fs_prod_bind #qString #qBool fs_e2' (fun v2 -> return (v1 = v2)))) h lt fs_r /\
              qString ⫃ (h, fs_e1', e1) /\
              (forall (lt':local_trace h). qString ⫃ (h++lt', fs_e2', e2)))
    (ensures exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh (EStringEq e1 e2) e' h lt) =
  let fs_k1 : fs_val qString -> fs_prod qBool = fun v1 -> fs_prod_bind #qString #qBool fs_e2' (fun v2 -> return (v1 = v2)) in
  assert (fs_prod_bind fs_e1' fs_k1 == io_bind fs_e1' fs_k1) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_e1' fs_k1 h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_v1:fs_val qString).
    lt == (lt1@lt2) /\ fs_beh fs_e1' h lt1 fs_v1 /\ fs_beh (fs_k1 fs_v1) (h++lt1) lt2 fs_r
    returns exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh (EStringEq e1 e2) e' h lt with _. begin
  // Get e1 value
  eliminate forall (lt':local_trace h) (fs_r':get_Type qString). fs_beh fs_e1' h lt' fs_r' ==> exists em'. qString ∈ (h++lt', fs_r', em') /\ e_beh e1 em' h lt' with lt1 fs_v1;
  eliminate exists em1. qString ∈ (h++lt1, fs_v1, em1) /\ e_beh e1 em1 h lt1
    returns exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh (EStringEq e1 e2) e' h lt with _. begin
  lem_values_are_values qString (h++lt1) fs_v1 em1;
  lem_value_is_irred em1;
  let EString s1 = em1 in
  // Decompose inner bind: fs_prod_bind fs_e2' (fun v2 -> return (fs_v1 = v2))
  let fs_k2 : fs_val qString -> fs_prod qBool = fun v2 -> return (fs_v1 = v2) in
  assert (fs_prod_bind #qString #qBool fs_e2' fs_k2 == io_bind fs_e2' fs_k2) by (norm [delta_only [`%fs_prod_bind]]; trefl ());
  destruct_fs_beh fs_e2' fs_k2 (h++lt1) lt2 fs_r;
  eliminate exists (lt2a:local_trace (h++lt1)) (lt2b:local_trace ((h++lt1)++lt2a)) (fs_v2:fs_val qString).
    lt2 == (lt2a@lt2b) /\ fs_beh fs_e2' (h++lt1) lt2a fs_v2 /\ fs_beh (return (fs_v1 = fs_v2)) ((h++lt1)++lt2a) lt2b fs_r
    returns exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh (EStringEq e1 e2) e' h lt with _. begin
  let val_ : bool = (fs_v1 = fs_v2) in
  theta_monad_morphism_ret val_;
  let p : hist_post ((h++lt1)++lt2a) bool = fun lt' r' -> lt' == [] /\ r' == val_ in
  assert (hist_return val_ ((h++lt1)++lt2a) p);
  assert (theta (io_return val_) ((h++lt1)++lt2a) p);
  assert (thetaP (io_return val_) ((h++lt1)++lt2a) lt2b fs_r);
  assert (p lt2b fs_r);
  assert (lt2b == []);
  assert (fs_r == val_);
  unit_l lt2a;
  // Get e2 value
  assert (qString ⫃ (h++lt1, fs_e2', e2));
  eliminate forall (lt':local_trace (h++lt1)) (fs_r':get_Type qString). fs_beh fs_e2' (h++lt1) lt' fs_r' ==> exists em'. qString ∈ ((h++lt1)++lt', fs_r', em') /\ e_beh e2 em' (h++lt1) lt' with lt2a fs_v2;
  eliminate exists em2. qString ∈ ((h++lt1)++lt2a, fs_v2, em2) /\ e_beh e2 em2 (h++lt1) lt2a
    returns exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh (EStringEq e1 e2) e' h lt with _. begin
  lem_values_are_values qString ((h++lt1)++lt2a) fs_v2 em2;
  lem_value_is_irred em2;
  let EString s2 = em2 in
  trans_history h lt1 lt2a;
  val_type_closed_under_history_extension qString (h++lt1) fs_v1 em1;
  let result = if s1 = s2 then ETrue else EFalse in
  let _ : step (EStringEq (EString s1) (EString s2)) result (h++(lt1@lt2a)) None = StringEqReturn s1 s2 (h++(lt1@lt2a)) in
  lem_step_implies_steps (EStringEq (EString s1) (EString s2)) result (h++(lt1@lt2a)) None;
  lem_value_is_irred result;
  // Construct: EStringEq e1 e2 -->* EStringEq (EString s1) (EString s2) --> result
  FStar.Squash.bind_squash #(steps e1 em1 h lt1) () (fun sts1 ->
  FStar.Squash.bind_squash #(steps e2 em2 (h++lt1) lt2a) () (fun sts2 ->
  construct_steps_estringeq e1 em1 e2 em2 h lt1 lt2a sts1 sts2;
  lem_steps_transitive (EStringEq e1 e2) (EStringEq (EString s1) (EString s2)) result h (lt1@lt2a) []))
  end
  end
  end
  end
#pop-options

#push-options "--split_queries always"
let equiv_oprod_string_eq #g
  (fs_e1:fs_oprod g qString) (fs_e2:fs_oprod g qString)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊑ e1 /\ fs_e2 ⊑ e2)
    (ensures fs_oprod_string_eq fs_e1 fs_e2 ⊑ EStringEq e1 e2) =
  lem_fv_in_env_string_eq g e1 e2;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> qBool ⫃ (h, fs_oprod_string_eq fs_e1 fs_e2 fsG, gsubst s (EStringEq e1 e2)) with begin
    introduce _ ==> _ with _. begin
      let fs_e1' : fs_prod qString = fs_e1 fsG in
      let fs_e2' : fs_prod qString = fs_e2 fsG in
      let fs_e = fs_prod_bind fs_e1' (fun v1 -> fs_prod_bind #qString #qBool fs_e2' (fun v2 -> return (v1 = v2))) in
      assert (fs_e == fs_oprod_string_eq fs_e1 fs_e2 fsG) by (
        norm [delta_only [`%fs_oprod_string_eq;`%fs_oprod_bind';`%fs_oprod_bind;`%fs_oprod_return_val]];
        l_to_r [`lem_hd_stack;`tail_stack_inverse];
        trefl ());
      let e = EStringEq (gsubst s e1) (gsubst s e2) in
      assert (gsubst s (EStringEq e1 e2) == e);
      let EStringEq e1 e2 = e in
      introduce fsG `(≍) h` s ==> qBool ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val qBool). fs_beh fs_e h lt fs_r ==> exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            helper_equiv_oprod_string_eq_steps h lt fs_e1' fs_e2' fs_r e1 e2
          end
        end
      end
    end
  end
#pop-options

#push-options "--split_queries always"
let equiv_oprod_fst #g
  (#t1 #t2:qType)
  (fs_e12:fs_oprod g (t1 ^* t2))
  (e12:exp)
  : Lemma
    (requires fs_e12 ⊑ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures fs_oprod_fmap fs_e12 fst ⊑ (EFst e12))
  =
  lem_fv_in_env_fst g e12;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> t1 ⫃ (h, (fs_oprod_fmap #g #(t1 ^* t2) #t1 fs_e12 fst) fsG, gsubst s (EFst e12)) with begin
    introduce _ ==> _ with _. begin
      let fs_e12' : fs_prod (t1 ^* t2) = fs_e12 fsG in
      let fs_e = fs_prod_bind #(t1 ^* t2) #t1 fs_e12' (fun v -> return (fst #(fs_val t1) #(fs_val t2) v)) in
      assert (fs_e == (fs_oprod_fmap #g #(t1 ^* t2) #t1 fs_e12 fst) fsG) by (
        norm [delta_only [`%fs_oprod_fmap;`%fs_oprod_bind';`%fs_oprod_bind;`%fs_oprod_return_val]];
        l_to_r [`lem_hd_stack;`tail_stack_inverse];
        trefl ());
      let e = EFst (gsubst s e12) in
      assert (gsubst s (EFst e12) == e);
      let EFst e12 = e in
      introduce fsG `(≍) h` s ==> t1 ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val t1). fs_beh fs_e h lt fs_r ==> exists e'. t1 ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. t1 ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            helper_equiv_oprod_fmap_fst_steps h lt t1 t2 fs_e12' fs_r e12
          end
        end
      end
    end
  end
#pop-options

#push-options "--split_queries always"
let equiv_oprod_snd #g (#t1 #t2:qType) (fs_e12:fs_oprod g (t1 ^* t2)) (e12:exp)
  : Lemma
    (requires fs_e12 ⊑ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures fs_oprod_fmap fs_e12 snd ⊑ (ESnd e12)) =
  lem_fv_in_env_snd g e12;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> t2 ⫃ (h, (fs_oprod_fmap #g #(t1 ^* t2) #t2 fs_e12 snd) fsG, gsubst s (ESnd e12)) with begin
    introduce _ ==> _ with _. begin
      let fs_e12' : fs_prod (t1 ^* t2) = fs_e12 fsG in
      let fs_e = fs_prod_bind #(t1 ^* t2) #t2 fs_e12' (fun v -> return (snd #(fs_val t1) #(fs_val t2) v)) in
      assert (fs_e == (fs_oprod_fmap #g #(t1 ^* t2) #t2 fs_e12 snd) fsG) by (
        norm [delta_only [`%fs_oprod_fmap;`%fs_oprod_bind';`%fs_oprod_bind;`%fs_oprod_return_val]];
        l_to_r [`lem_hd_stack;`tail_stack_inverse];
        trefl ());
      let e = ESnd (gsubst s e12) in
      assert (gsubst s (ESnd e12) == e);
      let ESnd e12 = e in
      introduce fsG `(≍) h` s ==> t2 ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val t2). fs_beh fs_e h lt fs_r ==> exists e'. t2 ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. t2 ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            helper_equiv_oprod_fmap_snd_steps h lt t1 t2 fs_e12' fs_r e12
          end
        end
      end
    end
  end
#pop-options

#push-options "--split_queries always"
let equiv_oprod_case #g (#a #b #c:qType)
  (fs_cond:fs_oprod g (a ^+ b))
  (fs_inlc:fs_oprod (extend a g) c)
  (fs_inrc:fs_oprod (extend b g) c)
  (cond inlc inrc:exp)
  : Lemma
    (requires fs_cond ⊑ cond /\ fs_inlc ⊑ inlc /\ fs_inrc ⊑ inrc)
    (ensures (fs_oprod_case fs_cond fs_inlc fs_inrc) ⊑ (ECase cond inlc inrc)) =
  lem_fv_in_env_case g a b cond inlc inrc;
  lem_fv_in_env_lam g a inlc;
  lem_fv_in_env_lam g b inrc;
  equiv_oval_lambda_oprod fs_inlc inlc;
  equiv_oval_lambda_oprod fs_inrc inrc;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> c ⫃ (h, fs_oprod_case fs_cond fs_inlc fs_inrc fsG, gsubst s (ECase cond inlc inrc)) with begin
    introduce _ ==> _ with _. begin
      let fs_sc : fs_prod (a ^+ b) = fs_cond fsG in
      let fs_il : fs_val (a ^->!@ c) = fun x -> fs_inlc (stack fsG x) in
      let fs_ir : fs_val (b ^->!@ c) = fun x -> fs_inrc (stack fsG x) in
      let fs_e = fs_prod_bind fs_sc (fun x -> fs_prod_case_val x fs_il fs_ir) in
      assert (fs_e == fs_oprod_case fs_cond fs_inlc fs_inrc fsG) by (
        norm [delta_only [`%fs_oprod_case;`%fs_prod_case_val;`%fs_oprod_bind';`%fs_oprod_bind;`%fs_oprod_case_val]];
        l_to_r [`lem_hd_stack;`tail_stack_inverse];
        trefl ());
      let e = ECase (gsubst s cond) (subst (sub_elam s) inlc) (subst (sub_elam s) inrc) in
      assert (gsubst s (ECase cond inlc inrc) == e);
      let ECase e_sc e_il e_ir = e in
      introduce fsG `(≍) h` s ==> c ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val c). fs_beh fs_e h lt fs_r ==> exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            helper_equiv_oprod_case_steps h lt a b c fs_sc fs_il fs_ir fs_r e_sc e_il e_ir
          end
        end
      end
    end
  end
#pop-options

#push-options "--split_queries always"
let equiv_oprod_inl #g (t1 t2:qType) (fs_e:fs_oprod g t1) (e:exp)
  : Lemma
    (requires fs_e ⊑ e)
    (ensures fs_oprod_fmap #g #t1 #(t1 ^+ t2) fs_e Inl ⊑ (EInl e))
  =
  lem_fv_in_env_inl g e;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> (t1 ^+ t2) ⫃ (h, (fs_oprod_fmap #g #t1 #(t1 ^+ t2) fs_e Inl) fsG, gsubst s (EInl e)) with begin
    introduce _ ==> _ with _. begin
      let fs_e' : fs_prod t1 = fs_e fsG in
      let fs_ex = fs_prod_bind #t1 #(t1 ^+ t2) fs_e' (fun v -> return (Inl #(fs_val t1) #(fs_val t2) v)) in
      assert (fs_ex == (fs_oprod_fmap #g #t1 #(t1 ^+ t2) fs_e Inl) fsG) by (
        norm [delta_only [`%fs_oprod_fmap;`%fs_oprod_bind';`%fs_oprod_bind;`%fs_oprod_return_val]];
        l_to_r [`lem_hd_stack;`tail_stack_inverse];
        trefl ());
      let ex = EInl (gsubst s e) in
      assert (gsubst s (EInl e) == ex);
      let EInl e = ex in
      introduce fsG `(≍) h` s ==> (t1 ^+ t2) ⫃ (h, fs_ex, ex) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val (t1 ^+ t2)). fs_beh fs_ex h lt fs_r ==> exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh ex e' h lt with begin
          introduce fs_beh fs_ex h lt fs_r ==> exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh ex e' h lt with _. begin
            helper_equiv_oprod_fmap_inl_steps h lt t1 t2 fs_e' fs_r e
          end
        end
      end
    end
  end
#pop-options

#push-options "--split_queries always"
let equiv_oprod_inr #g (t1 t2:qType) (fs_e:fs_oprod g t2) (e:exp)
  : Lemma
    (requires fs_e ⊑ e)
    (ensures fs_oprod_fmap #g #t2 #(t1 ^+ t2) fs_e Inr ⊑ (EInr e))
  =
  lem_fv_in_env_inr g e;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> (t1 ^+ t2) ⫃ (h, (fs_oprod_fmap #g #t2 #(t1 ^+ t2) fs_e Inr) fsG, gsubst s (EInr e)) with begin
    introduce _ ==> _ with _. begin
      let fs_e' : fs_prod t2 = fs_e fsG in
      let fs_ex = fs_prod_bind #t2 #(t1 ^+ t2) fs_e' (fun v -> return (Inr #(fs_val t1) #(fs_val t2) v)) in
      assert (fs_ex == (fs_oprod_fmap #g #t2 #(t1 ^+ t2) fs_e Inr) fsG) by (
        norm [delta_only [`%fs_oprod_fmap;`%fs_oprod_bind';`%fs_oprod_bind;`%fs_oprod_return_val]];
        l_to_r [`lem_hd_stack;`tail_stack_inverse];
        trefl ());
      let ex = EInr (gsubst s e) in
      assert (gsubst s (EInr e) == ex);
      let EInr e = ex in
      introduce fsG `(≍) h` s ==> (t1 ^+ t2) ⫃ (h, fs_ex, ex) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val (t1 ^+ t2)). fs_beh fs_ex h lt fs_r ==> exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh ex e' h lt with begin
          introduce fs_beh fs_ex h lt fs_r ==> exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh ex e' h lt with _. begin
            helper_equiv_oprod_fmap_inr_steps h lt t1 t2 fs_e' fs_r e
          end
        end
      end
    end
  end
#pop-options

#push-options "--split_queries always"
let equiv_oprod_openfile #g (fs_fnm:fs_oprod g qString) (fnm:exp)
  : Lemma
    (requires fs_fnm ⊑ fnm)
    (ensures fs_oprod_openfile fs_fnm ⊑ EOpen fnm)
  =
  lem_fv_in_env_openfile g fnm;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> (qResexn qFileDescr) ⫃ (h, (fs_oprod_openfile fs_fnm) fsG, gsubst s (EOpen fnm)) with begin
    introduce _ ==> _ with _. begin
      let fs_fnm' : fs_prod qString = fs_fnm fsG in
      let fs_e = fs_prod_bind fs_fnm' (fun fnm' -> openfile fnm') in
      assert (fs_e == (fs_oprod_openfile fs_fnm) fsG) by (
        norm [delta_only [`%fs_oprod_openfile;`%fs_oprod_bind';`%fs_oprod_bind;`%fs_oprod_return_prod]];
        l_to_r [`lem_hd_stack;`tail_stack_inverse];
        trefl ());
      let e = EOpen (gsubst s fnm) in
      assert (gsubst s (EOpen fnm) == e);
      let EOpen fnm = e in
      introduce fsG `(≍) h` s ==> (qResexn qFileDescr) ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val (qResexn qFileDescr)). fs_beh fs_e h lt fs_r ==> exists e'. (qResexn qFileDescr) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. (qResexn qFileDescr) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            helper_equiv_oprod_openfile_steps h lt fs_fnm' fs_r fnm
          end
        end
      end
    end
  end
#pop-options

#push-options "--split_queries always"
let equiv_oprod_read #g (fs_fd:fs_oprod g qFileDescr) (fd:exp)
  : Lemma
    (requires fs_fd ⊑ fd)
    (ensures fs_oprod_read fs_fd ⊑ ERead fd)
  =
  lem_fv_in_env_read g fd;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> (qResexn qString) ⫃ (h, (fs_oprod_read fs_fd) fsG, gsubst s (ERead fd)) with begin
    introduce _ ==> _ with _. begin
      let fs_fd' : fs_prod qFileDescr = fs_fd fsG in
      let fs_e = fs_prod_bind fs_fd' (fun fd' -> read fd') in
      assert (fs_e == (fs_oprod_read fs_fd) fsG) by (
        norm [delta_only [`%fs_oprod_read;`%fs_oprod_bind';`%fs_oprod_bind;`%fs_oprod_return_prod]];
        l_to_r [`lem_hd_stack;`tail_stack_inverse];
        trefl ());
      let e = ERead (gsubst s fd) in
      assert (gsubst s (ERead fd) == e);
      let ERead fd = e in
      introduce fsG `(≍) h` s ==> (qResexn qString) ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val (qResexn qString)). fs_beh fs_e h lt fs_r ==> exists e'. (qResexn qString) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. (qResexn qString) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            helper_equiv_oprod_read_steps h lt fs_fd' fs_r fd
          end
        end
      end
    end
  end
#pop-options

#push-options "--split_queries always"
let equiv_oprod_write #g (fs_fd:fs_oprod g qFileDescr) (fs_msg:fs_oprod g qString) (fd msg:exp)
  : Lemma
    (requires fs_fd ⊑ fd /\ fs_msg ⊑ msg)
    (ensures fs_oprod_write fs_fd fs_msg ⊑ EWrite fd msg)
  =
  lem_fv_in_env_write g fd msg;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> (qResexn qUnit) ⫃ (h, (fs_oprod_write fs_fd fs_msg) fsG, gsubst s (EWrite fd msg)) with begin
    introduce _ ==> _ with _. begin
      let fs_fd' : fs_prod qFileDescr = fs_fd fsG in
      let fs_msg' : fs_prod qString = fs_msg fsG in
      let fs_e = fs_prod_bind fs_fd' (fun fd' -> fs_prod_bind #qString #(qResexn qUnit) fs_msg' (fun msg' -> write (fd', msg'))) in
      assert (fs_e == (fs_oprod_write fs_fd fs_msg) fsG) by (
        norm [delta_only [`%fs_oprod_write;`%fs_oprod_bind';`%fs_oprod_bind;`%fs_oprod_return_prod]];
        l_to_r [`lem_hd_stack;`tail_stack_inverse];
        trefl ());
      let e = EWrite (gsubst s fd) (gsubst s msg) in
      assert (gsubst s (EWrite fd msg) == e);
      let EWrite fd msg = e in
      introduce fsG `(≍) h` s ==> (qResexn qUnit) ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val (qResexn qUnit)). fs_beh fs_e h lt fs_r ==> exists e'. (qResexn qUnit) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. (qResexn qUnit) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            helper_equiv_oprod_write_steps h lt fs_fd' fs_msg' fs_r fd msg
          end
        end
      end
    end
  end
#pop-options

#push-options "--split_queries always"
let equiv_oprod_close #g (fs_fd:fs_oprod g qFileDescr) (fd:exp)
  : Lemma
    (requires fs_fd ⊑ fd)
    (ensures fs_oprod_close fs_fd ⊑ EClose fd)
  =
  lem_fv_in_env_close g fd;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> (qResexn qUnit) ⫃ (h, (fs_oprod_close fs_fd) fsG, gsubst s (EClose fd)) with begin
    introduce _ ==> _ with _. begin
      let fs_fd' : fs_prod qFileDescr = fs_fd fsG in
      let fs_e = fs_prod_bind fs_fd' (fun fd' -> close fd') in
      assert (fs_e == (fs_oprod_close fs_fd) fsG) by (
        norm [delta_only [`%fs_oprod_close;`%fs_oprod_bind';`%fs_oprod_bind;`%fs_oprod_return_prod]];
        l_to_r [`lem_hd_stack;`tail_stack_inverse];
        trefl ());
      let e = EClose (gsubst s fd) in
      assert (gsubst s (EClose fd) == e);
      let EClose fd = e in
      introduce fsG `(≍) h` s ==> (qResexn qUnit) ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val (qResexn qUnit)). fs_beh fs_e h lt fs_r ==> exists e'. (qResexn qUnit) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. (qResexn qUnit) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            helper_equiv_oprod_close_steps h lt fs_fd' fs_r fd
          end
        end
      end
    end
  end
#pop-options
