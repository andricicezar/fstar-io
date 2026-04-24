module LogRelSourceTarget.CompatibilityLemmas

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open LambdaIO
open LambdaIO.ConstructLemmas
open IOStar
open IOStar.DestructLemmas
open QTypes.Subst
open QTypes.OpenValComp
open QTypes.HelperTactics
open LogRelSourceTarget

let bind_squash (a #b:Type) (f:a -> GTot (squash b)) : Pure (squash b) (requires a) (ensures fun _ -> True) = 
  FStar.Squash.bind_squash #a () f

let compat_oval_unit g : Lemma (fs_oval_return g #qUnit () ⊏ EUnit) =
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> qUnit ⊆ (h, (), gsubst s EUnit) with begin
    introduce _ ==> _ with _. begin
      assert (qUnit ∈ (h, (), EUnit));
      lem_values_are_expressions qUnit h () EUnit
    end
  end

let compat_oval_true g : Lemma (fs_oval_return g #qBool true ⊏ ETrue) =
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> qBool ⊆ (h, true, gsubst s ETrue) with begin
    introduce _ ==> _ with _. begin
      assert (qBool ∈ (h, true, ETrue));
      lem_values_are_expressions qBool h true ETrue
    end
  end

let compat_oval_false g : Lemma (fs_oval_return g #qBool false ⊏ EFalse) =
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> qBool ⊆ (h, false, gsubst s EFalse) with begin
    introduce _ ==> _ with _. begin
      assert (qBool ∈ (h, false, EFalse));
      lem_values_are_expressions qBool h false EFalse
    end
  end

let compat_oval_file_descr g fd : Lemma (fs_oval_return g #qFileDescr fd ⊏ EFileDescr fd) =
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> qFileDescr ⊆ (h, fd, gsubst s (EFileDescr fd)) with begin
    introduce _ ==> _ with _. begin
      assert (qFileDescr ∈ (h, fd, (EFileDescr fd)));
      lem_values_are_expressions qFileDescr h fd (EFileDescr fd)
    end
  end

let compat_oval_string g (str:string) : Lemma (fs_oval_return g #qString str ⊏ EString str) =
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> qString ⊆ (h, str, gsubst s (EString str)) with begin
    introduce _ ==> _ with _. begin
      assert (qString ∈ (h, str, EString str));
      lem_values_are_expressions qString h str (EString str)
    end
  end

#push-options "--z3rlimit 10"
let helper_compat_oval_string_eq_steps (h:history) (fs_e1:fs_val qString) (fs_e2:fs_val qString) (e1 e2:closed_exp) :
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

let compat_oval_string_eq #g #preS1 #preS2
  (fs_e1:fs_oval g qString preS1) (fs_e2:fs_oval g qString preS2)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊏ e1 /\ fs_e2 ⊏ e2)
    (ensures fs_oval_eq_string fs_e1 fs_e2 ⊏ EStringEq e1 e2) =
  lem_fv_in_env_string_eq g e1 e2;
  introduce forall b (s:gsub g b) fsG h. (fsG `(≍) h` s /\ (spec_env_app preS1 preS2) fsG) ==> qBool ⊆ (h, (fs_e1 fsG = fs_e2 fsG), gsubst s (EStringEq e1 e2)) with begin
    let preS1 = preS1 fsG in
    let preS2 = preS2 fsG in
    let pre = (preS1 /\ preS2) in
    let fs_e1 () : Pure (fs_val qString) (requires preS1) (ensures (fun _ -> True)) = fs_e1 fsG in
    let fs_e2 () : Pure (fs_val qString) (requires preS2) (ensures (fun _ -> True)) = fs_e2 fsG in
    let fs_e () : Pure (fs_val qBool) (requires pre) (ensures (fun _ -> True)) = (fs_e1 () = fs_e2 ()) in
    let e = EStringEq (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EStringEq e1 e2) == e);
    let EStringEq e1 e2 = e in
    introduce (fsG `(≍) h` s /\ pre) ==> qBool ⊆ (h, fs_e (), e) with _. begin
      helper_compat_oval_string_eq_steps h (fs_e1 ()) (fs_e2 ()) e1 e2
    end
  end

(** Used in backtranslation **)
let compat_oval_var g (x:var{Some? (g x)}) : Lemma (fs_oval_var g x ⊏ EVar x) =
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> Some?.v (g x) ⊆ (h, index fsG x, gsubst s (EVar x)) with begin
    introduce _ ==> _ with _. begin
      assert (Some?.v (g x) ∈ (h, index fsG x, s x));
      lem_values_are_expressions (Some?.v (g x)) h (index fsG x) (s x)
    end
  end

(** Used in compilation **)
let compat_oval_axiom (g:typ_env) (t:qType) : Lemma (fs_oval_axiom g t ⊏ EVar 0) =
  introduce forall b (s:gsub (extend t g) b) fsG h. fsG `(≍) h` s ==>  t ⊆ (h, hd fsG, gsubst s (EVar 0)) with begin
    introduce _ ==> _ with _. begin
      lem_index_0_hd fsG;
      assert (t ∈ (h, hd fsG, s 0));
      lem_values_are_expressions t h (hd fsG) (s 0)
    end
  end

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
 (** Used in compilation **)
let compat_weaken (#g:typ_env) #a #t #pre (s:fs_oval g a pre) (e:exp)
  : Lemma
      (requires (s ⊏ e))
      (ensures (fs_oval_weaken t s ⊏ subst sub_inc e))
  =
  lem_fv_in_env_weaken g t e;
  introduce forall b (s':gsub (extend t g) b) (fsG:eval_env (extend t g)) (h:history). (fsG `(≍) h` s' /\ (spec_env_weaken pre) fsG) ==> a ⊆ (h, s (tail fsG), gsubst s' (subst sub_inc e)) with begin
    introduce (fsG `(≍) h` s' /\ (spec_env_weaken pre) fsG) ==> a ⊆ (h, s (tail fsG), gsubst s' (subst sub_inc e)) with _. begin
      lem_index_tail fsG;
      let f : var -> exp = fun (y:var) -> s' (y+1) in
      introduce (forall (x:var{x>0}). EVar? (s' x)) ==> a ⊆ (h, s (tail fsG), gsubst s' (subst sub_inc e)) with _. begin
        eliminate forall b_ (s_:gsub g b_) (fsG_:eval_env g) (h_:history). (fsG_ `(≍) h_` s_  /\ pre fsG_) ==> a ⊆ (h_, s fsG_, gsubst s_ e) with true f (tail fsG) h;
        shift_sub_equiv_sub_inc_rename #t s' e f
      end;
      introduce (~(forall (x:var{x>0}). EVar? (s' x))) ==> ((spec_env_weaken pre) fsG /\ a ⊆ (h, s (tail fsG), gsubst s' (subst sub_inc e))) with _. begin
        eliminate forall b_ (s_:gsub g b_) (fsG_:eval_env g) (h_:history). (fsG_ `(≍) h_` s_ /\ pre fsG_)  ==> a ⊆ (h_, s fsG_, gsubst s_ e) with false f (tail fsG) h;
        shift_sub_equiv_sub_inc_no_rename #t #g s' e f
      end
    end
  end
#pop-options

let compat_oval_lambda #g (#t1:qType) (#preBody:spec_env (extend t1 g)) (#t2:qType) (fs_body:fs_oval (extend t1 g) t2 preBody) (body:exp) : Lemma
  (requires fs_body ⊏ body)
  (ensures (fs_oval_lambda fs_body ⊏ ELam body)) =
  lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  let f : fs_oval g (t1 ^-> t2) (spec_env_lambda_tot preBody) = fun fsG x -> fs_body (stack fsG x) in
  introduce forall b (s:gsub g b) fsG h. (fsG `(≍) h` s /\ (spec_env_lambda_tot preBody) fsG) ==> (t1 ^-> t2) ⊆ (h, f fsG, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∈ (h++lt_v, fs_v, v) ==> t2 ⊆ (h++lt_v, f fsG fs_v, subst_beta v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fsG' = stack fsG fs_v in
          let h' = h++lt_v in
          let f' () : Pure (fs_val (t1 ^-> t2)) (requires ((spec_env_lambda_tot preBody) fsG)) (ensures (fun _ -> True)) = f (tail #t1 fsG') in
          let f' : fs_val t2 = f' () (hd #t1 #g fsG') in
          assert ((fsG' `(≍) h'` s' /\ preBody fsG') ==> t2 ⊆ (h', f', gsubst s' body));
          assert (fsG `(≍) h` s);
          assert (t1 ∈ (h++lt_v, fs_v, v));
          introduce forall (x:var). Some? (g x) ==> Some?.v (g x) ∈ (h++lt_v, index fsG x, s x) with begin
            introduce _ ==> _ with _. begin
              val_type_closed_under_history_extension (Some?.v (g x)) h (index fsG x) (s x)
            end
          end;
          assert (stack fsG fs_v `(≍) h'` gsub_extend s t1 v);
          assert (t2 ⊆ (h', f', (gsubst s' body)));
          assert (hd (stack fsG fs_v) == fs_v);
          lem_substitution s t1 v body;
          assert (t2 ⊆ (h', f', subst_beta v body'))
        end
      end;
      assert ((t1 ^-> t2) ∈ (h, f fsG, gsubst s (ELam body)));
      lem_values_are_expressions (t1 ^-> t2) h (f fsG) (gsubst s (ELam body));
      assert ((t1 ^-> t2) ⊆ (h, f fsG, gsubst s (ELam body)))
    end
  end

let helper_compat_oval_app_steps (h:history) (lt:local_trace h) (t1 t2:qType) (fs_e1:fs_val (t1 ^-> t2)) (fs_e2:fs_val t1) (e1 e2:closed_exp) :
  Lemma 
    (requires (t1 ^-> t2) ⊆ (h, fs_e1, e1) /\
              (forall (lt:local_trace h). t1 ⊆ (h++lt, fs_e2, e2)))
    (ensures exists (e':closed_exp). e_beh (EApp e1 e2) e' h [] /\ t2 ∈ (h, fs_e1 fs_e2, e')) =
  eliminate exists (e1':closed_exp). e_beh e1 e1' h [] /\ (t1 ^-> t2) ∈ (h, fs_e1, e1')
    returns exists (e':closed_exp). e_beh (EApp e1 e2) e' h [] /\ t2 ∈ (h, fs_e1 fs_e2, e') with _. begin
  let ELam e11 = e1' in
  unfold_contains_arrow t1 t2 h fs_e1 e11;
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

let compat_oval_app #g #preS1 #preS2
  (#t1:qType) (#t2:qType)
  (fs_e1:fs_oval g (t1 ^-> t2) preS1) (fs_e2:fs_oval g t1 preS2)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊏ e1 /\ fs_e2 ⊏ e2)
    (ensures fs_oval_app fs_e1 fs_e2 ⊏ EApp e1 e2) =
  lem_fv_in_env_app g e1 e2;
  introduce forall b (s:gsub g b) fsG h. (fsG `(≍) h` s /\ (spec_env_app preS1 preS2) fsG) ==> t2 ⊆ (h, (fs_e1 fsG) (fs_e2 fsG), gsubst s (EApp e1 e2)) with begin
    let preS1 = preS1 fsG in
    let preS2 = preS2 fsG in
    let pre = (preS1 /\ preS2) in
    let fs_e1 () : Pure (fs_val (t1 ^-> t2)) (requires preS1) (ensures (fun _ -> True)) = fs_e1 fsG in
    let fs_e2 () : Pure (fs_val t1) (requires preS2) (ensures (fun _ -> True)) = fs_e2 fsG in
    let fs_e () : Pure (fs_val t2) (requires pre) (ensures (fun _ -> True)) = (fs_e1 ()) (fs_e2 ()) in
    let e = EApp (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EApp e1 e2) == e);
    let EApp e1 e2 = e in
    introduce (fsG `(≍) h` s /\ pre) ==> t2 ⊆ (h, fs_e (), e) with _. begin
      lem_shift_type_value_environments h fsG s;
      helper_compat_oval_app_steps h [] t1 t2 (fs_e1 ()) (fs_e2 ()) e1 e2
    end
  end

let helper_compat_oval_if_steps (h:history) (t:qType) (fs_c:fs_val qBool) (fs_r:fs_val t) (c e_t e_f:closed_exp) :
  Lemma
    (requires qBool ⊆ (h, fs_c, c) /\
              (if fs_c then t ⊆ (h, fs_r, e_t) else t ⊆ (h, fs_r, e_f)))
    (ensures exists (e':closed_exp). e_beh (EIf c e_t e_f) e' h [] /\ t ∈ (h, fs_r, e')) =
  eliminate exists (c':closed_exp). e_beh c c' h [] /\ qBool ∈ (h, fs_c, c')
    returns exists (e':closed_exp). e_beh (EIf c e_t e_f) e' h [] /\ t ∈ (h, fs_r, e') with _. begin
  eliminate exists (e':closed_exp). e_beh (if fs_c then e_t else e_f) e' h [] /\ t ∈ (h, fs_r, e')
    returns exists (e':closed_exp). e_beh (EIf c e_t e_f) e' h [] /\ t ∈ (h, fs_r, e') with _. begin
  FStar.Squash.bind_squash #(steps c c' h []) () (fun sts1 ->
    FStar.Squash.bind_squash #(steps (if fs_c then e_t else e_f) e' h []) () (fun sts2 ->
      construct_steps_eif c c' e_t e_f e' h [] [] sts1 sts2))
    end
  end

let compat_oval_if #g
  (#t:qType) #preC #preT #preE
  (fs_e1:fs_oval g qBool preC) (fs_e2:fs_oval g t preT) (fs_e3:fs_oval g t preE)
  (e1:exp) (e2:exp) (e3:exp)
  : Lemma
    (requires fs_e1 ⊏ e1 /\ fs_e2 ⊏ e2 /\ fs_e3 ⊏ e3)
    (ensures fs_oval_if fs_e1 fs_e2 fs_e3 ⊏ EIf e1 e2 e3) =
  lem_fv_in_env_if g e1 e2 e3;
  introduce forall b (s:gsub g b) fsG h. (fsG `(≍) h` s /\ (spec_env_if fs_e1 preT preE) fsG) ==> t ⊆ (h, (if fs_e1 fsG then fs_e2 fsG else fs_e3 fsG), gsubst s (EIf e1 e2 e3)) with begin
    let preC = preC fsG in
    let preT = preT fsG in
    let preE = preE fsG in
    let fs_e1 () : Pure (fs_val qBool) (requires preC) (ensures (fun _ -> True)) = fs_e1 fsG in
    let pre = (preC /\ (fs_e1 () ==> preT) /\ (~(fs_e1 ()) ==> preE)) in
    let fs_e2 () : Pure (fs_val t) (requires preT) (ensures (fun _ -> True)) = fs_e2 fsG in
    let fs_e3 () : Pure (fs_val t) (requires preE) (ensures (fun _ -> True)) = fs_e3 fsG in
    let fs_e () : Pure (fs_val t) (requires pre) (ensures (fun _ -> True)) = if fs_e1 () then fs_e2 () else fs_e3 () in
    let e = EIf (gsubst s e1) (gsubst s e2) (gsubst s e3) in
    assert (gsubst s (EIf e1 e2 e3) == e);
    let EIf e1 e2 e3 = e in
    introduce (fsG `(≍) h` s /\ pre) ==> t ⊆ (h, fs_e (), e) with _. begin
      helper_compat_oval_if_steps h t (fs_e1 ()) (fs_e ()) e1 e2 e3
    end
  end

#push-options "--z3rlimit 10"
let helper_compat_oval_pair_steps (h:history) (t1 t2:qType) (fs_e1:fs_val t1) (fs_e2:fs_val t2) (e1 e2:closed_exp) :
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

let compat_oval_pair #g
  (#t1 #t2:qType) #preX #preY
  (fs_e1:fs_oval g t1 preX) (fs_e2:fs_oval g t2 preY)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊏ e1 /\ fs_e2 ⊏ e2)
    (ensures fs_oval_pair fs_e1 fs_e2 ⊏ EPair e1 e2) =
  lem_fv_in_env_pair g e1 e2;
  let t = t1 ^* t2 in
  introduce forall b (s:gsub g b) fsG h. (fsG `(≍) h` s /\ (spec_env_app preX preY) fsG) ==> t ⊆ (h, (fs_e1 fsG, fs_e2 fsG), gsubst s (EPair e1 e2)) with begin
    let preX = preX fsG in
    let preY = preY fsG in
    let pre = (preX /\ preY) in
    let fs_e1 () : Pure (fs_val t1) (requires preX) (ensures (fun _ -> True)) = fs_e1 fsG in
    let fs_e2 () : Pure (fs_val t2) (requires preY) (ensures (fun _ -> True)) = fs_e2 fsG in
    let fs_e () : Pure (fs_val (t1 ^* t2)) (requires pre) (ensures (fun _ -> True)) = (fs_e1 (), fs_e2()) in
    let e = EPair (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EPair e1 e2) == e);
    let EPair e1 e2 = e in
    introduce (fsG `(≍) h` s /\ pre) ==> t ⊆ (h, fs_e (), e) with _. begin
      helper_compat_oval_pair_steps h t1 t2 (fs_e1 ()) (fs_e2 ()) e1 e2
    end
  end

let helper_compat_oval_fst_steps (h:history) (t1 t2:qType) (fs_e12:fs_val (t1 ^* t2)) (e12:closed_exp) :
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

let helper_compat_oval_snd_steps (h:history) (t1 t2:qType) (fs_e12:fs_val (t1 ^* t2)) (e12:closed_exp) :
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

let compat_oval_pair_fst #g
  #pre12
  (#t1 #t2:qType)
  (fs_e12:fs_oval g (t1 ^* t2) pre12)
  (e12:exp)
  : Lemma
    (requires fs_e12 ⊏ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures fs_oval_fmap fs_e12 fst ⊏ (EFst e12)) =
  lem_fv_in_env_fst g e12;
  introduce forall b (s:gsub g b) fsG h. (fsG `(≍) h` s /\ pre12 fsG) ==>  t1 ⊆ (h, (fs_oval_fmap fs_e12 fst) fsG, gsubst s (EFst e12)) with begin
    let pre12 = pre12 fsG in
    let fs_e12 () : Pure (fs_val (t1 ^* t2)) (requires pre12) (ensures (fun _ -> True)) = fs_e12 fsG in
    let fs_e () : Pure (fs_val t1) (requires pre12) (ensures (fun _ -> True)) = fst (fs_e12 ()) in
    let e = EFst (gsubst s e12) in
    assert (gsubst s (EFst e12) == e);
    let EFst e12 = e in
    introduce (fsG `(≍) h` s /\ pre12) ==> t1 ⊆ (h, fs_e (), e) with _. begin
      helper_compat_oval_fst_steps h t1 t2 (fs_e12 ()) e12
    end
  end

let compat_oval_pair_snd #g #pre12 (#t1 #t2:qType) (fs_e12:fs_oval g (t1 ^* t2) pre12) (e12:exp)
  : Lemma
    (requires fs_e12 ⊏ e12)
    (ensures fs_oval_fmap fs_e12 snd ⊏ (ESnd e12)) =
  lem_fv_in_env_snd g e12;
  introduce forall b (s:gsub g b) fsG h. (fsG `(≍) h` s /\ pre12 fsG) ==> t2 ⊆ (h, (fs_oval_fmap fs_e12 snd) fsG, gsubst s (ESnd e12)) with begin
    let pre12 = pre12 fsG in
    let fs_e12 () : Pure (fs_val (t1 ^* t2)) (requires pre12) (ensures (fun _ -> True)) = fs_e12 fsG in
    let fs_e () : Pure (fs_val t2) (requires pre12) (ensures (fun _ -> True)) = snd (fs_e12 ()) in
    let e = ESnd (gsubst s e12) in
    assert (gsubst s (ESnd e12) == e);
    let ESnd e12 = e in
    introduce (fsG `(≍) h` s /\ pre12) ==> t2 ⊆ (h, fs_e (), e) with _. begin
      helper_compat_oval_snd_steps h t1 t2 (fs_e12 ()) e12
    end
  end

let helper_compat_oval_inl_steps (h:history) (t1 t2:qType) (fs_e:fs_val t1) (e:closed_exp) :
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

let helper_compat_oval_inr_steps (h:history) (t1 t2:qType) (fs_e:fs_val t2) (e:closed_exp) :
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

let compat_oval_inl #g #pre (#t1 t2:qType) (fs_e:fs_oval g t1 pre) (e:exp) : Lemma
  (requires fs_e ⊏ e)
  (ensures fs_oval_fmap #g #t1 #(t1 ^+ t2) fs_e Inl ⊏ (EInl e)) =
  lem_fv_in_env_inl g e;
  let t = t1 ^+ t2 in
  introduce forall b (s:gsub g b) fsG h. (fsG `(≍) h` s /\ pre fsG) ==> (t1 ^+ t2) ⊆ (h, Inl (fs_e fsG), gsubst s (EInl e)) with begin
    let pre = pre fsG in
    let fs_e () : Pure (fs_val t1) (requires pre) (ensures (fun _ -> True)) = fs_e fsG in
    let fs_ex () : Pure (fs_val (t1 ^+ t2)) (requires pre) (ensures (fun _ -> True)) = Inl #(get_Type t1) #(get_Type t2) (fs_e ()) in
    let ex = EInl (gsubst s e) in
    assert (gsubst s (EInl e) == ex);
    let EInl e = ex in
    introduce (fsG `(≍) h` s /\ pre) ==> t ⊆ (h, fs_ex (), ex) with _. begin
      helper_compat_oval_inl_steps h t1 t2 (fs_e ()) e
    end
  end

let compat_oval_inr #g #pre (t1 #t2:qType) (fs_e:fs_oval g t2 pre) (e:exp) : Lemma
  (requires fs_e ⊏ e)
  (ensures fs_oval_fmap #g #t2 #(t1 ^+ t2) fs_e Inr ⊏ (EInr e)) =
  lem_fv_in_env_inr g e;
  let t = t1 ^+ t2 in
  introduce forall b (s:gsub g b) fsG h. (fsG `(≍) h` s /\ pre fsG) ==> (t1 ^+ t2) ⊆ (h, Inr (fs_e fsG), gsubst s (EInr e)) with begin
    let pre = pre fsG in
    let fs_e () : Pure (fs_val t2) (requires pre) (ensures (fun _ -> True)) = fs_e fsG in
    let fs_ex () : Pure (fs_val (t1 ^+ t2)) (requires pre) (ensures (fun _ -> True)) = Inr #(get_Type t1) #(get_Type t2) (fs_e ()) in
    let ex = EInr (gsubst s e) in
    assert (gsubst s (EInr e) == ex);
    let EInr e = ex in
    introduce (fsG `(≍) h` s /\ pre) ==> t ⊆ (h, fs_ex (), ex) with _. begin
      helper_compat_oval_inr_steps h t1 t2 (fs_e ()) e
    end
  end

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let helper_compat_oval_case_steps (h:history) (t1 t2 t3:qType)
  (fs_case:fs_val (t1 ^+ t2))
  (fs_r:fs_val t3)
  (e_case:closed_exp)
  (e_lc:exp{is_closed (ELam e_lc)})
  (e_rc:exp{is_closed (ELam e_rc)}) :
  Lemma
    (requires (t1 ^+ t2) ⊆ (h, fs_case, e_case) /\
              (Inl? fs_case ==> (forall (v:value). t1 ∈ (h, Inl?.v fs_case, v) ==> t3 ⊆ (h, fs_r, subst_beta v e_lc))) /\
              (Inr? fs_case ==> (forall (v:value). t2 ∈ (h, Inr?.v fs_case, v) ==> t3 ⊆ (h, fs_r, subst_beta v e_rc))))
    (ensures t3 ⊆ (h, fs_r, ECase e_case e_lc e_rc)) =
  eliminate exists (ec':closed_exp). e_beh e_case ec' h [] /\ (t1 ^+ t2) ∈ (h, fs_case, ec')
    returns t3 ⊆ (h, fs_r, ECase e_case e_lc e_rc) with _. begin
  lem_values_are_values (t1 ^+ t2) h fs_case ec';
  match fs_case with
  | Inl x -> begin
    assert (Inl? fs_case);
    let EInl v = ec' in
    lem_values_are_values t1 h x v;
    eliminate forall (v':value). t1 ∈ (h, Inl?.v fs_case, v') ==> t3 ⊆ (h, fs_r, subst_beta v' e_lc) with v;
    eliminate exists (e':closed_exp). e_beh (subst_beta v e_lc) e' h [] /\ t3 ∈ (h, fs_r, e')
      returns t3 ⊆ (h, fs_r, ECase e_case e_lc e_rc) with _. begin
    FStar.Squash.bind_squash #(steps e_case (EInl v) h []) #(squash (t3 ⊆ (h, fs_r, ECase e_case e_lc e_rc))) () (fun (sts1:steps e_case (EInl v) h []) ->
    FStar.Squash.bind_squash #(steps (subst_beta v e_lc) e' h []) #(squash (t3 ⊆ (h, fs_r, ECase e_case e_lc e_rc))) () (fun (sts2:steps (subst_beta v e_lc) e' h []) ->
      construct_steps_ecase_inl e_case v e_lc e_rc e' h [] [] sts1 sts2))
    end
  end
  | Inr x -> begin
    assert (Inr? fs_case);
    let EInr v = ec' in
    lem_values_are_values t2 h x v;
    eliminate forall (v':value). t2 ∈ (h, Inr?.v fs_case, v') ==> t3 ⊆ (h, fs_r, subst_beta v' e_rc) with v;
    eliminate exists (e':closed_exp). e_beh (subst_beta v e_rc) e' h [] /\ t3 ∈ (h, fs_r, e')
      returns t3 ⊆ (h, fs_r, ECase e_case e_lc e_rc) with _. begin
    FStar.Squash.bind_squash #(steps e_case (EInr v) h []) #(squash (t3 ⊆ (h, fs_r, ECase e_case e_lc e_rc))) () (fun (sts1:steps e_case (EInr v) h []) ->
    FStar.Squash.bind_squash #(steps (subst_beta v e_rc) e' h []) #(squash (t3 ⊆ (h, fs_r, ECase e_case e_lc e_rc))) () (fun (sts2:steps (subst_beta v e_rc) e' h []) ->
      construct_steps_ecase_inr e_case v e_lc e_rc e' h [] [] sts1 sts2))
    end
  end
  end
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
    (requires fs_case ⊏ e_case /\ fs_lc ⊏ e_lc /\ fs_rc ⊏ e_rc)
    (ensures fs_oval_case fs_case fs_lc fs_rc ⊏ ECase e_case e_lc e_rc) =
  lem_fv_in_env_case g t1 t2 e_case e_lc e_rc;
  lem_fv_in_env_lam g t1 e_lc;
  lem_fv_in_env_lam g t2 e_rc;
  introduce forall b (s:gsub g b) fsG h.
    (fsG `(≍) h` s /\ (spec_env_case fs_case preLc preRc) fsG) ==> t3 ⊆ (h, fs_oval_case fs_case fs_lc fs_rc fsG, gsubst s (ECase e_case e_lc e_rc)) with begin
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
    introduce (fsG `(≍) h` s /\ (spec_env_case fs_case preLc preRc) fsG) ==> t3 ⊆ (h, fs_e (), e) with _. begin
      assert ((t1 ^+ t2) ⊆ (h, fs_case_v (), e_case_s));
      introduce Inl? (fs_case_v ()) ==> (forall (v:value). t1 ∈ (h, Inl?.v (fs_case_v ()), v) ==> t3 ⊆ (h, fs_e (), subst_beta v e_lc_s)) with _. begin
        let prove_inl_branch () : Lemma
          (requires Inl? (fs_case_v ()))
          (ensures forall (v:value). t1 ∈ (h, Inl?.v (fs_case_v ()), v) ==> t3 ⊆ (h, fs_e (), subst_beta v e_lc_s)) =
          introduce forall (v:value). t1 ∈ (h, Inl?.v (fs_case_v ()), v) ==> t3 ⊆ (h, fs_e (), subst_beta v e_lc_s) with begin
            introduce _ ==> _ with _. begin
            let s' = gsub_extend s t1 v in
            let fsG' = stack fsG (Inl?.v (fs_case_v ())) in
            assert ((fsG' `(≍) h` s' /\ preLc fsG') ==> t3 ⊆ (h, fs_lc fsG', gsubst s' e_lc));
            assert (fsG `(≍) h` s);
            assert (t1 ∈ (h, Inl?.v (fs_case_v ()), v));
            lem_values_are_values t1 h (Inl?.v (fs_case_v ())) v;
            assert (stack fsG (Inl?.v (fs_case_v ())) `(≍) h` gsub_extend s t1 v);
            assert (preLc fsG');
            assert (t3 ⊆ (h, fs_lc fsG', gsubst s' e_lc));
            lem_substitution s t1 v e_lc;
            assert (subst_beta v e_lc_s == gsubst s' e_lc);
            assert (t3 ⊆ (h, fs_lc fsG', subst_beta v e_lc_s));
            assert (fs_e () == fs_lc fsG');
            assert (t3 ⊆ (h, fs_e (), subst_beta v e_lc_s))
            end
          end in
        prove_inl_branch ()
      end;
      introduce Inr? (fs_case_v ()) ==> (forall (v:value). t2 ∈ (h, Inr?.v (fs_case_v ()), v) ==> t3 ⊆ (h, fs_e (), subst_beta v e_rc_s)) with _. begin
        let prove_inr_branch () : Lemma
          (requires Inr? (fs_case_v ()))
          (ensures forall (v:value). t2 ∈ (h, Inr?.v (fs_case_v ()), v) ==> t3 ⊆ (h, fs_e (), subst_beta v e_rc_s)) =
          introduce forall (v:value). t2 ∈ (h, Inr?.v (fs_case_v ()), v) ==> t3 ⊆ (h, fs_e (), subst_beta v e_rc_s) with begin
            introduce _ ==> _ with _. begin
            let s' = gsub_extend s t2 v in
            let fsG' = stack fsG (Inr?.v (fs_case_v ())) in
            assert ((fsG' `(≍) h` s' /\ preRc fsG') ==> t3 ⊆ (h, fs_rc fsG', gsubst s' e_rc));
            assert (fsG `(≍) h` s);
            assert (t2 ∈ (h, Inr?.v (fs_case_v ()), v));
            lem_values_are_values t2 h (Inr?.v (fs_case_v ())) v;
            assert (stack fsG (Inr?.v (fs_case_v ())) `(≍) h` gsub_extend s t2 v);
            assert (preRc fsG');
            assert (t3 ⊆ (h, fs_rc fsG', gsubst s' e_rc));
            lem_substitution s t2 v e_rc;
            assert (subst_beta v e_rc_s == gsubst s' e_rc);
            assert (t3 ⊆ (h, fs_rc fsG', subst_beta v e_rc_s));
            assert (fs_e () == fs_rc fsG');
            assert (t3 ⊆ (h, fs_e (), subst_beta v e_rc_s))
            end
          end in
        prove_inr_branch ()
      end;
      helper_compat_oval_case_steps h t1 t2 t3 (fs_case_v ()) (fs_e ()) e_case_s e_lc_s e_rc_s
    end
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let compat_oval_lambda_ocomp #g (#t1:qType) (#preBody:spec_env (extend t1 g)) (#t2:qType) (fs_body:fs_ocomp (extend t1 g) t2 preBody) (body:exp)
  : Lemma
    (requires fs_body ⊑ body)
    (ensures fs_oval_lambda_ocomp fs_body ⊏ (ELam body)) =
  lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  let f : fs_oval g (t1 ^->!@ t2) (spec_env_lambda_tot preBody) = fun fsG x -> fs_body (stack fsG x) in
  assert (f == fs_oval_lambda_ocomp fs_body)
    by (FStar.Tactics.norm [delta_only [`%fs_oval_lambda_ocomp]]; FStar.Tactics.trefl ());
  introduce forall b (s:gsub g b) fsG h. (fsG `(≍) h` s /\ (spec_env_lambda_tot preBody) fsG) ==> (t1 ^->!@ t2) ⊆ (h, f fsG, gsubst s (ELam body)) with begin 
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∈ (h++lt_v, fs_v, v) ==> t2 ⫃ (h++lt_v, f fsG fs_v, subst_beta v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fsG' = stack fsG fs_v in
          let h' = h++lt_v in
          let f1 () : Pure (fs_val (t1 ^->!@ t2)) (requires ((spec_env_lambda_tot preBody) fsG)) (ensures (fun _ -> True)) =
            f (tail #t1 fsG') in
          let f' : fs_comp t2 = f1 () (hd #t1 #g fsG') in
          assert ((fsG' `(≍) h'` s' /\ preBody fsG') ==> t2 ⫃ (h', f', gsubst s' body));
          assert ((spec_env_lambda_tot preBody) fsG);
          assert (preBody fsG');
          assert (fsG `(≍) h` s);
          assert (t1 ∈ (h++lt_v, fs_v, v));
          introduce forall (x:var). Some? (g x) ==> Some?.v (g x) ∈ (h++lt_v, index fsG x, s x) with begin
            introduce _ ==> _ with _. begin
              val_type_closed_under_history_extension (Some?.v (g x)) h (index fsG x) (s x)
            end
          end;
          assert (stack fsG fs_v `(≍) h'` gsub_extend s t1 v);
          assert (t2 ⫃ (h', f', gsubst s' body));
          assert (hd (stack fsG fs_v) == fs_v);
          assert (t2 ⫃ (h', f (tail fsG') fs_v, gsubst s' body));
          assert (t2 ⫃ (h', f fsG fs_v, gsubst s' body));
          lem_substitution s t1 v body;
          assert (t2 ⫃ (h', f fsG fs_v, subst_beta v body'))
        end
      end;
      assert (forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∈ (h++lt_v, fs_v, v) ==> t2 ⫃ (h++lt_v, f fsG fs_v, subst_beta v body'));
      assert ((t1 ^->!@ t2) ∈ (h, f fsG, ELam body'));
      assert ((t1 ^->!@ t2) ∈ (h, f fsG, gsubst s (ELam body)));
      lem_values_are_expressions (t1 ^->!@ t2) h (f fsG) (gsubst s (ELam body));
      assert ((t1 ^->!@ t2) ⊆ (h, f fsG, gsubst s (ELam body)))
    end
  end
#pop-options

let compat_ocomp_return #g (#t:qType) #pre (fs_x:fs_oval g t pre) (x:exp)
  : Lemma
    (requires fs_x ⊏ x)
    (ensures fs_ocomp_return_oval fs_x ⊑ x) =
  introduce forall b (s:gsub g b) fsG h. (fsG `(≍) h` s /\ pre fsG) ==> t ⫃ (h, return (fs_x fsG), gsubst s x) with begin
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

#push-options "--z3rlimit 10 --fuel 2 --ifuel 0"
let helper_compat_ocomp_bind_steps (h:history) (lt:local_trace h) (a b:qType)
  (fs_m:fs_comp a) (fs_k:fs_val a -> fs_comp b) (fs_r:fs_val b)
  (m:closed_exp) (k:exp{is_closed (ELam k)}) :
  Lemma
    (requires fs_beh (fs_comp_bind fs_m fs_k) h lt fs_r /\
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
  assert (exists (lam':closed_exp). e_beh (ELam k) lam' h [] /\ (a ^->!@ b) ∈ (h, fs_k, lam'));
  eliminate exists (lam':closed_exp). e_beh (ELam k) lam' h [] /\ (a ^->!@ b) ∈ (h, fs_k, lam')
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp (ELam k) m) e' h lt with _. begin
  steps_val_id (ELam k) lam' h;
  unfold_contains_io_arrow a b fs_k k h;
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

#push-options "--split_queries always"
let compat_ocomp_bind #g (#a #b:qType) (#preM:spec_env g) (#preK:spec_env (extend a g))
  (fs_m:fs_ocomp g a preM) (fs_k:fs_ocomp (extend a g) b preK) (m k:exp)
  : Lemma
    (requires fs_m ⊑ m /\ fs_k ⊑ k)
    (ensures (fs_ocomp_bind fs_m fs_k) ⊑ (EApp (ELam k) m)) =
  lem_fv_in_env_lam g a k;
  lem_fv_in_env_app g (ELam k) m;
  compat_oval_lambda_ocomp fs_k k;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(≍) h` s /\ spec_env_bind preM preK fsG) ==> b ⫃ (h, fs_ocomp_bind fs_m fs_k fsG, gsubst s (EApp (ELam k) m)) with begin
    let k' = subst (sub_elam s) k in
    assert (gsubst s (ELam k) == ELam k');
    let e = EApp (ELam k') (gsubst s m) in
    assert (gsubst s (EApp (ELam k) m) == e);
    let EApp (ELam k') m = e in
    introduce (fsG `(≍) h` s /\ spec_env_bind preM preK fsG) ==> b ⫃ (h, fs_ocomp_bind fs_m fs_k fsG, e) with _. begin
      assert (preM fsG);
      assert ((spec_env_lambda_tot preK) fsG);
      let fs_m' () : Pure (fs_comp a) (requires preM fsG) (ensures (fun _ -> True)) = fs_m fsG in
      let fs_k_oval : fs_oval g (a ^->!@ b) (spec_env_lambda_tot preK) = fun fsG x -> fs_k (stack fsG x) in
      assert (fs_k_oval == fs_oval_lambda_ocomp fs_k);
      let fs_k' () : Pure (fs_val (a ^->!@ b)) (requires (spec_env_lambda_tot preK) fsG) (ensures (fun _ -> True)) = fs_k_oval fsG in
      let fs_e = fs_comp_bind (fs_m' ()) (fun m' -> (fs_k' ()) m') in
      assert ((fs_ocomp_bind fs_m fs_k fsG) == fs_e);
      introduce forall lt (fs_r:fs_val b). fs_beh fs_e h lt fs_r ==> exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce fs_beh fs_e h lt fs_r ==> exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          lem_shift_type_value_environments h fsG s;
          assert ((a ^->!@ b) ⊆ (h, fs_oval_lambda_ocomp fs_k fsG, gsubst s (ELam k)));
          assert ((a ^->!@ b) ⊆ (h, fs_oval_lambda_ocomp fs_k fsG, ELam k'));
          assert ((a ^->!@ b) ⊆ (h, fs_k_oval fsG, ELam k'));
          assert ((a ^->!@ b) ⊆ (h, fs_k' (), ELam k'));
          assert (a ⫃ (h, fs_m' (), m));
          assert (fs_comp_bind (fs_m' ()) (fs_k' ()) == fs_comp_bind (fs_m' ()) (fun m' -> (fs_k' ()) m'))
            by (FStar.Tactics.trefl ());
          assert (fs_beh (fs_comp_bind (fs_m' ()) (fs_k' ())) h lt fs_r);
          helper_compat_ocomp_bind_steps h lt a b (fs_m' ()) (fs_k' ()) fs_r m k'
        end
      end
    end
  end
#pop-options

let helper_compat_ocomp_app_oval_oval_steps (h:history) (lt:local_trace h) (a b:qType) (fs_f:fs_val (a ^->!@ b)) (fs_x:fs_val a) (f x:closed_exp) (fs_r:fs_val b) :
  Lemma
    (requires (fs_beh (fs_f fs_x) h lt fs_r) /\
              (a ^->!@ b) ⊆ (h, fs_f, f) /\
              (forall (lt:local_trace h). a ⊆ (h++lt, fs_x, x)))
    (ensures exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt) =
  eliminate exists (f':closed_exp). e_beh f f' h [] /\ (a ^->!@ b) ∈ (h, fs_f, f')
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
  let ELam f1 = f' in
  unfold_contains_io_arrow a b fs_f f1 h;
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

let compat_ocomp_app_oval_oval #g (#a #b:qType) #preF (fs_f:fs_oval g (a ^->!@ b) preF) #preX (fs_x:fs_oval g a preX) (f x:exp)
  : Lemma
    (requires fs_f ⊏ f /\ fs_x ⊏ x)
    (ensures (fs_ocomp_app_oval_oval fs_f fs_x) ⊑ (EApp f x)) =
  lem_fv_in_env_app g f x;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(≍) h` s /\ (spec_env_app preF preX) fsG) ==> b ⫃ (h, (fs_f fsG) (fs_x fsG), gsubst s (EApp f x)) with begin
    let preF = preF fsG in
    let preX = preX fsG in
    let pre = (preF /\ preX) in
    let fs_f () : Pure (fs_val (a ^->!@ b)) (requires preF) (ensures (fun _ -> True)) = fs_f fsG in
    let fs_x () : Pure (fs_val a) (requires preX) (ensures (fun _ -> True)) = fs_x fsG in
    let fs_e () : Pure (fs_comp b) (requires pre) (ensures (fun _ -> True)) = (fs_f ()) (fs_x ()) in
    let e = EApp (gsubst s f) (gsubst s x) in
    assert (gsubst s (EApp f x) == e);
    let EApp f x = e in
    introduce (fsG `(≍) h` s /\ pre) ==> b ⫃ (h, fs_e (), e) with _. begin
      introduce forall (lt:local_trace h) (fs_r:get_Type b). fs_beh (fs_e ()) h lt fs_r ==> exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce _ ==> _ with _. begin
          lem_shift_type_value_environments h fsG s;
          helper_compat_ocomp_app_oval_oval_steps h lt a b (fs_f ()) (fs_x ()) f x fs_r
        end
      end
    end
  end

let helper_compat_ocomp_if_val (#h:history) (lt:local_trace h) (a:qType) (fs_c:fs_val qBool) (fs_e:fs_comp a) (fs_r:fs_val a) (c t e:closed_exp) :
  Lemma
    (requires (fs_beh fs_e h lt fs_r) /\
              (qBool ⊆ (h, fs_c, c)) /\
              (if fs_c then a ⫃ (h, fs_e, t) else a ⫃ (h, fs_e, e)))
    (ensures (exists ex'. a ∈ (h++lt, fs_r, ex') /\ e_beh (EIf c t e) ex' h lt)) =
  eliminate exists (c':closed_exp). e_beh c c' h [] /\ qBool ∈ (h, fs_c, c')
    returns exists ex'. a ∈ (h++lt, fs_r, ex') /\ e_beh (EIf c t e) ex' h lt with _. begin
  eliminate forall (lt:local_trace h) (fs_r:fs_val a). fs_beh fs_e h lt fs_r ==> exists ex'. a ∈ (h++lt, fs_r, ex') /\ e_beh (if fs_c then t else e) ex' h lt with lt fs_r;
  eliminate exists ex'. a ∈ (h++lt, fs_r, ex') /\ e_beh (if fs_c then t else e) ex' h lt
    returns exists ex'. a ∈ (h++lt, fs_r, ex') /\ e_beh (EIf c t e) ex' h lt with _. begin
  FStar.Squash.bind_squash #(steps c c' h []) () (fun sts1 ->
  FStar.Squash.bind_squash #(steps (if fs_c then t else e) ex' h lt) () (fun sts2 ->
  construct_steps_eif c c' t e ex' h [] lt sts1 sts2))
  end
  end

let compat_ocomp_if_oval #g (#a:qType) #preC #preT #preE
  (fs_c:fs_oval g qBool preC) (fs_t:fs_ocomp g a preT) (fs_e:fs_ocomp g a preE) (c t e:exp)
  : Lemma
    (requires fs_c ⊏ c /\ fs_t ⊑ t /\ fs_e ⊑ e)
    (ensures (fs_ocomp_if_oval fs_c fs_t fs_e) ⊑ (EIf c t e)) =
  lem_fv_in_env_if g c t e;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(≍) h` s /\ (spec_env_if fs_c preT preE) fsG) ==> a ⫃ (h, (if (fs_c fsG) then (fs_t fsG) else (fs_e fsG)), gsubst s (EIf c t e)) with begin
    let ex = EIf (gsubst s c) (gsubst s t) (gsubst s e) in
    assert (gsubst s (EIf c t e) == ex);
    let EIf c t e = ex in
    introduce (fsG `(≍) h` s /\ (spec_env_if fs_c preT preE) fsG) ==> a ⫃ (h, (if fs_c fsG then fs_t fsG else fs_e fsG), ex) with _. begin
      let fs_c = fs_c fsG in
      let fs_ex = if fs_c then fs_t fsG else fs_e fsG in
      introduce forall (lt:local_trace h) (fs_r:fs_val a). fs_beh fs_ex h lt fs_r ==> exists ex'. a ∈ (h++lt, fs_r, ex') /\ e_beh ex ex' h lt with begin
        introduce fs_beh fs_ex h lt fs_r ==> exists ex'. a ∈ (h++lt, fs_r, ex') /\ e_beh ex ex' h lt with _. begin
          assert (qBool ⊆ (h, fs_c, c));
          assert (if fs_c then a ⫃ (h, fs_ex, t) else a ⫃ (h, fs_ex, e));
          helper_compat_ocomp_if_val lt a fs_c fs_ex fs_r c t e
        end
      end
    end
  end

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let helper_compat_ocomp_case_oval_steps (h:history) (lt:local_trace h) (a b c:qType)
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
              fs_beh (fs_comp_case_val fs_cond fs_inlc fs_inrc) h lt fs_r)
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
    unfold_contains_io_arrow a c fs_inlc e_lc h;
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
    unfold_contains_io_arrow b c fs_inrc e_rc h;
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

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let helper_compat_ocomp_case_oval_steps_inl (h:history) (lt:local_trace h) (a b c:qType)
  (fs_x:fs_val a)
  (fs_inlc_x:fs_comp c)
  (fs_r:fs_val c)
  (e_cond:closed_exp)
  (e_lc:exp{is_closed (ELam e_lc)})
  (e_rc:exp{is_closed (ELam e_rc)}) :
  Lemma
    (requires (a ^+ b) ⊆ (h, Inl fs_x, e_cond) /\
              (forall (v':value). a ∈ (h, fs_x, v') ==> c ⫃ (h, fs_inlc_x, subst_beta v' e_lc)) /\
              fs_beh fs_inlc_x h lt fs_r)
    (ensures exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt) =
  eliminate exists (ec':closed_exp). e_beh e_cond ec' h [] /\ (a ^+ b) ∈ (h, Inl fs_x, ec')
    returns exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt with _. begin
  lem_values_are_values (a ^+ b) h (Inl fs_x) ec';
  let EInl v = ec' in
  lem_values_are_values a h fs_x v;
  eliminate forall (lt':local_trace h) (fs_r':get_Type c). fs_beh fs_inlc_x h lt' fs_r' ==>
    exists e'. c ∈ (h++lt', fs_r', e') /\ e_beh (subst_beta v e_lc) e' h lt' with lt fs_r;
  eliminate exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (subst_beta v e_lc) e' h lt
    returns exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt with _. begin
  FStar.Squash.bind_squash #(steps e_cond (EInl v) h []) #(squash (exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt)) () (fun (sts1:steps e_cond (EInl v) h []) ->
  FStar.Squash.bind_squash #(steps (subst_beta v e_lc) e' h lt) #(squash (exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt)) () (fun (sts2:steps (subst_beta v e_lc) e' h lt) ->
    construct_steps_ecase_inl e_cond v e_lc e_rc e' h [] lt sts1 sts2))
  end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let helper_compat_ocomp_case_oval_steps_inr (h:history) (lt:local_trace h) (a b c:qType)
  (fs_x:fs_val b)
  (fs_inrc_x:fs_comp c)
  (fs_r:fs_val c)
  (e_cond:closed_exp)
  (e_lc:exp{is_closed (ELam e_lc)})
  (e_rc:exp{is_closed (ELam e_rc)}) :
  Lemma
    (requires (a ^+ b) ⊆ (h, Inr fs_x, e_cond) /\
              (forall (v':value). b ∈ (h, fs_x, v') ==> c ⫃ (h, fs_inrc_x, subst_beta v' e_rc)) /\
              fs_beh fs_inrc_x h lt fs_r)
    (ensures exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt) =
  eliminate exists (ec':closed_exp). e_beh e_cond ec' h [] /\ (a ^+ b) ∈ (h, Inr fs_x, ec')
    returns exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt with _. begin
  lem_values_are_values (a ^+ b) h (Inr fs_x) ec';
  let EInr v = ec' in
  lem_values_are_values b h fs_x v;
  eliminate forall (lt':local_trace h) (fs_r':get_Type c). fs_beh fs_inrc_x h lt' fs_r' ==>
    exists e'. c ∈ (h++lt', fs_r', e') /\ e_beh (subst_beta v e_rc) e' h lt' with lt fs_r;
  eliminate exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (subst_beta v e_rc) e' h lt
    returns exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt with _. begin
  FStar.Squash.bind_squash #(steps e_cond (EInr v) h []) #(squash (exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt)) () (fun (sts1:steps e_cond (EInr v) h []) ->
  FStar.Squash.bind_squash #(steps (subst_beta v e_rc) e' h lt) #(squash (exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_cond e_lc e_rc) e' h lt)) () (fun (sts2:steps (subst_beta v e_rc) e' h lt) ->
    construct_steps_ecase_inr e_cond v e_lc e_rc e' h [] lt sts1 sts2))
  end
  end
#pop-options

#push-options "--split_queries always"
let compat_ocomp_case_oval #g (#a #b #c:qType) #preCond (fs_cond:fs_oval g (a ^+ b) preCond) (#preInlc:spec_env (extend a g)) (fs_inlc:fs_ocomp (extend a g) c preInlc) (#preInrc:spec_env (extend b g)) (fs_inrc:fs_ocomp (extend b g) c preInrc) (cond inlc inrc:exp)
  : Lemma
    (requires fs_cond ⊏ cond /\ fs_inlc ⊑ inlc /\ fs_inrc ⊑ inrc)
    (ensures (fs_ocomp_case_oval fs_cond fs_inlc fs_inrc) ⊑ (ECase cond inlc inrc)) =
  lem_fv_in_env_case g a b cond inlc inrc;
  lem_fv_in_env_lam g a inlc;
  lem_fv_in_env_lam g b inrc;
  introduce forall b' (s:gsub g b') fsG h.
    (fsG `(≍) h` s /\ (spec_env_case fs_cond preInlc preInrc) fsG) ==> c ⫃ (h, fs_ocomp_case_oval fs_cond fs_inlc fs_inrc fsG, gsubst s (ECase cond inlc inrc)) with begin
    let preCondH = preCond fsG in
    let fs_cond_v () : Pure (fs_val (a ^+ b)) (requires preCondH) (ensures (fun _ -> True)) = fs_cond fsG in
    let e = ECase (gsubst s cond) (subst (sub_elam s) inlc) (subst (sub_elam s) inrc) in
    assert (gsubst s (ECase cond inlc inrc) == e);
    let ECase cond_s inlc_s inrc_s = e in
    introduce (fsG `(≍) h` s /\ (spec_env_case fs_cond preInlc preInrc) fsG) ==> c ⫃ (h, fs_ocomp_case_oval fs_cond fs_inlc fs_inrc fsG, e) with _. begin
      assert (preCondH);
      let fs_cond_val = fs_cond_v () in
      assert ((a ^+ b) ⊆ (h, fs_cond_val, cond_s));
      match fs_cond_val with
      | Inl x -> begin
        assert (preInlc (stack fsG x));
        let fsG' = stack fsG x in
        let fs_inlc_x : fs_comp c = fs_inlc fsG' in
        assert (fs_inlc_x == fs_ocomp_case_oval fs_cond fs_inlc fs_inrc fsG);
        // Prove: forall v'. a ∈ (h, x, v') ==> c ⫃ (h, fs_inlc_x, subst_beta v' inlc_s)
        introduce forall (v':value). a ∈ (h, x, v') ==> c ⫃ (h, fs_inlc_x, subst_beta v' inlc_s) with begin
          introduce _ ==> _ with _. begin
            let s'' = gsub_extend s a v' in
            let fsG'' = stack fsG x in
            assert ((fsG'' `(≍) h` s'' /\ preInlc fsG'') ==> c ⫃ (h, fs_inlc fsG'', gsubst s'' inlc));
            lem_values_are_values a h x v';
            assert (stack fsG x `(≍) h` gsub_extend s a v');
            assert (preInlc fsG'');
            assert (c ⫃ (h, fs_inlc fsG'', gsubst s'' inlc));
            lem_substitution s a v' inlc;
            assert (subst_beta v' inlc_s == gsubst s'' inlc);
            assert (c ⫃ (h, fs_inlc_x, subst_beta v' inlc_s))
          end
        end;
        introduce forall (lt:local_trace h) (fs_r:fs_val c). fs_beh fs_inlc_x h lt fs_r ==> exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_inlc_x h lt fs_r ==> exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            helper_compat_ocomp_case_oval_steps_inl h lt a b c x fs_inlc_x fs_r cond_s inlc_s inrc_s
          end
        end
      end
      | Inr x -> begin
        assert (preInrc (stack fsG x));
        let fsG' = stack fsG x in
        let fs_inrc_x : fs_comp c = fs_inrc fsG' in
        assert (fs_inrc_x == fs_ocomp_case_oval fs_cond fs_inlc fs_inrc fsG);
        introduce forall (v':value). b ∈ (h, x, v') ==> c ⫃ (h, fs_inrc_x, subst_beta v' inrc_s) with begin
          introduce _ ==> _ with _. begin
            let s'' = gsub_extend s b v' in
            let fsG'' = stack fsG x in
            assert ((fsG'' `(≍) h` s'' /\ preInrc fsG'') ==> c ⫃ (h, fs_inrc fsG'', gsubst s'' inrc));
            lem_values_are_values b h x v';
            assert (stack fsG x `(≍) h` gsub_extend s b v');
            assert (preInrc fsG'');
            assert (c ⫃ (h, fs_inrc fsG'', gsubst s'' inrc));
            lem_substitution s b v' inrc;
            assert (subst_beta v' inrc_s == gsubst s'' inrc);
            assert (c ⫃ (h, fs_inrc_x, subst_beta v' inrc_s))
          end
        end;
        introduce forall (lt:local_trace h) (fs_r:fs_val c). fs_beh fs_inrc_x h lt fs_r ==> exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_inrc_x h lt fs_r ==> exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            helper_compat_ocomp_case_oval_steps_inr h lt a b c x fs_inrc_x fs_r cond_s inlc_s inrc_s
          end
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
    (requires (q_io_args op) ∈ (h, fs_arg, val_arg))
    (ensures exists (args:io_args op). val_arg == as_e_io_args op args) =
  match op with
  | OWrite -> begin
    let EPair (EFileDescr arg1) (EString arg2) = val_arg in
    assert (as_e_io_args OWrite (arg1, arg2) == val_arg)
    end
  | _ -> ()

#push-options "--fuel 4 --z3rlimit 20 --ifuel 1 --split_queries always"
let helper_compat_ocomp_call_oval_steps (op:io_ops) (h:history) (lt:local_trace h)
  (fs_arg:fs_val (q_io_args op){fs_val (q_io_args op) == io_args op}) (arg:closed_exp) (fs_e:fs_comp (q_io_res op){(fs_val (q_io_res op) == io_res op fs_arg) /\ (fs_e == io_call op fs_arg)}) (fs_r:fs_val (q_io_res op)) :
  Lemma
    (requires fs_beh fs_e h lt fs_r /\
              (q_io_args op) ⊆ (h, fs_arg, arg))
    (ensures exists e'. (q_io_res op) ∈ (h++lt, fs_r, e') /\ e_beh (ECall op arg) e' h lt) =
  eliminate exists (arg':closed_exp). e_beh arg arg' h [] /\ (q_io_args op) ∈ (h, fs_arg, arg')
    returns exists e'. (q_io_res op) ∈ (h++lt, fs_r, e') /\ e_beh (ECall op arg) e' h lt with _. begin
  lem_values_are_values (q_io_args op) h fs_arg arg';
  assert (fs_val (q_io_args OOpen) == string)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res OOpen) == resexn file_descr)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_args ORead) == file_descr)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res ORead) == resexn string)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_args OWrite) == (file_descr * string))
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res OWrite) == resexn unit)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_args OClose) == file_descr)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res OClose) == resexn unit)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  destruct_thetaP_call op fs_arg h lt fs_r;
  FStar.Squash.bind_squash #(steps arg arg' h []) () (fun sts_arg ->
  construct_steps_ecall op arg arg' h [] sts_arg;
  let st_call : step (ECall op (as_e_io_args op fs_arg)) (as_e_io_res op fs_arg fs_r) h (Some (op_to_ev op fs_arg fs_r)) = SCallReturn h op fs_arg fs_r in
  lem_step_implies_steps (ECall op (as_e_io_args op fs_arg)) (as_e_io_res op fs_arg fs_r) h (Some (op_to_ev op fs_arg fs_r));
  lem_steps_transitive (ECall op arg) (ECall op (as_e_io_args op fs_arg)) (as_e_io_res op fs_arg fs_r) h [] [op_to_ev op fs_arg fs_r];
  lem_value_is_irred (as_e_io_res op fs_arg fs_r))
  end
#pop-options

(** Helper to establish fs_e == fs_ocomp_call_oval via tactic, provided as a pure lemma *)
let lem_fs_ocomp_call_oval_eq #g (op:io_ops) #preArgs (fs_arg:fs_oval g (q_io_args op) preArgs) (fsG:eval_env g) :
  Lemma
    (requires preArgs fsG)
    (ensures fs_ocomp_call_oval op fs_arg fsG == fs_comp_call_val op (fs_arg fsG)) =
  assert (fs_ocomp_call_oval op fs_arg fsG == fs_comp_call_val op (fs_arg fsG)) by (
    norm [delta_only [`%fs_ocomp_call_oval;`%fs_ocomp_call;`%fs_ocomp_bind';`%fs_ocomp_bind;
                      `%fs_ocomp_return;`%fs_ocomp_return_oval;
                      `%fs_comp_bind;`%io_bind;`%io_return];
          iota;zeta];
    simplify_stack_ops ();
    trefl ())

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2 --split_queries always"
let compat_ocomp_call_oval #g (op:io_ops) #preArgs (fs_arg:fs_oval g (q_io_args op) preArgs) (arg:exp)
  : Lemma
    (requires fs_arg ⊏ arg)
    (ensures fs_ocomp_call_oval op fs_arg ⊑ ECall op arg)
  =
  lem_fv_in_env_call g op arg;
  assert (fs_val (q_io_args OOpen) == string)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res OOpen) == resexn file_descr)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_args ORead) == file_descr)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res ORead) == resexn string)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_args OWrite) == (file_descr * string))
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res OWrite) == resexn unit)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_args OClose) == file_descr)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res OClose) == resexn unit)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  let pre : spec_env g = spec_env_bind' #g #(q_io_args op) preArgs (fun a -> spec_env_return_comp #g #(q_io_res op) (fs_comp_call_val op a)) in
  let fs_e : fs_ocomp g (q_io_res op) pre = fs_ocomp_call_oval op fs_arg in
  introduce forall b (s:gsub g b) (fsG:eval_env g) (h:history). (fsG `(≍) h` s /\ pre fsG) ==> (q_io_res op) ⫃ (h, fs_e fsG, gsubst s (ECall op arg)) with begin
    let e = ECall op (gsubst s arg) in
    assert (gsubst s (ECall op arg) == e);
    let ECall op arg = e in
    introduce (fsG `(≍) h` s /\ pre fsG) ==> (q_io_res op) ⫃ (h, fs_e fsG, gsubst s (ECall op arg)) with _. begin
      assert (preArgs fsG);
      let fs_arg_v : fs_val (q_io_args op) = fs_arg fsG in
      let fs_e_call : fs_comp (q_io_res op) = fs_comp_call_val op fs_arg_v in
      lem_fs_ocomp_call_oval_eq #g op #preArgs fs_arg fsG;
      assert (fs_e fsG == fs_e_call);
      lem_shift_type_value_environments h fsG s;
      introduce forall lt (fs_r:fs_val (q_io_res op)). fs_beh fs_e_call h lt fs_r ==> exists e'. (q_io_res op) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce fs_beh fs_e_call h lt fs_r ==> exists e'. (q_io_res op) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          helper_compat_ocomp_call_oval_steps op h lt fs_arg_v arg fs_e_call fs_r
        end
      end
    end
  end;
  assert (fs_ocomp_call_oval op fs_arg ⊑ ECall op arg) by (
    FStar.Tactics.V1.norm [delta_only [`%(⊑); `%subset_ocomp]];
    FStar.Tactics.V1.smt ())
#pop-options

let compat_ocomp_unit g : Lemma (fs_ocomp_return_val g qUnit () ⊑ EUnit) =
  compat_oval_unit g;
  compat_ocomp_return (fs_oval_return g #qUnit ()) EUnit

let compat_ocomp_true g : Lemma (fs_ocomp_return_val g qBool true ⊑ ETrue) =
  compat_oval_true g;
  compat_ocomp_return (fs_oval_return g #qBool true) ETrue

let compat_ocomp_false g : Lemma (fs_ocomp_return_val g qBool false ⊑ EFalse) =
  compat_oval_false g;
  compat_ocomp_return (fs_oval_return g #qBool false) EFalse

let compat_ocomp_string g s : Lemma (fs_ocomp_return_val g qString s ⊑ EString s) =
  compat_oval_string g s;
  compat_ocomp_return (fs_oval_return g #qString s) (EString s)

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let helper_ocomp_if_from_bool_value (h:history) (lt:local_trace h) (t:qType)
  (lt1:local_trace h) (lt2:local_trace (h++lt1))
  (fs_b:fs_val qBool) (e1':closed_exp) (fs_e2 fs_e3:fs_comp t) (fs_r:fs_val t)
  (e1 e2 e3:closed_exp) :
  Lemma
    (requires
      lt == lt1@lt2 /\
      qBool ∈ (h++lt1, fs_b, e1') /\ e_beh e1 e1' h lt1 /\
      is_value e1' /\ indexed_irred e1' (h++lt1) /\
      fs_beh (fs_comp_if_val fs_b fs_e2 fs_e3) (h++lt1) lt2 fs_r /\
      (forall (lt':local_trace h). t ⫃ (h++lt', fs_e2, e2)) /\
      (forall (lt':local_trace h). t ⫃ (h++lt', fs_e3, e3)))
    (ensures exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh (EIf e1 e2 e3) e' h lt) =
  trans_history h lt1 lt2;
  if fs_b then begin
    assert (e1' == ETrue);
    assert (fs_beh fs_e2 (h++lt1) lt2 fs_r);
    assert (t ⫃ (h++lt1, fs_e2, e2));
    eliminate forall (lt'':local_trace (h++lt1)) (fs_r':get_Type t).
      fs_beh fs_e2 (h++lt1) lt'' fs_r' ==> exists e'. t ∈ ((h++lt1)++lt'', fs_r', e') /\ e_beh e2 e' (h++lt1) lt'' with lt2 fs_r;
    eliminate exists e'. t ∈ ((h++lt1)++lt2, fs_r, e') /\ e_beh e2 e' (h++lt1) lt2
      returns exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh (EIf e1 e2 e3) e' h lt with _. begin
    let goal : Type0 = (exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh (EIf e1 e2 e3) e' h lt) in
    FStar.Squash.bind_squash #(steps e1 e1' h lt1) #goal () (fun sts_e1 ->
    FStar.Squash.bind_squash #(steps e2 e' (h++lt1) lt2) #goal () (fun sts_branch ->
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
    let goal : Type0 = (exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh (EIf e1 e2 e3) e' h lt) in
    FStar.Squash.bind_squash #(steps e1 e1' h lt1) #goal () (fun sts_e1 ->
    FStar.Squash.bind_squash #(steps e3 e' (h++lt1) lt2) #goal () (fun sts_branch ->
    construct_steps_eif e1 EFalse e2 e3 e' h lt1 lt2 sts_e1 sts_branch))
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let helper_compat_ocomp_if_steps (h:history) (lt:local_trace h) (t:qType)
  (fs_e1:fs_comp qBool) (fs_e2 fs_e3:fs_comp t) (fs_r:fs_val t)
  (e1 e2 e3:closed_exp) :
  Lemma
    (requires fs_beh (fs_comp_bind fs_e1 (fun x -> if x then fs_e2 else fs_e3)) h lt fs_r /\
              qBool ⫃ (h, fs_e1, e1) /\
              (forall (lt':local_trace h). t ⫃ (h++lt', fs_e2, e2)) /\
              (forall (lt':local_trace h). t ⫃ (h++lt', fs_e3, e3)))
    (ensures exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh (EIf e1 e2 e3) e' h lt) =
  let fs_k : fs_val qBool -> fs_comp t = fun x -> fs_comp_if_val x fs_e2 fs_e3 in
  assert (fs_comp_bind fs_e1 fs_k == io_bind fs_e1 fs_k) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
  destruct_fs_beh fs_e1 fs_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_b:fs_val qBool).
    lt == (lt1@lt2) /\ fs_beh fs_e1 h lt1 fs_b /\ fs_beh (fs_k fs_b) (h++lt1) lt2 fs_r
    returns exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh (EIf e1 e2 e3) e' h lt with _. begin
  eliminate forall (lt':local_trace h) (fs_r':get_Type qBool). fs_beh fs_e1 h lt' fs_r' ==> exists e1'. qBool ∈ (h++lt', fs_r', e1') /\ e_beh e1 e1' h lt' with lt1 fs_b;
  eliminate exists e1'. qBool ∈ (h++lt1, fs_b, e1') /\ e_beh e1 e1' h lt1
    returns exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh (EIf e1 e2 e3) e' h lt with _. begin
  lem_values_are_values qBool (h++lt1) fs_b e1';
  lem_value_is_irred e1';
  assert (fs_k fs_b == (if fs_b then fs_e2 else fs_e3)) by (norm []; trefl ());
  helper_ocomp_if_from_bool_value h lt t lt1 lt2 fs_b e1' fs_e2 fs_e3 fs_r e1 e2 e3
  end
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2 --split_queries always"
let compat_ocomp_if #g
  (#t:qType) #preC #preT #preE
  (fs_e1:fs_ocomp g qBool preC) (fs_e2:fs_ocomp g t preT) (fs_e3:fs_ocomp g t preE)
  (e1:exp) (e2:exp) (e3:exp)
  : Lemma
    (requires fs_e1 ⊑ e1 /\ fs_e2 ⊑ e2 /\ fs_e3 ⊑ e3)
    (ensures fs_ocomp_if fs_e1 fs_e2 fs_e3 ⊑ EIf e1 e2 e3) =
  lem_fv_in_env_if g e1 e2 e3;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(≍) h` s /\ (spec_env_bind' #g #qBool preC (fun c' -> if c' then preT else preE)) fsG) ==> t ⫃ (h, fs_ocomp_if fs_e1 fs_e2 fs_e3 fsG, gsubst s (EIf e1 e2 e3)) with begin
    let e = EIf (gsubst s e1) (gsubst s e2) (gsubst s e3) in
    assert (gsubst s (EIf e1 e2 e3) == e);
    let EIf e1 e2 e3 = e in
    introduce (fsG `(≍) h` s /\ (spec_env_bind' #g #qBool preC (fun c' -> if c' then preT else preE)) fsG) ==> t ⫃ (h, fs_ocomp_if fs_e1 fs_e2 fs_e3 fsG, e) with _. begin
      assert (preC fsG);
      assert (forall (x:fs_val qBool). (if x then preT else preE) fsG);
      eliminate forall (x:fs_val qBool). (if x then preT else preE) fsG with true;
      eliminate forall (x:fs_val qBool). (if x then preT else preE) fsG with false;
      assert (preT fsG);
      assert (preE fsG);
      let fs_e1' () : Pure (fs_comp qBool) (requires preC fsG) (ensures (fun _ -> True)) = fs_e1 fsG in
      let fs_e2' () : Pure (fs_comp t) (requires preT fsG) (ensures (fun _ -> True)) = fs_e2 fsG in
      let fs_e3' () : Pure (fs_comp t) (requires preE fsG) (ensures (fun _ -> True)) = fs_e3 fsG in
      let fs_e = fs_comp_bind (fs_e1' ()) (fun x -> if x then fs_e2' () else fs_e3' ()) in
      assert (fs_e == fs_ocomp_if fs_e1 fs_e2 fs_e3 fsG) by (
        norm [delta_only [`%fs_ocomp_if;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_if_val]];
        simplify_stack_ops ();
        trefl ());
      lem_shift_type_value_environments h fsG s;
      introduce forall lt (fs_r:fs_val t). fs_beh fs_e h lt fs_r ==> exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce fs_beh fs_e h lt fs_r ==> exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          assert (fs_beh (fs_comp_bind (fs_e1' ()) (fun x -> if x then (fs_e2' ()) else (fs_e3' ()))) h lt fs_r);
          assert (qBool ⫃ (h, fs_e1' (), e1));
          helper_compat_ocomp_if_steps h lt t (fs_e1' ()) (fs_e2' ()) (fs_e3' ()) fs_r e1 e2 e3
        end
      end
    end
  end
#pop-options

let compat_ocomp_file_descr g fd : Lemma (fs_ocomp_return_val g qFileDescr fd ⊑ EFileDescr fd) =
  compat_oval_file_descr g fd;
  compat_ocomp_return (fs_oval_return g #qFileDescr fd) (EFileDescr fd)

let compat_ocomp_var g (x:var{Some? (g x)}) : Lemma (fs_ocomp_var g x ⊑ EVar x) =
  compat_oval_var g x;
  compat_ocomp_return (fs_oval_var g x) (EVar x)

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let helper_ocomp_app_from_arg_value (h:history) (lt:local_trace h) (a b:qType)
  (lt1:local_trace h) (lt2a:local_trace (h++lt1)) (lt2b:local_trace ((h++lt1)++lt2a))
  (fs_r_f:fs_val (a ^->!@ b)) (fs_r_x:fs_val a) (fs_r:fs_val b)
  (f':closed_exp) (x':closed_exp) (f x:closed_exp) :
  Lemma
    (requires
      lt == lt1@(lt2a@lt2b) /\
      (a ^->!@ b) ∈ (h++lt1, fs_r_f, f') /\
      a ∈ ((h++lt1)++lt2a, fs_r_x, x') /\
      e_beh f f' h lt1 /\ e_beh x x' (h++lt1) lt2a /\
      is_value f' /\ indexed_irred f' (h++lt1) /\
      is_value x' /\ indexed_irred x' ((h++lt1)++lt2a) /\
      fs_beh (fs_r_f fs_r_x) ((h++lt1)++lt2a) lt2b fs_r)
    (ensures exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt) =
  let ELam f1 = f' in
  unfold_contains_io_arrow a b fs_r_f f1 (h++lt1);
  eliminate forall (v:value) (fs_v:fs_val a) (lt_v:local_trace (h++lt1)).
    a ∈ ((h++lt1)++lt_v, fs_v, v) ==> b ⫃ ((h++lt1)++lt_v, fs_r_f fs_v, subst_beta v f1) with x' fs_r_x lt2a;
  eliminate forall (lt':local_trace ((h++lt1)++lt2a)) (fs_r':get_Type b).
    fs_beh (fs_r_f fs_r_x) ((h++lt1)++lt2a) lt' fs_r' ==> exists e'. b ∈ (((h++lt1)++lt2a)++lt', fs_r', e') /\ e_beh (subst_beta x' f1) e' ((h++lt1)++lt2a) lt' with lt2b fs_r;
  eliminate exists e'. b ∈ (((h++lt1)++lt2a)++lt2b, fs_r, e') /\ e_beh (subst_beta x' f1) e' ((h++lt1)++lt2a) lt2b
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
  let goal : Type0 = (exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt) in
  FStar.Squash.bind_squash #(steps f (ELam f1) h lt1) #goal () (fun sts_f ->
  FStar.Squash.bind_squash #(steps x x' (h++lt1) lt2a) #goal () (fun sts_x ->
  FStar.Squash.bind_squash #(steps (subst_beta x' f1) e' ((h++lt1)++lt2a) lt2b) #goal () (fun sts_body ->
  construct_steps_eapp f f1 x x' e' h lt1 lt2a lt2b sts_f sts_x sts_body;
  trans_history (h++lt1) lt2a lt2b;
  trans_history h lt1 (lt2a@lt2b))))
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let helper_ocomp_app_inner_bind (h:history) (lt:local_trace h) (a b:qType)
  (lt1:local_trace h) (lt2:local_trace (h++lt1))
  (fs_r_f:fs_val (a ^->!@ b)) (fs_r:fs_val b)
  (fs_x':fs_comp a) (f':closed_exp) (f x:closed_exp) :
  Lemma
    (requires
      lt == lt1@lt2 /\
      (a ^->!@ b) ∈ (h++lt1, fs_r_f, f') /\ e_beh f f' h lt1 /\
      is_value f' /\ indexed_irred f' (h++lt1) /\
      fs_beh (fs_comp_bind fs_x' (fun x' -> fs_r_f x')) (h++lt1) lt2 fs_r /\
      a ⫃ (h++lt1, fs_x', x))
    (ensures exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt) =
  assert (fs_comp_bind fs_x' (fun x' -> fs_r_f x') == io_bind fs_x' (fun x' -> fs_r_f x')) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
  destruct_fs_beh fs_x' (fun x' -> fs_r_f x') (h++lt1) lt2 fs_r;
  eliminate exists (lt2a:local_trace (h++lt1)) (lt2b:local_trace ((h++lt1)++lt2a)) (fs_r_x:fs_val a).
    lt2 == (lt2a@lt2b) /\ fs_beh fs_x' (h++lt1) lt2a fs_r_x /\ fs_beh (fs_r_f fs_r_x) ((h++lt1)++lt2a) lt2b fs_r
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
  assert (a ⫃ (h++lt1, fs_x', x));
  eliminate forall (lt':local_trace (h++lt1)) (fs_r':get_Type a). fs_beh fs_x' (h++lt1) lt' fs_r' ==> exists e'. a ∈ ((h++lt1)++lt', fs_r', e') /\ e_beh x e' (h++lt1) lt' with lt2a fs_r_x;
  eliminate exists x'. a ∈ ((h++lt1)++lt2a, fs_r_x, x') /\ e_beh x x' (h++lt1) lt2a
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
  lem_values_are_values a ((h++lt1)++lt2a) fs_r_x x';
  helper_ocomp_app_from_arg_value h lt a b lt1 lt2a lt2b fs_r_f fs_r_x fs_r f' x' f x
  end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let helper_compat_ocomp_app_steps (h:history) (lt:local_trace h) (a b:qType)
  (fs_f':fs_comp (a ^->!@ b)) (fs_x':fs_comp a) (fs_r:fs_val b)
  (f x:closed_exp) :
  Lemma
    (requires fs_beh (fs_comp_bind fs_f' (fun f' -> fs_comp_bind fs_x' (fun x' -> f' x'))) h lt fs_r /\
              (a ^->!@ b) ⫃ (h, fs_f', f) /\
              (forall (lt':local_trace h). a ⫃ (h++lt', fs_x', x)))
    (ensures exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt) =
  let fs_outer_k : fs_val (a ^->!@ b) -> fs_comp b = fun f' -> fs_comp_bind fs_x' (fun x' -> f' x') in
  assert (fs_comp_bind fs_f' fs_outer_k == io_bind fs_f' fs_outer_k) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
  destruct_fs_beh fs_f' fs_outer_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_r_f:fs_val (a ^->!@ b)).
    lt == (lt1@lt2) /\ fs_beh fs_f' h lt1 fs_r_f /\ fs_beh (fs_outer_k fs_r_f) (h++lt1) lt2 fs_r
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
  eliminate forall (lt':local_trace h) (fs_r':get_Type (a ^->!@ b)). fs_beh fs_f' h lt' fs_r' ==> exists e'. (a ^->!@ b) ∈ (h++lt', fs_r', e') /\ e_beh f e' h lt' with lt1 fs_r_f;
  eliminate exists f'. (a ^->!@ b) ∈ (h++lt1, fs_r_f, f') /\ e_beh f f' h lt1
    returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
  lem_values_are_values (a ^->!@ b) (h++lt1) fs_r_f f';
  lem_value_is_irred f';
  assert (a ⫃ (h++lt1, fs_x', x));
  assert (fs_outer_k fs_r_f == fs_comp_bind fs_x' (fun x' -> fs_r_f x')) by (norm []; trefl ());
  helper_ocomp_app_inner_bind h lt a b lt1 lt2 fs_r_f fs_r fs_x' f' f x
  end
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2 --split_queries always"
let compat_ocomp_app #g (#a #b:qType) #preF #preX (fs_f:fs_ocomp g (a ^->!@ b) preF) (fs_x:fs_ocomp g a preX) (f x:exp)
  : Lemma
    (requires fs_f ⊑ f /\ fs_x ⊑ x)
    (ensures fs_ocomp_app fs_f fs_x ⊑ EApp f x) =
  lem_fv_in_env_app g f x;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(≍) h` s /\ (spec_env_bind' #g #(a ^->!@ b) preF (fun f' -> spec_env_bind' #g #a preX (fun x' -> spec_env_return_comp #g #b (f' x')))) fsG) ==> b ⫃ (h, fs_ocomp_app fs_f fs_x fsG, gsubst s (EApp f x)) with begin
    introduce _ ==> _ with _. begin
      assert (preF fsG);
      let fs_f' : fs_comp (a ^->!@ b) = fs_f fsG in
      let fs_e = fs_ocomp_app fs_f fs_x fsG in
      let e = EApp (gsubst s f) (gsubst s x) in
      assert (gsubst s (EApp f x) == e);
      let EApp f x = e in
      introduce fsG `(≍) h` s ==> b ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val b). fs_beh fs_e h lt fs_r ==> exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            (* Destruct the outer [fs_comp_bind fs_f' ...] to obtain a concrete result
               [fs_r_f : fs_val (a ^->!@ b)] produced by running the function IO computation.
               This real witness lets us instantiate the [forall f'] quantifier from the
               outer [spec_env_bind'] precondition to extract [preX fsG] — mirroring how
               [compat_ocomp_if] uses the limited-domain values [true]/[false] to
               instantiate [forall x:fs_val qBool]. *)
            let fs_outer_k : fs_val (a ^->!@ b) -> fs_comp b = fun f' -> fs_comp_bind (fs_x fsG) (fun x' -> f' x') in
            assert (fs_e == fs_comp_bind fs_f' fs_outer_k) by (
              norm [delta_only [`%fs_ocomp_app;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_app_oval_oval;`%fs_ocomp_return]];
              simplify_stack_ops ();
              trefl ());
            assert (fs_comp_bind fs_f' fs_outer_k == io_bind fs_f' fs_outer_k) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
            destruct_fs_beh fs_f' fs_outer_k h lt fs_r;
            eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_r_f:fs_val (a ^->!@ b)).
              lt == (lt1@lt2) /\ fs_beh fs_f' h lt1 fs_r_f /\ fs_beh (fs_outer_k fs_r_f) (h++lt1) lt2 fs_r
              returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (EApp f x) e' h lt with _. begin
              (* Use the real [fs_r_f] (the value produced by running the first IO
                 computation) to instantiate [forall f'. preX fsG /\ ...]. *)
              eliminate forall (f':fs_val (a ^->!@ b)).
                spec_env_bind' #g #a preX (fun x' -> spec_env_return_comp #g #b (f' x')) fsG
                with fs_r_f;
              assert (preX fsG);
              let fs_x' : fs_comp a = fs_x fsG in
              (* Reassemble [fs_e] in the form expected by [helper_compat_ocomp_app_steps]. *)
              let fs_e' = fs_comp_bind fs_f' (fun f' -> fs_comp_bind fs_x' (fun x' -> f' x')) in
              assert (fs_e == fs_e') by (
                norm [delta_only [`%fs_ocomp_app;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_app_oval_oval;`%fs_ocomp_return]];
                simplify_stack_ops ();
                trefl ());
              assert (fs_beh fs_e' h lt fs_r);
              helper_compat_ocomp_app_steps h lt a b fs_f' fs_x' fs_r f x
            end
          end
        end
      end
    end
  end
#pop-options

let compat_ocomp_lambda #g (#t1:qType) (#preBody:spec_env (extend t1 g)) (#t2:qType)
  (fs_body:fs_ocomp (extend t1 g) t2 preBody)
  (body:exp)
  : Lemma
    (requires fs_body ⊑ body)
    (ensures fs_ocomp_lambda fs_body ⊑ (ELam body))
  =
  compat_oval_lambda_ocomp #g #t1 #preBody #t2 fs_body body;
  compat_ocomp_return (fs_oval_lambda_ocomp fs_body) (ELam body)

(** ---- Helpers for fmap-based lemmas (inl, inr, fst, snd) ---- **)

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let helper_compat_ocomp_fmap_inl_steps (h:history) (lt:local_trace h) (t1 t2:qType)
  (fs_e':fs_comp t1) (fs_r:fs_val (t1 ^+ t2)) (e:closed_exp) :
  Lemma
    (requires fs_beh (fs_comp_bind fs_e' (fun v -> return (Inl #(fs_val t1) #(fs_val t2) v))) h lt fs_r /\
              t1 ⫃ (h, fs_e', e))
    (ensures exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh (EInl e) e' h lt) =
  let fs_k : fs_val t1 -> fs_comp (t1 ^+ t2) = fun v -> return (Inl #(fs_val t1) #(fs_val t2) v) in
  assert (fs_comp_bind fs_e' fs_k == io_bind fs_e' fs_k) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
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

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let helper_compat_ocomp_fmap_inr_steps (h:history) (lt:local_trace h) (t1 t2:qType)
  (fs_e':fs_comp t2) (fs_r:fs_val (t1 ^+ t2)) (e:closed_exp) :
  Lemma
    (requires fs_beh (fs_comp_bind fs_e' (fun v -> return (Inr #(fs_val t1) #(fs_val t2) v))) h lt fs_r /\
              t2 ⫃ (h, fs_e', e))
    (ensures exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh (EInr e) e' h lt) =
  let fs_k : fs_val t2 -> fs_comp (t1 ^+ t2) = fun v -> return (Inr #(fs_val t1) #(fs_val t2) v) in
  assert (fs_comp_bind fs_e' fs_k == io_bind fs_e' fs_k) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
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

#push-options "--z3rlimit 15 --fuel 1 --ifuel 1"
let helper_compat_ocomp_fmap_fst_steps (h:history) (lt:local_trace h) (t1 t2:qType)
  (fs_e12':fs_comp (t1 ^* t2)) (fs_r:fs_val t1) (e12:closed_exp) :
  Lemma
    (requires fs_beh (fs_comp_bind fs_e12' (fun v -> return (fst #(fs_val t1) #(fs_val t2) v))) h lt fs_r /\
              (t1 ^* t2) ⫃ (h, fs_e12', e12))
    (ensures exists e'. t1 ∈ (h++lt, fs_r, e') /\ e_beh (EFst e12) e' h lt) =
  let fs_k : fs_val (t1 ^* t2) -> fs_comp t1 = fun v -> return (fst #(fs_val t1) #(fs_val t2) v) in
  assert (fs_comp_bind fs_e12' fs_k == io_bind fs_e12' fs_k) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
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

#push-options "--z3rlimit 15 --fuel 1 --ifuel 1"
let helper_compat_ocomp_fmap_snd_steps (h:history) (lt:local_trace h) (t1 t2:qType)
  (fs_e12':fs_comp (t1 ^* t2)) (fs_r:fs_val t2) (e12:closed_exp) :
  Lemma
    (requires fs_beh (fs_comp_bind fs_e12' (fun v -> return (snd #(fs_val t1) #(fs_val t2) v))) h lt fs_r /\
              (t1 ^* t2) ⫃ (h, fs_e12', e12))
    (ensures exists e'. t2 ∈ (h++lt, fs_r, e') /\ e_beh (ESnd e12) e' h lt) =
  let fs_k : fs_val (t1 ^* t2) -> fs_comp t2 = fun v -> return (snd #(fs_val t1) #(fs_val t2) v) in
  assert (fs_comp_bind fs_e12' fs_k == io_bind fs_e12' fs_k) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
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

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let helper_ocomp_pair_from_values
  (h:history) (lt:local_trace h) (t1 t2:qType)
  (lt1:local_trace h) (lt2a:local_trace (h++lt1))
  (fs_v1:fs_val t1) (fs_v2:fs_val t2) (em1 em2 e1 e2:closed_exp) :
  Lemma
    (requires
      lt == lt1@lt2a /\
      t1 ∈ (h++lt1, fs_v1, em1) /\ e_beh e1 em1 h lt1 /\
      t2 ∈ ((h++lt1)++lt2a, fs_v2, em2) /\ e_beh e2 em2 (h++lt1) lt2a)
    (ensures exists e'. (t1 ^* t2) ∈ (h++lt, (fs_v1, fs_v2), e') /\ e_beh (EPair e1 e2) e' h lt) =
  lem_values_are_values t1 (h++lt1) fs_v1 em1;
  lem_values_are_values t2 ((h++lt1)++lt2a) fs_v2 em2;
  lem_value_is_irred em1;
  lem_value_is_irred em2;
  trans_history h lt1 lt2a;
  val_type_closed_under_history_extension t1 (h++lt1) fs_v1 em1;
  lem_value_is_irred (EPair em1 em2);
  let goal : Type0 = (exists e'. (t1 ^* t2) ∈ (h++lt, (fs_v1, fs_v2), e') /\ e_beh (EPair e1 e2) e' h lt) in
  FStar.Squash.bind_squash #(steps e1 em1 h lt1) #goal () (fun sts1 ->
  FStar.Squash.bind_squash #(steps e2 em2 (h++lt1) lt2a) #goal () (fun sts2 ->
  construct_steps_epair e1 em1 e2 em2 h lt1 lt2a sts1 sts2;
  assert (steps (EPair e1 e2) (EPair em1 em2) h (lt1@lt2a))))
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let helper_ocomp_pair_inner_bind
  (h:history) (lt:local_trace h) (t1 t2:qType)
  (lt1:local_trace h) (lt2:local_trace (h++lt1))
  (fs_v1:fs_val t1) (em1:closed_exp)
  (fs_e2':fs_comp t2) (fs_r:fs_val (t1 ^* t2))
  (e1 e2:closed_exp) :
  Lemma
    (requires
      lt == lt1@lt2 /\
      t1 ∈ (h++lt1, fs_v1, em1) /\ e_beh e1 em1 h lt1 /\
      is_value em1 /\ indexed_irred em1 (h++lt1) /\
      fs_beh (fs_comp_bind #t2 #(t1 ^* t2) fs_e2' (fun v2 -> return (fs_v1, v2))) (h++lt1) lt2 fs_r /\
      t2 ⫃ (h++lt1, fs_e2', e2))
    (ensures exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh (EPair e1 e2) e' h lt) =
  let fs_k2 : fs_val t2 -> fs_comp (t1 ^* t2) = fun v2 -> return (fs_v1, v2) in
  assert (fs_comp_bind #t2 #(t1 ^* t2) fs_e2' fs_k2 == io_bind fs_e2' fs_k2) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
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
  assert (t2 ⫃ (h++lt1, fs_e2', e2));
  eliminate forall (lt':local_trace (h++lt1)) (fs_r':get_Type t2). fs_beh fs_e2' (h++lt1) lt' fs_r' ==> exists em'. t2 ∈ ((h++lt1)++lt', fs_r', em') /\ e_beh e2 em' (h++lt1) lt' with lt2a fs_v2;
  eliminate exists em2. t2 ∈ ((h++lt1)++lt2a, fs_v2, em2) /\ e_beh e2 em2 (h++lt1) lt2a
    returns exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh (EPair e1 e2) e' h lt with _. begin
  helper_ocomp_pair_from_values h lt t1 t2 lt1 lt2a fs_v1 fs_v2 em1 em2 e1 e2
  end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let helper_compat_ocomp_pair_steps (h:history) (lt:local_trace h) (t1 t2:qType)
  (fs_e1':fs_comp t1) (fs_e2':fs_comp t2) (fs_r:fs_val (t1 ^* t2)) (e1 e2:closed_exp) :
  Lemma
    (requires fs_beh (fs_comp_bind fs_e1' (fun v1 -> fs_comp_bind #t2 #(t1 ^* t2) fs_e2' (fun v2 -> return (v1, v2)))) h lt fs_r /\
              t1 ⫃ (h, fs_e1', e1) /\
              (forall (lt':local_trace h). t2 ⫃ (h++lt', fs_e2', e2)))
    (ensures exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh (EPair e1 e2) e' h lt) =
  let fs_k1 : fs_val t1 -> fs_comp (t1 ^* t2) = fun v1 -> fs_comp_bind #t2 #(t1 ^* t2) fs_e2' (fun v2 -> return (v1, v2)) in
  assert (fs_comp_bind fs_e1' fs_k1 == io_bind fs_e1' fs_k1) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
  destruct_fs_beh fs_e1' fs_k1 h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_v1:fs_val t1).
    lt == (lt1@lt2) /\ fs_beh fs_e1' h lt1 fs_v1 /\ fs_beh (fs_k1 fs_v1) (h++lt1) lt2 fs_r
    returns exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh (EPair e1 e2) e' h lt with _. begin
  eliminate forall (lt':local_trace h) (fs_r':get_Type t1). fs_beh fs_e1' h lt' fs_r' ==> exists em'. t1 ∈ (h++lt', fs_r', em') /\ e_beh e1 em' h lt' with lt1 fs_v1;
  eliminate exists em1. t1 ∈ (h++lt1, fs_v1, em1) /\ e_beh e1 em1 h lt1
    returns exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh (EPair e1 e2) e' h lt with _. begin
  lem_values_are_values t1 (h++lt1) fs_v1 em1;
  lem_value_is_irred em1;
  assert (t2 ⫃ (h++lt1, fs_e2', e2));
  assert (fs_k1 fs_v1 == fs_comp_bind #t2 #(t1 ^* t2) fs_e2' (fun v2 -> return (fs_v1, v2))) by (norm []; trefl ());
  helper_ocomp_pair_inner_bind h lt t1 t2 lt1 lt2 fs_v1 em1 fs_e2' fs_r e1 e2
  end
  end
#pop-options

(** ---- Helpers for IO operation bind decomposition ---- **)

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2 --split_queries always"
let helper_compat_ocomp_call_steps (op:io_ops) (h:history) (lt:local_trace h)
  (fs_arg':fs_comp (q_io_args op){fs_val (q_io_args op) == io_args op}) (fs_e:fs_comp (q_io_res op){fs_e == fs_comp_bind #(q_io_args op) #(q_io_res op) fs_arg' (fun arg' -> fs_comp_call_val op arg')}) (fs_r:fs_val (q_io_res op)) (arg:closed_exp) :
  Lemma
    (requires fs_beh fs_e h lt fs_r /\
              fs_e == fs_comp_bind fs_arg' (fun arg' -> fs_comp_call_val op arg') /\
              (q_io_args op) ⫃ (h, fs_arg', arg))
    (ensures exists e'. (q_io_res op) ∈ (h++lt, fs_r, e') /\ e_beh (ECall op arg) e' h lt) = admit ()
  (*let fs_k : fs_val (q_io_args op) -> fs_comp (q_io_res op) = fun arg' -> fs_comp_call_val op arg' in
  assert (fs_comp_bind fs_arg' fs_k == io_bind fs_arg' fs_k) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
  assert (fs_e == fs_comp_bind fs_arg' fs_k);
  destruct_fs_beh fs_arg' fs_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_arg_val:fs_val (q_io_args op)).
    lt == (lt1@lt2) /\ fs_beh fs_arg' h lt1 fs_arg_val /\ fs_beh (fs_k fs_arg_val) (h++lt1) lt2 fs_r
    returns exists e'. (q_io_res op) ∈ (h++lt, fs_r, e') /\ e_beh (ECall op arg) e' h lt with _. begin
  eliminate forall (lt':local_trace h) (fs_r':get_Type (q_io_args op)). fs_beh fs_arg' h lt' fs_r' ==> exists em'. (q_io_args op) ∈ (h++lt', fs_r', em') /\ e_beh arg em' h lt' with lt1 fs_arg_val;
  eliminate exists em'. (q_io_args op) ∈ (h++lt1, fs_arg_val, em') /\ e_beh arg em' h lt1
    returns exists e'. (q_io_res op) ∈ (h++lt, fs_r, e') /\ e_beh (ECall op arg) e' h lt with _. begin
  lem_values_are_values (q_io_args op) (h++lt1) fs_arg_val em';
  trans_history h lt1 lt2;
  assert (fs_val (q_io_args OOpen) == string)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res OOpen) == resexn file_descr)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_args ORead) == file_descr)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res ORead) == resexn string)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_args OWrite) == (file_descr * string))
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res OWrite) == resexn unit)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_args OClose) == file_descr)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res OClose) == resexn unit)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  helper_compat_ocomp_call_oval_steps op (h++lt1) lt2 fs_arg_val em' fs_e fs_r;
  eliminate exists e'. (q_io_res op) ∈ ((h++lt1)++lt2, fs_r, e') /\ e_beh (ECall op em') e' (h++lt1) lt2
    returns exists e'. (q_io_res op) ∈ (h++lt, fs_r, e') /\ e_beh (ECall op arg) e' h lt with _. begin
  FStar.Squash.bind_squash #(steps arg em' h lt1) () (fun sts_arg ->
  FStar.Squash.bind_squash #(steps (ECall op em') e' (h++lt1) lt2) () (fun sts_call ->
  construct_steps_ecall op arg em' h lt1 sts_arg;
  lem_steps_transitive (ECall op arg) (ECall op em') e' h lt1 lt2))
  end
  end
  end*)
#pop-options

let lem_fs_beh_return_inv (#t:qType) (val_:fs_val t) (h:history) (lt:local_trace h) (fs_r:fs_val t) :
  Lemma (requires fs_beh (return val_) h lt fs_r)
        (ensures lt == [] /\ fs_r == val_) =
  theta_monad_morphism_ret val_;
  assert (theta (io_return val_) == hist_return val_);
  let p : hist_post h (get_Type t) = fun lt' r' -> lt' == [] /\ r' == val_ in
  assert (hist_return val_ h p);
  assert (theta (io_return val_) h p);
  assert (thetaP (io_return val_) h lt fs_r);
  assert (p lt fs_r)

(** ---- Case helper for bind decomposition ---- **)

#push-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let helper_compat_ocomp_case_steps (h:history) (lt:local_trace h) (a b c:qType)
  (fs_sc':fs_comp (a ^+ b))
  (fs_inlc:fs_val (a ^->!@ c))
  (fs_inrc:fs_val (b ^->!@ c))
  (fs_r:fs_val c)
  (e_sc:closed_exp)
  (e_lc:exp{is_closed (ELam e_lc)})
  (e_rc:exp{is_closed (ELam e_rc)}) :
  Lemma
    (requires fs_beh (fs_comp_bind fs_sc' (fun x -> fs_comp_case_val x fs_inlc fs_inrc)) h lt fs_r /\
              (a ^+ b) ⫃ (h, fs_sc', e_sc) /\
              (a ^->!@ c) ⊆ (h, fs_inlc, ELam e_lc) /\
              (b ^->!@ c) ⊆ (h, fs_inrc, ELam e_rc))
    (ensures exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh (ECase e_sc e_lc e_rc) e' h lt) =
  let fs_k : fs_val (a ^+ b) -> fs_comp c = fun x -> fs_comp_case_val x fs_inlc fs_inrc in
  assert (fs_comp_bind fs_sc' fs_k == io_bind fs_sc' fs_k) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
  destruct_fs_beh fs_sc' fs_k h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_cond_val:fs_val (a ^+ b)).
    lt == (lt1@lt2) /\ fs_beh fs_sc' h lt1 fs_cond_val /\ fs_beh (fs_comp_case_val fs_cond_val fs_inlc fs_inrc) (h++lt1) lt2 fs_r
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
  helper_compat_ocomp_case_oval_steps (h++lt1) lt2 a b c fs_cond_val fs_inlc fs_inrc fs_r em' e_lc e_rc;
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

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2 --split_queries always"
let compat_ocomp_pair #g
  (#t1 #t2:qType) #preX #preY
  (fs_e1:fs_ocomp g t1 preX) (fs_e2:fs_ocomp g t2 preY)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊑ e1 /\ fs_e2 ⊑ e2)
    (ensures fs_ocomp_pair fs_e1 fs_e2 ⊑ EPair e1 e2) =
  lem_fv_in_env_pair g e1 e2;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(≍) h` s /\ (spec_env_bind' #g #t1 preX (fun x' -> spec_env_bind' #g #t2 preY (fun y' -> spec_env_return_comp #g #(t1 ^* t2) (io_return (fs_val_pair x' y'))))) fsG) ==> (t1 ^* t2) ⫃ (h, fs_ocomp_pair fs_e1 fs_e2 fsG, gsubst s (EPair e1 e2)) with begin
    introduce _ ==> _ with _. begin
      assert (preX fsG);
      let fs_e1' : fs_comp t1 = fs_e1 fsG in
      let fs_e = fs_ocomp_pair fs_e1 fs_e2 fsG in
      let fs_e_bound = fs_comp_bind fs_e1' (fun v1 -> fs_comp_bind #t2 #(t1 ^* t2) (fs_e2 fsG) (fun v2 -> return (v1, v2))) in
      assert (fs_e == fs_e_bound) by (
        norm [delta_only [`%fs_ocomp_pair;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val;`%fs_val_pair]];
        simplify_stack_ops ();
        trefl ());
      let e = EPair (gsubst s e1) (gsubst s e2) in
      assert (gsubst s (EPair e1 e2) == e);
      let EPair e1 e2 = e in
      introduce fsG `(≍) h` s ==> (t1 ^* t2) ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val (t1 ^* t2)). fs_beh fs_e h lt fs_r ==> exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            (* Destruct the outer [fs_comp_bind fs_e1' ...] to obtain a concrete result
               [fs_v1 : fs_val t1] produced by running the first IO computation. This
               real witness lets us instantiate the [forall x'] quantifier from the
               outer [spec_env_bind'] precondition to extract [preY fsG] — mirroring
               how [compat_ocomp_app] instantiates [forall f'] with the real function
               value produced by the first component. *)
            let fs_outer_k : fs_val t1 -> fs_comp (t1 ^* t2) =
              fun v1 -> fs_comp_bind #t2 #(t1 ^* t2) (fs_e2 fsG) (fun v2 -> return (v1, v2)) in
            assert (fs_e == fs_comp_bind fs_e1' fs_outer_k) by (
              norm [delta_only [`%fs_ocomp_pair;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val;`%fs_val_pair]];
              simplify_stack_ops ();
              trefl ());
            assert (fs_comp_bind fs_e1' fs_outer_k == io_bind fs_e1' fs_outer_k) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
            destruct_fs_beh fs_e1' fs_outer_k h lt fs_r;
            eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_v1:fs_val t1).
              lt == (lt1@lt2) /\ fs_beh fs_e1' h lt1 fs_v1 /\ fs_beh (fs_outer_k fs_v1) (h++lt1) lt2 fs_r
              returns exists e'. (t1 ^* t2) ∈ (h++lt, fs_r, e') /\ e_beh (EPair e1 e2) e' h lt with _. begin
              (* Use the real [fs_v1] (the value produced by running the first IO
                 computation) to instantiate [forall x'. preY fsG /\ ...]. *)
              eliminate forall (x':fs_val t1).
                spec_env_bind' #g #t2 preY (fun y' -> spec_env_return_comp #g #(t1 ^* t2) (io_return (fs_val_pair x' y'))) fsG
                with fs_v1;
              assert (preY fsG);
              let fs_e2' : fs_comp t2 = fs_e2 fsG in
              (* Reassemble [fs_e] in the form expected by [helper_compat_ocomp_pair_steps]. *)
              let fs_e' = fs_comp_bind fs_e1' (fun v1 -> fs_comp_bind #t2 #(t1 ^* t2) fs_e2' (fun v2 -> return (v1, v2))) in
              assert (fs_e == fs_e') by (
                norm [delta_only [`%fs_ocomp_pair;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val;`%fs_val_pair]];
                simplify_stack_ops ();
                trefl ());
              assert (fs_beh fs_e' h lt fs_r);
              helper_compat_ocomp_pair_steps h lt t1 t2 fs_e1' fs_e2' fs_r e1 e2
            end
          end
        end
      end
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let helper_ocomp_string_eq_from_values
  (h:history) (lt1:local_trace h) (lt2a:local_trace (h++lt1))
  (fs_v1 fs_v2:fs_val qString) (em1 em2 e1 e2:closed_exp)
  : Lemma
    (requires
      qString ∈ (h++lt1, fs_v1, em1) /\ e_beh e1 em1 h lt1 /\
      qString ∈ ((h++lt1)++lt2a, fs_v2, em2) /\ e_beh e2 em2 (h++lt1) lt2a)
    (ensures exists e'. qBool ∈ (h++(lt1@lt2a), (fs_v1 = fs_v2), e') /\ e_beh (EStringEq e1 e2) e' h (lt1@lt2a)) =
  lem_values_are_values qString (h++lt1) fs_v1 em1;
  lem_values_are_values qString ((h++lt1)++lt2a) fs_v2 em2;
  lem_value_is_irred em1;
  lem_value_is_irred em2;
  trans_history h lt1 lt2a;
  val_type_closed_under_history_extension qString (h++lt1) fs_v1 em1;
  let EString s1 = em1 in
  let EString s2 = em2 in
  let result = if s1 = s2 then ETrue else EFalse in
  let _ : step (EStringEq (EString s1) (EString s2)) result ((h++lt1)++lt2a) None = StringEqReturn s1 s2 ((h++lt1)++lt2a) in
  lem_step_implies_steps (EStringEq (EString s1) (EString s2)) result ((h++lt1)++lt2a) None;
  lem_value_is_irred result;
  assert ((h++lt1)++lt2a == h++(lt1@lt2a));
  assert (steps (EStringEq (EString s1) (EString s2)) result (h++(lt1@lt2a)) []);
  assert (indexed_irred em1 (h++lt1));
  assert (indexed_irred em2 ((h++lt1)++lt2a));
  let goal : Type0 = (exists e'. qBool ∈ (h++(lt1@lt2a), (fs_v1 = fs_v2), e') /\ e_beh (EStringEq e1 e2) e' h (lt1@lt2a)) in
  FStar.Squash.bind_squash #(steps e1 em1 h lt1) #goal () (fun sts1 ->
  FStar.Squash.bind_squash #(steps e2 em2 (h++lt1) lt2a) #goal () (fun sts2 ->
  construct_steps_estringeq e1 em1 e2 em2 h lt1 lt2a sts1 sts2;
  lem_steps_transitive (EStringEq e1 e2) (EStringEq (EString s1) (EString s2)) result h (lt1@lt2a) [];
  unit_l (lt1@lt2a)))
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let helper_ocomp_string_eq_inner_bind
  (h:history) (lt:local_trace h)
  (lt1:local_trace h) (lt2:local_trace (h++lt1))
  (fs_v1:fs_val qString) (em1:closed_exp)
  (fs_e2':fs_comp qString) (fs_r:fs_val qBool)
  (e1 e2:closed_exp) :
  Lemma
    (requires
      lt == lt1@lt2 /\
      qString ∈ (h++lt1, fs_v1, em1) /\ e_beh e1 em1 h lt1 /\
      is_value em1 /\ indexed_irred em1 (h++lt1) /\
      fs_beh (fs_comp_bind #qString #qBool fs_e2' (fun v2 -> return (fs_v1 = v2))) (h++lt1) lt2 fs_r /\
      qString ⫃ (h++lt1, fs_e2', e2))
    (ensures exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh (EStringEq e1 e2) e' h lt) =
  let fs_k2 : fs_val qString -> fs_comp qBool = fun v2 -> return (fs_v1 = v2) in
  assert (fs_comp_bind #qString #qBool fs_e2' fs_k2 == io_bind fs_e2' fs_k2) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
  destruct_fs_beh fs_e2' fs_k2 (h++lt1) lt2 fs_r;
  eliminate exists (lt2a:local_trace (h++lt1)) (lt2b:local_trace ((h++lt1)++lt2a)) (fs_v2:fs_val qString).
    lt2 == (lt2a@lt2b) /\ fs_beh fs_e2' (h++lt1) lt2a fs_v2 /\ fs_beh (return (fs_v1 = fs_v2)) ((h++lt1)++lt2a) lt2b fs_r
    returns exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh (EStringEq e1 e2) e' h lt with _. begin
  lem_fs_beh_return_inv #qBool (fs_v1 = fs_v2) ((h++lt1)++lt2a) lt2b fs_r;
  assert (lt2b == []);
  assert (fs_r == (fs_v1 = fs_v2));
  unit_l lt2a;
  assert (qString ⫃ (h++lt1, fs_e2', e2));
  eliminate forall (lt':local_trace (h++lt1)) (fs_r':get_Type qString). fs_beh fs_e2' (h++lt1) lt' fs_r' ==> exists em'. qString ∈ ((h++lt1)++lt', fs_r', em') /\ e_beh e2 em' (h++lt1) lt' with lt2a fs_v2;
  eliminate exists em2. qString ∈ ((h++lt1)++lt2a, fs_v2, em2) /\ e_beh e2 em2 (h++lt1) lt2a
    returns exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh (EStringEq e1 e2) e' h lt with _. begin
  helper_ocomp_string_eq_from_values h lt1 lt2a fs_v1 fs_v2 em1 em2 e1 e2
  end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
let helper_compat_ocomp_string_eq_steps (h:history) (lt:local_trace h)
  (fs_e1':fs_comp qString) (fs_e2':fs_comp qString) (fs_r:fs_val qBool) (e1 e2:closed_exp) :
  Lemma
    (requires fs_beh (fs_comp_bind fs_e1' (fun v1 -> fs_comp_bind #qString #qBool fs_e2' (fun v2 -> return (v1 = v2)))) h lt fs_r /\
              qString ⫃ (h, fs_e1', e1) /\
              (forall (lt':local_trace h). qString ⫃ (h++lt', fs_e2', e2)))
    (ensures exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh (EStringEq e1 e2) e' h lt) =
  let fs_k1 : fs_val qString -> fs_comp qBool = fun v1 -> fs_comp_bind #qString #qBool fs_e2' (fun v2 -> return (v1 = v2)) in
  assert (fs_comp_bind fs_e1' fs_k1 == io_bind fs_e1' fs_k1) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
  destruct_fs_beh fs_e1' fs_k1 h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_v1:fs_val qString).
    lt == (lt1@lt2) /\ fs_beh fs_e1' h lt1 fs_v1 /\ fs_beh (fs_k1 fs_v1) (h++lt1) lt2 fs_r
    returns exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh (EStringEq e1 e2) e' h lt with _. begin
  eliminate forall (lt':local_trace h) (fs_r':get_Type qString). fs_beh fs_e1' h lt' fs_r' ==> exists em'. qString ∈ (h++lt', fs_r', em') /\ e_beh e1 em' h lt' with lt1 fs_v1;
  eliminate exists em1. qString ∈ (h++lt1, fs_v1, em1) /\ e_beh e1 em1 h lt1
    returns exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh (EStringEq e1 e2) e' h lt with _. begin
  lem_values_are_values qString (h++lt1) fs_v1 em1;
  lem_value_is_irred em1;
  assert (qString ⫃ (h++lt1, fs_e2', e2));
  assert (fs_k1 fs_v1 == fs_comp_bind #qString #qBool fs_e2' (fun v2 -> return (fs_v1 = v2))) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
  helper_ocomp_string_eq_inner_bind h lt lt1 lt2 fs_v1 em1 fs_e2' fs_r e1 e2
  end
  end
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2 --split_queries always"
let compat_ocomp_string_eq #g #preX #preY
  (fs_e1:fs_ocomp g qString preX) (fs_e2:fs_ocomp g qString preY)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊑ e1 /\ fs_e2 ⊑ e2)
    (ensures fs_ocomp_string_eq fs_e1 fs_e2 ⊑ EStringEq e1 e2) =
  lem_fv_in_env_string_eq g e1 e2;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(≍) h` s /\ (spec_env_bind' #g #qString preX (fun x' -> spec_env_bind' #g #qString preY (fun y' -> spec_env_return_comp #g #qBool (io_return (x' = y'))))) fsG) ==> qBool ⫃ (h, fs_ocomp_string_eq fs_e1 fs_e2 fsG, gsubst s (EStringEq e1 e2)) with begin
    introduce _ ==> _ with _. begin
      assert (preX fsG);
      let fs_e1' : fs_comp qString = fs_e1 fsG in
      let fs_e = fs_ocomp_string_eq fs_e1 fs_e2 fsG in
      let fs_e_bound = fs_comp_bind fs_e1' (fun v1 -> fs_comp_bind #qString #qBool (fs_e2 fsG) (fun v2 -> return (v1 = v2))) in
      assert (fs_e == fs_e_bound) by (
        norm [delta_only [`%fs_ocomp_string_eq;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val]];
        simplify_stack_ops ();
        trefl ());
      let e = EStringEq (gsubst s e1) (gsubst s e2) in
      assert (gsubst s (EStringEq e1 e2) == e);
      let EStringEq e1 e2 = e in
      introduce fsG `(≍) h` s ==> qBool ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val qBool). fs_beh fs_e h lt fs_r ==> exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            (* Destruct the outer [fs_comp_bind fs_e1' ...] to obtain a concrete result
               [fs_v1 : fs_val qString] produced by running the first IO computation.
               This real witness lets us instantiate the [forall x'] quantifier from the
               outer [spec_env_bind'] precondition to extract [preY fsG] — mirroring
               how [compat_ocomp_pair] instantiates [forall x'] with the real value
               produced by the first component. *)
            let fs_outer_k : fs_val qString -> fs_comp qBool =
              fun v1 -> fs_comp_bind #qString #qBool (fs_e2 fsG) (fun v2 -> return (v1 = v2)) in
            assert (fs_e == fs_comp_bind fs_e1' fs_outer_k) by (
              norm [delta_only [`%fs_ocomp_string_eq;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val]];
              simplify_stack_ops ();
              trefl ());
            assert (fs_comp_bind fs_e1' fs_outer_k == io_bind fs_e1' fs_outer_k) by (norm [delta_only [`%fs_comp_bind]]; trefl ());
            destruct_fs_beh fs_e1' fs_outer_k h lt fs_r;
            eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_v1:fs_val qString).
              lt == (lt1@lt2) /\ fs_beh fs_e1' h lt1 fs_v1 /\ fs_beh (fs_outer_k fs_v1) (h++lt1) lt2 fs_r
              returns exists e'. qBool ∈ (h++lt, fs_r, e') /\ e_beh (EStringEq e1 e2) e' h lt with _. begin
              (* Use the real [fs_v1] (the value produced by running the first IO
                 computation) to instantiate [forall x'. preY fsG /\ ...]. *)
              eliminate forall (x':fs_val qString).
                spec_env_bind' #g #qString preY (fun y' -> spec_env_return_comp #g #qBool (io_return (x' = y'))) fsG
                with fs_v1;
              assert (preY fsG);
              let fs_e2' : fs_comp qString = fs_e2 fsG in
              (* Reassemble [fs_e] in the form expected by [helper_compat_ocomp_string_eq_steps]. *)
              let fs_e' = fs_comp_bind fs_e1' (fun v1 -> fs_comp_bind #qString #qBool fs_e2' (fun v2 -> return (v1 = v2))) in
              assert (fs_e == fs_e') by (
                norm [delta_only [`%fs_ocomp_string_eq;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val]];
                simplify_stack_ops ();
                trefl ());
              assert (fs_beh fs_e' h lt fs_r);
              helper_compat_ocomp_string_eq_steps h lt fs_e1' fs_e2' fs_r e1 e2
            end
          end
        end
      end
    end
  end
#pop-options

let compat_ocomp_fst #g
  (#t1 #t2:qType) #preP
  (fs_e12:fs_ocomp g (t1 ^* t2) preP)
  (e12:exp)
  : Lemma
    (requires fs_e12 ⊑ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures fs_ocomp_fmap fs_e12 fst ⊑ (EFst e12))
  =
  lem_fv_in_env_fst g e12;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(≍) h` s /\ (spec_env_bind' #g #(t1 ^* t2) preP (fun x -> spec_env_return_comp #g #t1 (io_return (fst #(fs_val t1) #(fs_val t2) x)))) fsG) ==> t1 ⫃ (h, (fs_ocomp_fmap #g #(t1 ^* t2) #t1 fs_e12 fst) fsG, gsubst s (EFst e12)) with begin
    let e = EFst (gsubst s e12) in
    assert (gsubst s (EFst e12) == e);
    let EFst e12 = e in
    introduce (fsG `(≍) h` s /\ (spec_env_bind' #g #(t1 ^* t2) preP (fun x -> spec_env_return_comp #g #t1 (io_return (fst #(fs_val t1) #(fs_val t2) x)))) fsG) ==> t1 ⫃ (h, (fs_ocomp_fmap #g #(t1 ^* t2) #t1 fs_e12 fst) fsG, e) with _. begin
      assert (preP fsG);
      let fs_e12' () : Pure (fs_comp (t1 ^* t2)) (requires preP fsG) (ensures (fun _ -> True)) = fs_e12 fsG in
      let fs_e = fs_comp_bind #(t1 ^* t2) #t1 (fs_e12' ()) (fun e12' -> return (fst #(fs_val t1) #(fs_val t2) e12')) in
      assert (fs_e == (fs_ocomp_fmap #g #(t1 ^* t2) #t1 fs_e12 fst) fsG) by (
        norm [delta_only [`%fs_ocomp_fmap;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val]];
        simplify_stack_ops ();
        trefl ());
      lem_shift_type_value_environments h fsG s;
      introduce forall lt (fs_r:fs_val t1). fs_beh fs_e h lt fs_r ==> exists e'. t1 ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce fs_beh fs_e h lt fs_r ==> exists e'. t1 ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          helper_compat_ocomp_fmap_fst_steps h lt t1 t2 (fs_e12' ()) fs_r e12
        end
      end
    end
  end;
  assert (fs_ocomp_fmap #g #(t1 ^* t2) #t1 fs_e12 fst ⊑ (EFst e12))
    by (FStar.Tactics.norm [delta_only [`%subset_ocomp]];
        FStar.Tactics.smt ())
        
let compat_ocomp_snd #g (#t1 #t2:qType) #preP (fs_e12:fs_ocomp g (t1 ^* t2) preP) (e12:exp)
  : Lemma
    (requires fs_e12 ⊑ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures fs_ocomp_fmap fs_e12 snd ⊑ (ESnd e12)) =
  lem_fv_in_env_snd g e12;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(≍) h` s /\ (spec_env_bind' #g #(t1 ^* t2) preP (fun x -> spec_env_return_comp #g #t2 (io_return (snd #(fs_val t1) #(fs_val t2) x)))) fsG) ==> t2 ⫃ (h, (fs_ocomp_fmap #g #(t1 ^* t2) #t2 fs_e12 snd) fsG, gsubst s (ESnd e12)) with begin
    let e = ESnd (gsubst s e12) in
    assert (gsubst s (ESnd e12) == e);
    let ESnd e12 = e in
    introduce (fsG `(≍) h` s /\ (spec_env_bind' #g #(t1 ^* t2) preP (fun x -> spec_env_return_comp #g #t2 (io_return (snd #(fs_val t1) #(fs_val t2) x)))) fsG) ==> t2 ⫃ (h, (fs_ocomp_fmap #g #(t1 ^* t2) #t2 fs_e12 snd) fsG, e) with _. begin
      assert (preP fsG);
      let fs_e12' () : Pure (fs_comp (t1 ^* t2)) (requires preP fsG) (ensures (fun _ -> True)) = fs_e12 fsG in
      let fs_e = fs_comp_bind #(t1 ^* t2) #t2 (fs_e12' ()) (fun v -> return (snd #(fs_val t1) #(fs_val t2) v)) in
      assert (fs_e == (fs_ocomp_fmap #g #(t1 ^* t2) #t2 fs_e12 snd) fsG) by (
        norm [delta_only [`%fs_ocomp_fmap;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val]];
        simplify_stack_ops ();
        trefl ());
      lem_shift_type_value_environments h fsG s;
      introduce forall lt (fs_r:fs_val t2). fs_beh fs_e h lt fs_r ==> exists e'. t2 ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce fs_beh fs_e h lt fs_r ==> exists e'. t2 ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          helper_compat_ocomp_fmap_snd_steps h lt t1 t2 (fs_e12' ()) fs_r e12
        end
      end
    end
  end;
  assert (fs_ocomp_fmap #g #(t1 ^* t2) #t2 fs_e12 snd ⊑ (ESnd e12))
    by (FStar.Tactics.norm [delta_only [`%subset_ocomp]];
        FStar.Tactics.smt ())

#push-options "--z3rlimit 120 --fuel 2 --ifuel 2 --split_queries always"
let compat_ocomp_case #g (#a #b #c:qType) #preCond
  (fs_cond:fs_ocomp g (a ^+ b) preCond)
  (#preInlc:spec_env (extend a g))
  (fs_inlc:fs_ocomp (extend a g) c preInlc)
  (#preInrc:spec_env (extend b g))
  (fs_inrc:fs_ocomp (extend b g) c preInrc)
  (cond inlc inrc:exp)
  : Lemma
    (requires fs_cond ⊑ cond /\ fs_inlc ⊑ inlc /\ fs_inrc ⊑ inrc)
    (ensures (fs_ocomp_case fs_cond fs_inlc fs_inrc) ⊑ (ECase cond inlc inrc)) =
  lem_fv_in_env_case g a b cond inlc inrc;
  lem_fv_in_env_lam g a inlc;
  lem_fv_in_env_lam g b inrc;
  compat_ocomp_lambda fs_inlc inlc;
  compat_ocomp_lambda fs_inrc inrc;
  compat_oval_lambda_ocomp fs_inlc inlc;
  compat_oval_lambda_ocomp fs_inrc inrc;
  introduce forall b' (s:gsub g b') fsG h.
    (fsG `(≍) h` s /\
     (spec_env_bind' #g #(a ^+ b) preCond
        (fun cond' -> fun fsG -> match cond' with
                             | Inl x -> preInlc (stack fsG x)
                             | Inr x -> preInrc (stack fsG x))) fsG) ==>
    c ⫃ (h, fs_ocomp_case fs_cond fs_inlc fs_inrc fsG, gsubst s (ECase cond inlc inrc))
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
      introduce (fsG `(≍) h` s /\
        (spec_env_bind' #g #(a ^+ b) preCond
          (fun cond' -> fun fsG -> match cond' with
                             | Inl x -> preInlc (stack fsG x)
                             | Inr x -> preInrc (stack fsG x))) fsG) ==>
        c ⫃ (h, fs_e, e) with _. begin
        lem_shift_type_value_environments h fsG s;
        introduce forall lt (fs_r:fs_val c). fs_beh fs_e h lt fs_r ==> exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
          introduce fs_beh fs_e h lt fs_r ==> exists e'. c ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
            helper_compat_ocomp_case_steps h lt a b c (fs_sc ()) fs_il fs_ir fs_r e_sc e_il e_ir
          end
        end
      end
    end
  end
#pop-options

let compat_ocomp_inl #g (t1 t2:qType) #preP (fs_e:fs_ocomp g t1 preP) (e:exp)
  : Lemma
    (requires fs_e ⊑ e)
    (ensures fs_ocomp_fmap #g #t1 #(t1 ^+ t2) fs_e Inl ⊑ (EInl e))
  =
  lem_fv_in_env_inl g e;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(≍) h` s /\ (spec_env_bind' #g #t1 preP (fun x -> spec_env_return_comp #g #(t1 ^+ t2) (io_return (Inl x)))) fsG) ==> (t1 ^+ t2) ⫃ (h, (fs_ocomp_fmap #g #t1 #(t1 ^+ t2) fs_e Inl) fsG, gsubst s (EInl e)) with begin
    let ex = EInl (gsubst s e) in
    assert (gsubst s (EInl e) == ex);
    let EInl e = ex in
    introduce (fsG `(≍) h` s /\ (spec_env_bind' #g #t1 preP (fun x -> spec_env_return_comp #g #(t1 ^+ t2) (io_return (Inl x)))) fsG) ==> (t1 ^+ t2) ⫃ (h, (fs_ocomp_fmap #g #t1 #(t1 ^+ t2) fs_e Inl) fsG, ex) with _. begin
      assert (preP fsG);
      let fs_e' () : Pure (fs_comp t1) (requires preP fsG) (ensures (fun _ -> True)) = fs_e fsG in
      let fs_ex = fs_comp_bind #t1 #(t1 ^+ t2) (fs_e' ()) (fun v -> return (Inl #(fs_val t1) #(fs_val t2) v)) in
      assert (fs_ex == (fs_ocomp_fmap #g #t1 #(t1 ^+ t2) fs_e Inl) fsG) by (
        norm [delta_only [`%fs_ocomp_fmap;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val]];
        simplify_stack_ops ();
        trefl ());
      lem_shift_type_value_environments h fsG s;
      introduce forall lt (fs_r:fs_val (t1 ^+ t2)). fs_beh fs_ex h lt fs_r ==> exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh ex e' h lt with begin
        introduce fs_beh fs_ex h lt fs_r ==> exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh ex e' h lt with _. begin
          helper_compat_ocomp_fmap_inl_steps h lt t1 t2 (fs_e' ()) fs_r e
        end
      end
    end
  end;
  assert (fs_ocomp_fmap #g #t1 #(t1 ^+ t2) fs_e Inl ⊑ (EInl e))
    by (FStar.Tactics.norm [delta_only [`%subset_ocomp]];
        FStar.Tactics.smt ())

let compat_ocomp_inr #g (t1 t2:qType) #preP (fs_e:fs_ocomp g t2 preP) (e:exp)
  : Lemma
    (requires fs_e ⊑ e)
    (ensures fs_ocomp_fmap #g #t2 #(t1 ^+ t2) fs_e Inr ⊑ (EInr e))
  =
  lem_fv_in_env_inr g e;
  introduce forall b' (s:gsub g b') fsG h. (fsG `(≍) h` s /\ (spec_env_bind' #g #t2 preP (fun x -> spec_env_return_comp #g #(t1 ^+ t2) (io_return (Inr x)))) fsG) ==> (t1 ^+ t2) ⫃ (h, (fs_ocomp_fmap #g #t2 #(t1 ^+ t2) fs_e Inr) fsG, gsubst s (EInr e)) with begin
    let ex = EInr (gsubst s e) in
    assert (gsubst s (EInr e) == ex);
    let EInr e = ex in
    introduce (fsG `(≍) h` s /\ (spec_env_bind' #g #t2 preP (fun x -> spec_env_return_comp #g #(t1 ^+ t2) (io_return (Inr x)))) fsG) ==> (t1 ^+ t2) ⫃ (h, (fs_ocomp_fmap #g #t2 #(t1 ^+ t2) fs_e Inr) fsG, ex) with _. begin
      assert (preP fsG);
      let fs_e' () : Pure (fs_comp t2) (requires preP fsG) (ensures (fun _ -> True)) = fs_e fsG in
      let fs_ex = fs_comp_bind #t2 #(t1 ^+ t2) (fs_e' ()) (fun v -> return (Inr #(fs_val t1) #(fs_val t2) v)) in
      assert (fs_ex == (fs_ocomp_fmap #g #t2 #(t1 ^+ t2) fs_e Inr) fsG) by (
        norm [delta_only [`%fs_ocomp_fmap;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return_val]];
        simplify_stack_ops ();
        trefl ());
      lem_shift_type_value_environments h fsG s;
      introduce forall lt (fs_r:fs_val (t1 ^+ t2)). fs_beh fs_ex h lt fs_r ==> exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh ex e' h lt with begin
        introduce fs_beh fs_ex h lt fs_r ==> exists e'. (t1 ^+ t2) ∈ (h++lt, fs_r, e') /\ e_beh ex e' h lt with _. begin
          helper_compat_ocomp_fmap_inr_steps h lt t1 t2 (fs_e' ()) fs_r e
        end
      end
    end
  end;
  assert (fs_ocomp_fmap #g #t2 #(t1 ^+ t2) fs_e Inr ⊑ (EInr e))
    by (FStar.Tactics.norm [delta_only [`%subset_ocomp]];
        FStar.Tactics.smt ())

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2 --split_queries always"
let compat_ocomp_call #g (op:io_ops) #preArgs (fs_arg:fs_ocomp g (q_io_args op) preArgs) (arg:exp)
  : Lemma
    (requires fs_arg ⊑ arg)
    (ensures fs_ocomp_call op fs_arg ⊑ ECall op arg)
  =
  lem_fv_in_env_call g op arg;
  assert (fs_val (q_io_args OOpen) == string)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res OOpen) == resexn file_descr)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_args ORead) == file_descr)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res ORead) == resexn string)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_args OWrite) == (file_descr * string))
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res OWrite) == resexn unit)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_args OClose) == file_descr)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  assert (fs_val (q_io_res OClose) == resexn unit)
    by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ());
  let pre : spec_env g = spec_env_bind' #g #(q_io_args op) preArgs (fun a -> spec_env_return_comp #g #(q_io_res op) (fs_comp_call_val op a)) in
  let fs_e : fs_ocomp g (q_io_res op) pre = fs_ocomp_call op fs_arg in
  introduce forall b' (s:gsub g b') (fsG:eval_env g) (h:history). (fsG `(≍) h` s /\ pre fsG) ==> (q_io_res op) ⫃ (h, fs_e fsG, gsubst s (ECall op arg)) with begin
    let e = ECall op (gsubst s arg) in
    assert (gsubst s (ECall op arg) == e);
    let ECall op arg = e in
    introduce (fsG `(≍) h` s /\ pre fsG) ==> (q_io_res op) ⫃ (h, fs_e fsG, e) with _. begin
      assert (preArgs fsG);
      let fs_arg' : fs_comp (q_io_args op) = fs_arg fsG in
      let fs_e_call = fs_comp_bind #(q_io_args op) #(q_io_res op) fs_arg' (fun arg' -> fs_comp_call_val op arg') in
      assume (fs_e fsG == fs_e_call); (*by (
        norm [delta_only [`%fs_ocomp_call;`%fs_ocomp_bind';`%fs_ocomp_bind;`%fs_ocomp_return;`%io_bind;`%io_return]];
        simplify_stack_ops ();
        compute ();
        trefl ());
      lem_shift_type_value_environments h fsG s;*)
      introduce forall lt (fs_r:fs_val (q_io_res op)). fs_beh fs_e_call h lt fs_r ==> exists e'. (q_io_res op) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce fs_beh fs_e_call h lt fs_r ==> exists e'. (q_io_res op) ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          helper_compat_ocomp_call_steps op h lt fs_arg' fs_e_call fs_r arg
        end
      end
    end
  end;
  assert (fs_ocomp_call op fs_arg ⊑ ECall op arg) by (
    FStar.Tactics.V1.norm [delta_only [`%(⊑); `%subset_ocomp]];
    FStar.Tactics.V1.smt ())
#pop-options

(** Auxiliary: under the [QRef] rule we only change the top-level
    refinement of the qType, leaving the underlying F* type and every
    nested type quotation untouched (cf. [QTypes.change_refinement]). The
    source-side value relation [(∈)] at ground types does not inspect the
    refinement (for [QBool] the positive branch's [ref true] is the one
    place where it does, and that follows from [ref v] with [v == true]);
    at aggregates [(∈)] recurses on the component qTypes, which
    [change_refinement] leaves alone; at arrows [change_refinement] is the
    identity. *)
let lem_ref_value_subset (a : qType) (ref : ref_type a -> Type0)
  (h : history) (v : fs_val a) (e : closed_exp)
  : Lemma
    (requires a ∈ (h, v, e) /\ ref v)
    (ensures (change_refinement a ref) ∈ (h, v, e))
  =
  match get_rel a with
  | QUnit -> ()
  | QBool -> ()
  | QFileDescriptor -> ()
  | QString -> ()
  | QPair _ _ -> ()
  | QSum _ _ -> ()
  | QArr _ _ -> ()
  | QArrIO _ _ -> ()

(** Pointwise lift to [⊆]. *)
let lem_ref_pointwise_subset (a : qType) (ref : ref_type a -> Type0)
  (h : history) (v : fs_val a) (e : closed_exp)
  : Lemma
    (requires a ⊆ (h, v, e) /\ ref v)
    (ensures ((change_refinement a ref) ⊆ (h, v, e)))
  =
  eliminate exists (e':closed_exp). e_beh e e' h [] /\ a ∈ (h, v, e')
    returns (change_refinement a ref) ⊆ (h, v, e) with _. begin
    lem_ref_value_subset a ref h v e';
    assert ((change_refinement a ref) ∈ (h, v, e'))
  end

(** Compatibility lemma for [QRef]: refining a [fs_oval] by a new
    refinement [ref] that the underlying value satisfies preserves the
    source-subset-of-target relation, since [fs_oval_ref v ref] is the
    same function as [v] and [change_refinement] only touches the
    top-level refinement. *)
#push-options "--z3rlimit 30"
let compat_oval_ref #g (#a:qType) (#preV:spec_env g)
  (fs_v:fs_oval g a preV) (ref:ref_type a -> Type0) (e:exp)
  : Lemma
    (requires (fs_v ⊏ e))
    (ensures (fs_oval_ref fs_v ref ⊏ e))
  =
  assert (fv_in_env g e);
  assert_norm (subset_oval (change_refinement a ref) (fs_oval_ref fs_v ref) e ==
    (fv_in_env g e /\
     (forall bo (s:gsub g bo) (fsG:eval_env g) (h:history).
        (fsG `(≍) h` s /\ (spec_env_ref fs_v ref) fsG) ==>
          (change_refinement a ref) ⊆ (h, (fs_oval_ref fs_v ref) fsG, gsubst s e))));
  introduce forall bo (s:gsub g bo) (fsG:eval_env g) (h:history).
    (fsG `(≍) h` s /\ (spec_env_ref fs_v ref) fsG) ==>
      (change_refinement a ref) ⊆ (h, (fs_oval_ref fs_v ref) fsG, gsubst s e)
  with begin
    introduce (fsG `(≍) h` s /\ (spec_env_ref fs_v ref) fsG) ==>
              (change_refinement a ref) ⊆ (h, (fs_oval_ref fs_v ref) fsG, gsubst s e) with _. begin
      assert (preV fsG);
      assert (ref (fs_v fsG));
      assert (a ⊆ (h, fs_v fsG, gsubst s e));
      lem_ref_pointwise_subset a ref h (fs_v fsG) (gsubst s e);
      assert ((fs_oval_ref fs_v ref) fsG == fs_v fsG);
      assert ((change_refinement a ref) ⊆ (h, fs_v fsG, gsubst s e))
    end
  end
#pop-options
