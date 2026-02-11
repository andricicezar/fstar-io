module LogRelTargetSource.CompatibilityLemmas

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open QTyp
open IO
open Trace
open LogRelTargetSource

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
let rec shift_sub_equiv_sub_inc_no_rename #t #g
  (s':gsub (extend t g) false)
  (e:exp)
  (f:gsub g false{forall (x:var). (f x) == (s' (x+1))}) :
  Lemma (ensures subst s' (subst sub_inc e) == subst #false f e) =
  match e with
  | EUnit
  | ETrue
  | EFalse
  | EVar _
  | EFileDescr _ -> ()
  | ELam e1 -> begin
    subst_comp (sub_elam s') (sub_elam sub_inc) e1;
    introduce forall (x:var). (gsub_comp (sub_elam s') (sub_elam sub_inc)) x == (sub_elam f) x with begin
      ()
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam s') (sub_elam sub_inc)) (sub_elam f) e1
    end
  | EFst e1
  | ESnd e1
  | EInl e1
  | EInr e1
  | ERead e1
  | EOpen e1
  | EClose e1 -> shift_sub_equiv_sub_inc_no_rename #t #g s' e1 f
  | EApp e1 e2
  | EWrite e1 e2
  | EPair e1 e2 -> begin
    shift_sub_equiv_sub_inc_no_rename #t #g s' e1 f;
    shift_sub_equiv_sub_inc_no_rename #t #g s' e2 f
    end
  | EIf e1 e2 e3 -> begin
    shift_sub_equiv_sub_inc_no_rename #t #g s' e1 f;
    shift_sub_equiv_sub_inc_no_rename #t #g s' e2 f;
    shift_sub_equiv_sub_inc_no_rename #t #g s' e3 f
    end
  | ECase e1 e2 e3 -> begin
    shift_sub_equiv_sub_inc_no_rename #t #g s' e1 f;
    subst_comp (sub_elam s') (sub_elam sub_inc) e2;
    subst_comp (sub_elam s') (sub_elam sub_inc) e3;
    introduce forall (x:var). (gsub_comp (sub_elam s') (sub_elam sub_inc)) x == (sub_elam f) x with begin
      ()
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam s') (sub_elam sub_inc)) (sub_elam f) e2;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam s') (sub_elam sub_inc)) (sub_elam f) e3
    end

let rec shift_sub_equiv_sub_inc_rename #t
  (s':gsub (extend t empty) false)
  (e:exp)
  (f:gsub empty true{forall (x:var). (f x) == (s' (x+1))}) :
  Lemma (ensures subst s' (subst sub_inc e) == subst #true f e)
        (decreases e) =
  match e with
  | EUnit
  | ETrue
  | EFalse
  | EVar _
  | EFileDescr _ -> ()
  | ELam e1 -> begin
    subst_comp (sub_elam s') (sub_elam sub_inc) e1;
    introduce forall (x:var). (gsub_comp (sub_elam s') (sub_elam sub_inc)) x == (sub_elam f) x with begin
      ()
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam s') (sub_elam sub_inc)) (sub_elam f) e1
    end
  | EFst e1
  | ESnd e1
  | EInl e1
  | EInr e1
  | ERead e1
  | EOpen e1
  | EClose e1 -> shift_sub_equiv_sub_inc_rename #t s' e1 f
  | EApp e1 e2
  | EWrite e1 e2
  | EPair e1 e2 -> begin
    shift_sub_equiv_sub_inc_rename #t s' e1 f;
    shift_sub_equiv_sub_inc_rename #t s' e2 f
    end
  | EIf e1 e2 e3 -> begin
    shift_sub_equiv_sub_inc_rename #t s' e1 f;
    shift_sub_equiv_sub_inc_rename #t s' e2 f;
    shift_sub_equiv_sub_inc_rename #t s' e3 f
    end
  | ECase e1 e2 e3 -> begin
    shift_sub_equiv_sub_inc_rename #t s' e1 f;
    subst_comp (sub_elam s') (sub_elam sub_inc) e2;
    subst_comp (sub_elam s') (sub_elam sub_inc) e3;
    introduce forall (x:var). (gsub_comp (sub_elam s') (sub_elam sub_inc)) x == (sub_elam f) x with begin
      ()
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam s') (sub_elam sub_inc)) (sub_elam f) e2;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam s') (sub_elam sub_inc)) (sub_elam f) e3
    end

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
      eliminate exists (e1':closed_exp). e_beh e1 e1' h [] /\ (t1 ^-> t2) ∈ (h, fs_e1, e1')
      returns exists (e':closed_exp). e_beh e e' h [] /\ t2 ∈ (h, fs_e, e') with _. begin
      let ELam e11 = e1' in
      unfold_member_of_arrow t1 t2 h fs_e1 e11;
      assert (forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∈ (h++lt_v, fs_v, v) ==> t2 ⊆ (h++lt_v, fs_e1 fs_v, subst_beta v e11));
      lem_forall_values_are_values t1 h fs_e2;
      assert (exists (e2':closed_exp). e_beh e2 e2' h [] /\ t1 ∈ (h, fs_e2, e2'));
      eliminate exists (e2':closed_exp). e_beh e2 e2' h [] /\ t1 ∈ (h, fs_e2, e2')
      returns exists (e':closed_exp). e_beh e e' h [] /\ t2 ∈ (h, fs_e, e') with _. begin
      eliminate forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∈ (h++lt_v, fs_v, v) ==> t2 ⊆ (h++lt_v, fs_e1 fs_v, subst_beta v e11) with e2' fs_e2 [];
      assert (t2 ⊆ (h, fs_e, subst_beta e2' e11));
      eliminate exists (e':closed_exp). e_beh (subst_beta e2' e11) e' h [] /\ t2 ∈ (h, fs_e, e')
      returns exists (e':closed_exp). e_beh e e' h [] /\ t2 ∈ (h, fs_e, e') with _. begin
      FStar.Squash.bind_squash #(steps e1 (ELam e11) h []) () (fun sts1 ->
      FStar.Squash.bind_squash #(steps e2 e2' h []) () (fun sts2 ->
      FStar.Squash.bind_squash #(steps (subst_beta e2' e11) e' h []) () (fun sts3 ->
      construct_steps_eapp e1 e11 e2 e2' e' h [] [] [] sts1 sts2 sts3;
      assert (steps (EApp e1 e2) e' h [])
      )))
      end
      end
      end
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
      admit ()
    end
  end

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
      admit ()
    end
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
      admit ()
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
      admit ()
    end
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
      admit ()
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
      admit ()
    end
  end

#push-options "--z3rlimit 10000"
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
  introduce forall b (s:gsub g b) fsG h. fsG `(≍) h` s ==> t3 ⊆ (h,
    (match fs_case fsG with
    | Inl x -> fs_lc (stack fsG x)
    | Inr x -> fs_rc (stack fsG x)),
    gsubst s (ECase e_case e_lc e_rc)) with begin
    let fs_case = fs_case fsG in
    let fs_lc_lam : fs_oval g (t1 ^-> t3) = fun fsG x -> fs_lc (stack fsG x) in
    let fs_lc_lam = fs_lc_lam fsG in
    let fs_rc_lam : fs_oval g (t2 ^-> t3) = fun fsG x -> fs_rc (stack fsG x) in
    let fs_rc_lam = fs_rc_lam fsG in
    let fs_e = (match fs_case with
               | Inl x -> fs_lc_lam x
               | Inr x -> fs_rc_lam x) in
    let e_lc' = subst (sub_elam s) e_lc in
    let e_rc' = subst (sub_elam s) e_rc in
    assert (gsubst s (ELam e_lc) == ELam e_lc');
    assert (gsubst s (ELam e_rc) == ELam e_rc');
    let e = ECase (gsubst s e_case) e_lc' e_rc' in
    assert (gsubst s (ECase e_case e_lc e_rc) == e);
    let ECase e_case e_lc e_rc = e in
    introduce fsG `(≍) h` s ==> t3 ⊆ (h, fs_e, e) with _. begin
      admit ()
    end
  end
#pop-options

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
      admit ()
    end
  end

let equiv_oprod_bind #g (#a #b:qType) (fs_m:fs_oprod g a) (fs_k:fs_oprod (extend a g) b) (m k:exp)
  : Lemma
    (requires fs_m ⊑ m /\ fs_k ⊑ k)
    (ensures (fs_oprod_bind fs_m fs_k) ⊑ (EApp (ELam k) m)) =
  lem_fv_in_env_lam g a k;
  lem_fv_in_env_app g (ELam k) m;
  equiv_oval_lambda_oprod fs_k k;
  let fs_k' : fs_oval g (a ^->!@ b) = fun fsG x -> fs_k (stack fsG x) in
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> b ⫃ (h, io_bind (fs_m fsG) (fun x -> fs_k (stack fsG x)), gsubst s (EApp (ELam k) m)) with begin
    let fs_m = fs_m fsG in
    let fs_k' = fs_k' fsG in
    io_bind_equivalence (fun x -> fs_k (stack fsG x)) fs_k' fs_m;
    let fs_e = io_bind fs_m (fun x -> fs_k (stack fsG x)) in
    let fs_e' = io_bind fs_m fs_k' in
    let k' = subst (sub_elam s) k in
    assert (gsubst s (ELam k) == ELam k');
    let e = EApp (ELam k') (gsubst s m) in
    assert (gsubst s (EApp (ELam k) m) == e);
    let EApp (ELam k') m = e in
    introduce fsG `(≍) h` s ==> b ⫃ (h, fs_e, e) with _. begin
      admit ()
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
          eliminate exists (f':closed_exp). e_beh f f' h [] /\ (a ^->!@ b) ∈ (h, fs_f, f')
          returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          let ELam f1 = f' in
          unfold_member_of_io_arrow a b h fs_f f1;
          assert (forall (v:value) (fs_v:fs_val a) (lt_v:local_trace h). a ∈ (h++lt_v, fs_v, v) ==> b ⫃ (h++lt_v, fs_f fs_v, subst_beta v f1));
          lem_forall_values_are_values a h fs_x;
          eliminate exists (x':closed_exp). e_beh x x' h [] /\ a ∈ (h, fs_x, x')
          returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          eliminate forall (v:value) (fs_v:fs_val a) (lt_v:local_trace h). a ∈ (h++lt_v, fs_v, v) ==> b ⫃ (h++lt_v, fs_f fs_v, subst_beta v f1) with x' fs_x [];
          assert (b ⫃ (h, fs_e, subst_beta x' f1));
          eliminate forall (lt:local_trace h) (fs_r:get_Type b). fs_beh fs_e h lt fs_r ==> exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (subst_beta x' f1) e' h lt with lt fs_r;
          eliminate exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh (subst_beta x' f1) e' h lt
          returns exists e'. b ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          FStar.Squash.bind_squash #(steps f (ELam f1) h []) () (fun sts1 ->
          FStar.Squash.bind_squash #(steps x x' h []) () (fun sts2 ->
          FStar.Squash.bind_squash #(steps (subst_beta x' f1) e' h lt) () (fun sts3 ->
          construct_steps_eapp f f1 x x' e' h [] [] lt sts1 sts2 sts3;
          assert (steps (EApp f x) e' h lt))))
          end
          end
          end
        end
      end
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
      admit ()
    end
  end

#push-options "--z3rlimit 10000"
let equiv_oprod_case_oval #g (#a #b #c:qType) (fs_cond:fs_oval g (a ^+ b)) (fs_inlc:fs_oprod (extend a g) c) (fs_inrc:fs_oprod (extend b g) c) (cond inlc inrc:exp)
  : Lemma
    (requires fs_cond ⊏ cond /\ fs_inlc ⊑ inlc /\ fs_inrc ⊑ inrc)
    (ensures (fs_oprod_case_oval fs_cond fs_inlc fs_inrc) ⊑ (ECase cond inlc inrc)) =
  lem_fv_in_env_case g a b cond inlc inrc;
  lem_fv_in_env_lam g a inlc;
  lem_fv_in_env_lam g b inrc;
  equiv_oval_lambda_oprod fs_inlc inlc;
  equiv_oval_lambda_oprod fs_inrc inrc;
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> c ⫃ (h,
    (match fs_cond fsG with
    | Inl x -> fs_inlc (stack fsG x)
    | Inr x -> fs_inrc (stack fsG x)),
    gsubst s (ECase cond inlc inrc)) with begin
    let fs_cond = fs_cond fsG in
    let fs_inlc' : fs_oval g (a ^->!@ c) = fun fsG x -> fs_inlc (stack fsG x) in
    let fs_inlc' = fs_inlc' fsG in
    let fs_inrc' : fs_oval g (b ^->!@ c) = fun fsG x -> fs_inrc (stack fsG x) in
    let fs_inrc' = fs_inrc' fsG in
    let fs_e = (match fs_cond with
               | Inl x -> fs_inlc' x
               | Inr x -> fs_inrc' x) in
    let inlc' = subst (sub_elam s) inlc in
    let inrc' = subst (sub_elam s) inrc in
    assert (gsubst s (ELam inlc) == ELam inlc');
    assert (gsubst s (ELam inrc) == ELam inrc');
    let e = ECase (gsubst s cond) inlc' inrc' in
    assert (gsubst s (ECase cond inlc inrc) == e);
    let ECase cond inlc inrc = e in
    introduce fsG `(≍) h` s ==> c ⫃ (h, fs_e, e) with _. begin
      admit ()
    end
  end
#pop-options

let equiv_oprod_openfile_oval #g (fs_fnm:fs_oval g qBool) (fnm:exp)
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
      admit ()
    end
  end

let equiv_oprod_read_oval #g (fs_fd:fs_oval g qFileDescr) (fd:exp)
  : Lemma
    (requires fs_fd ⊏ fd)
    (ensures fs_oprod_read_oval fs_fd ⊑ ERead fd)
  =
  lem_fv_in_env_read g fd;
  introduce forall b (s:gsub g b) (fsG:eval_env g) (h:history). fsG `(≍) h` s ==> (qBool ^+ qUnit) ⫃ (h, read (fs_fd fsG), gsubst s (ERead fd)) with begin
    let fs_fd = fs_fd fsG in
    let fs_e = read fs_fd in
    let e = ERead (gsubst s fd) in
    assert (gsubst s (ERead fd) == e);
    let ERead fd = e in
    introduce fsG `(≍) h` s ==> (qBool ^+ qUnit) ⫃ (h, fs_e, e) with _. begin
      admit ()
    end
  end

let equiv_oprod_write_oval #g (fs_fd:fs_oval g qFileDescr) (fs_msg:fs_oval g qBool) (fd msg:exp)
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
      admit ()
    end
  end

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
      admit ()
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

let helper_equiv_oprod_if_steps_pre (g:typ_env) (e:closed_exp) (h:history) (lt:local_trace h) (t:qType) (fs_e1:fs_prod qBool) (fs_e2 fs_e3:fs_oprod g t) (fs_e:fs_prod t) (fs_r:fs_val t) (e1 e2 e3:closed_exp) (fsG:eval_env g) =
  (fs_e == (io_bind fs_e1 (fun x -> (if (hd (stack fsG x)) then (fs_e2 (tail (stack fsG x))) else (fs_e3 (tail (stack fsG x))))))) /\
  (e == (EIf e1 e2 e3)) /\
  (fs_beh fs_e h lt fs_r) /\
  (qBool ⫃ (h, fs_e1, e1)) /\
  (forall (lt:local_trace h). t ⫃ (h++lt, (fs_e2 fsG), e2)) /\
  (forall (lt:local_trace h). t ⫃ (h++lt, (fs_e3 fsG), e3))

#push-options "--split_queries always"
let helper_equiv_oprod_if_steps #g #e #h #lt #t #fs_e1 #fs_e2 #fs_e3 #fs_e #fs_r #e1 #e2 #e3 #fsG (sq:squash (helper_equiv_oprod_if_steps_pre g e h lt t fs_e1 fs_e2 fs_e3 fs_e fs_r e1 e2 e3 fsG)) : squash (exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt) =
  destruct_fs_beh fs_e1 (fun x -> (if (hd (stack fsG x)) then (fs_e2 (tail (stack fsG x))) else (fs_e3 (tail (stack fsG x))))) h lt fs_r;
  eliminate exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:fs_val qBool). 
  lt == (lt1@lt2) /\ fs_beh fs_e1 h lt1 fs_m /\ fs_beh ((fun x -> (if (hd (stack fsG x)) then (fs_e2 (tail (stack fsG x))) else (fs_e3 (tail (stack fsG x))))) fs_m) (h++lt1) lt2 fs_r
  returns exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
  assert (qBool ⫃ (h, fs_e1, e1));
  assume (forall (lt1:local_trace h) (fs_r1:get_Type qBool). fs_beh fs_e1 h lt1 fs_r1 ==> exists e1'. qBool ∈ (h++lt1, fs_r1, e1') /\ e_beh e1 e1' h lt1);
  eliminate forall (lt1:local_trace h) (fs_r1:get_Type qBool). fs_beh fs_e1 h lt1 fs_r1 ==> exists e1'. qBool ∈ (h++lt1, fs_r1, e1') /\ e_beh e1 e1' h lt1 with lt1 fs_m;
  assert (t ⫃ (h++lt1, (fs_e2 fsG), e2));
  assume (forall (lt2:local_trace (h++lt1)) (fs_r2:get_Type t). fs_beh (fs_e2 fsG) (h++lt1) lt2 fs_r2 ==> exists e'. t ∈ ((h++lt1)++lt2, fs_r2, e') /\ e_beh e2 e' (h++lt1) lt2);
  eliminate forall (lt2:local_trace (h++lt1)) (fs_r2:get_Type t). fs_beh (fs_e2 fsG) (h++lt1) lt2 fs_r2 ==> exists e'. t ∈ ((h++lt1)++lt2, fs_r2, e') /\ e_beh e2 e' (h++lt1) lt2 with lt2 fs_r;
  assert (t ⫃ (h++lt1, (fs_e3 fsG), e3));
  assume (forall (lt3:local_trace (h++lt1)) (fs_r3:get_Type t). fs_beh (fs_e3 fsG) (h++lt1) lt3 fs_r3 ==> exists e'. t ∈ ((h++lt1)++lt3, fs_r3, e') /\ e_beh e3 e' (h++lt1) lt3);
  eliminate forall (lt3:local_trace (h++lt1)) (fs_r3:get_Type t). fs_beh (fs_e3 fsG) (h++lt1) lt3 fs_r3 ==> exists e'. t ∈ ((h++lt1)++lt3, fs_r3, e') /\ e_beh e3 e' (h++lt1) lt3 with lt2 fs_r;
  eliminate exists e1'. qBool ∈ (h++lt1, fs_m, e1') /\ e_beh e1 e1' h lt1
  returns exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
  assert (fs_m == true \/ fs_m == false);
  introduce fs_m == true ==> exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
    eliminate exists e'. t ∈ ((h++lt1)++lt2, fs_r, e') /\ e_beh e2 e' (h++lt1) lt2
    returns exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
    FStar.Squash.bind_squash #(steps e1 e1' h lt1) () (fun sts1 ->
    FStar.Squash.bind_squash #(steps e2 e' (h++lt1) lt2) () (fun sts2 ->
    construct_steps_eif e1 e1' e2 e3 e' h lt1 lt2 sts1 sts2))
    end
  end;
  introduce fs_m == false ==> exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
    eliminate exists e'. t ∈ ((h++lt1)++lt2, fs_r, e') /\ e_beh e3 e' (h++lt1) lt2
    returns exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
    FStar.Squash.bind_squash #(steps e1 e1' h lt1) () (fun sts1 ->
    FStar.Squash.bind_squash #(steps e3 e' (h++lt1) lt2) () (fun sts3 ->
    construct_steps_eif e1 e1' e2 e3 e' h lt1 lt2 sts1 sts3))
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
  introduce forall b' (s:gsub g b') fsG h. fsG `(≍) h` s ==> t ⫃ (h, io_bind (fs_e1 fsG) (fun x -> (if (hd (stack fsG x)) then (fs_e2 (tail (stack fsG x))) else (fs_e3 (tail (stack fsG x))))), gsubst s (EIf e1 e2 e3)) with begin
  introduce _ ==> _ with _. begin
    let fs_e1 = fs_e1 fsG in
    let fs_e = io_bind fs_e1 (fun x -> (if (hd (stack fsG x)) then (fs_e2 (tail (stack fsG x))) else (fs_e3 (tail (stack fsG x))))) in
    let e = EIf (gsubst s e1) (gsubst s e2) (gsubst s e3) in
    assert (gsubst s (EIf e1 e2 e3) == e);
    let EIf e1 e2 e3 = e in
    introduce fsG `(≍) h` s ==> t ⫃ (h, fs_e, e) with _. begin
      introduce forall lt (fs_r:get_Type t). fs_beh fs_e h lt fs_r ==> exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with begin
        introduce fs_beh fs_e h lt fs_r ==> exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt with _. begin
          lem_shift_type_value_environments h fsG s;
          let steps_pre : squash (helper_equiv_oprod_if_steps_pre g e h lt t fs_e1 fs_e2 fs_e3 fs_e fs_r e1 e2 e3 fsG) = () in
          FStar.Squash.map_squash #_ #(squash (exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt)) steps_pre (fun steps_pre ->
          helper_equiv_oprod_if_steps #g #e #h #lt #t #fs_e1 #fs_e2 #fs_e3 #fs_e #fs_r #e1 #e2 #e3 #fsG steps_pre)
        end
      end
    end
  end
 end

let equiv_oprod_file_descr g fd : Lemma (fs_oprod_return_val g qFileDescr fd ⊑ EFileDescr fd) =
  equiv_oval_file_descr g fd;
  equiv_oprod_return (fs_oval_return g qFileDescr fd) (EFileDescr fd)

let equiv_oprod_var g (x:var{Some? (g x)}) : Lemma (fs_oprod_var g x ⊑ EVar x) =
  equiv_oval_var g x;
  equiv_oprod_return (fs_oval_var g x) (EVar x)

let equiv_oprod_app_steps_pre' (e e':closed_exp) (h:history) (lt:local_trace h) (a b:qType) (fs_x':(fs_val (a ^->!@ b)) -> fs_prod b) (fs_f:fs_prod (a ^->!@ b)) (fs_e':fs_prod b) (f x:exp) =
  (fs_e' == io_bind fs_f fs_x') /\
  (e == EApp f x) /\
  (e_beh e e' h lt) /\
  ((a ^->!@ b) ⫃ (h, fs_f, f))

let equiv_oprod_app #g (#a #b:qType) (fs_f:fs_oprod g (a ^->!@ b)) (fs_x:fs_oprod g a) (f x:exp)
  : Lemma
    (requires fs_f ⊑ f /\ fs_x ⊑ x)
    (ensures fs_oprod_app fs_f fs_x ⊑ EApp f x) =
  lem_fv_in_env_app g f x;
  admit ()

let equiv_oprod_lambda #g (#t1:qType) (#t2:qType)
  (fs_body:fs_oprod (extend t1 g) t2)
  (body:exp)
  : Lemma
    (requires fs_body ⊑ body)
    (ensures fs_oprod_lambda fs_body ⊑ (ELam body))
  =
  equiv_oval_lambda_oprod #g #t1 #t2 fs_body body;
  equiv_oprod_return (fs_oval_lambda_oprod fs_body) (ELam body)

let equiv_oprod_inl #g (t1 t2:qType) (fs_e:fs_oprod g t1) (e:exp)
  : Lemma
    (requires fs_e ⊑ e)
    (ensures fs_oprod_fmap #g #t1 #(t1 ^+ t2) fs_e Inl ⊑ (EInl e))
  = admit ()

let equiv_oprod_inr #g (t1 t2:qType) (fs_e:fs_oprod g t2) (e:exp)
  : Lemma
    (requires fs_e ⊑ e)
    (ensures fs_oprod_fmap #g #t2 #(t1 ^+ t2) fs_e Inr ⊑ (EInr e))
  =
  admit ()

let equiv_oprod_pair #g
  (#t1 #t2:qType)
  (fs_e1:fs_oprod g t1) (fs_e2:fs_oprod g t2)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊑ e1 /\ fs_e2 ⊑ e2)
    (ensures fs_oprod_pair fs_e1 fs_e2 ⊑ EPair e1 e2) =
  admit ()

let equiv_oprod_fst #g
  (#t1 #t2:qType)
  (fs_e12:fs_oprod g (t1 ^* t2))
  (e12:exp)
  : Lemma
    (requires fs_e12 ⊑ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures fs_oprod_fmap fs_e12 fst ⊑ (EFst e12))
  = admit ()

let equiv_oprod_snd #g (#t1 #t2:qType) (fs_e12:fs_oprod g (t1 ^* t2)) (e12:exp)
  : Lemma
    (requires fs_e12 ⊑ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures fs_oprod_fmap fs_e12 snd ⊑ (ESnd e12)) =
  admit ()

let equiv_oprod_case #g (#a #b #c:qType)
  (fs_cond:fs_oprod g (a ^+ b))
  (fs_inlc:fs_oprod (extend a g) c)
  (fs_inrc:fs_oprod (extend b g) c)
  (cond inlc inrc:exp)
  : Lemma
    (requires fs_cond ⊑ cond /\ fs_inlc ⊑ inlc /\ fs_inrc ⊑ inrc)
    (ensures (fs_oprod_case fs_cond fs_inlc fs_inrc) ⊑ (ECase cond inlc inrc)) =
  admit ()

let equiv_oprod_openfile #g (fs_fnm:fs_oprod g qBool) (fnm:exp)
  : Lemma
    (requires fs_fnm ⊑ fnm)
    (ensures fs_oprod_openfile fs_fnm ⊑ EOpen fnm)
  = admit ()

let equiv_oprod_read #g (fs_fd:fs_oprod g qFileDescr) (fd:exp)
  : Lemma
    (requires fs_fd ⊑ fd)
    (ensures fs_oprod_read fs_fd ⊑ ERead fd)
  = admit ()

let equiv_oprod_write #g (fs_fd:fs_oprod g qFileDescr) (fs_msg:fs_oprod g qBool) (fd msg:exp)
  : Lemma
    (requires fs_fd ⊑ fd /\ fs_msg ⊑ msg)
    (ensures fs_oprod_write fs_fd fs_msg ⊑ EWrite fd msg)
  = admit ()

let equiv_oprod_close #g (fs_fd:fs_oprod g qFileDescr) (fd:exp)
  : Lemma
    (requires fs_fd ⊑ fd)
    (ensures fs_oprod_close fs_fd ⊑ EClose fd)
  = admit ()
