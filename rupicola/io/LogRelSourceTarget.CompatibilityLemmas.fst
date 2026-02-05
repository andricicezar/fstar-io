module LogRelSourceTarget.CompatibilityLemmas

open Trace
open STLC
open QTyp
open IO
open LogRelSourceTarget


let equiv_oval_unit g : Lemma (fs_oval_return g qUnit () ⊐ EUnit) =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qUnit ⊇ (h, (), gsubst s EUnit) with begin
    introduce _ ==> _ with _. begin
      assert (qUnit ∋ (h, (), EUnit));
      lem_values_are_expressions qUnit h () EUnit
    end
  end

let equiv_oval_true g : Lemma (fs_oval_return g qBool true ⊐ ETrue) =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qBool ⊇ (h, true, gsubst s ETrue) with begin
    introduce _ ==> _ with _. begin
      assert (qBool ∋ (h, true, ETrue));
      lem_values_are_expressions qBool h true ETrue
    end
  end

let equiv_oval_false g : Lemma (fs_oval_return g qBool false ⊐ EFalse) =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qBool ⊇ (h, false, gsubst s EFalse) with begin
    introduce _ ==> _ with _. begin
      assert (qBool ∋ (h, false, EFalse));
      lem_values_are_expressions qBool h false EFalse
    end
  end

let equiv_oval_file_descr g fd : Lemma (fs_oval_return g qFileDescr fd ⊐ EFileDescr fd) =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qFileDescr ⊇ (h, fd, gsubst s (EFileDescr fd)) with begin
    introduce _ ==> _ with _. begin
      assert (qFileDescr ∋ (h, fd, (EFileDescr fd)));
      lem_values_are_expressions qFileDescr h fd (EFileDescr fd)
    end
  end

(** Used in backtranslation **)
let equiv_oval_var g (x:var{Some? (g x)}) : Lemma (fs_oval_var g x ⊐ EVar x) =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> Some?.v (g x) ⊇ (h, index fsG x, gsubst s (EVar x)) with begin
    introduce _ ==> _ with _. begin
      assert (Some?.v (g x) ∋ (h, index fsG x, s x));
      lem_values_are_expressions (Some?.v (g x)) h (index fsG x) (s x)
    end
  end

(** Used in compilation **)
let equiv_oval_var0 (g:typ_env) (t:qType) : Lemma (fs_oval_var0 g t ⊐ EVar 0) =
  introduce forall b (s:gsub (extend t g) b) fsG h. fsG `(∽) h` s ==>  t ⊇ (h, hd fsG, gsubst s (EVar 0)) with begin
    introduce _ ==> _ with _. begin
      index_0_hd fsG;
      assert (t ∋ (h, hd fsG, s 0));
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
      (requires (s ⊐ e))
      (ensures (fs_oval_varS t s ⊐ subst sub_inc e))
  =
  lem_fv_in_env_varS g t e;
  introduce forall b (s':gsub (extend t g) b) (fsG:eval_env (extend t g)) (h:history). fsG `(∽) h` s' ==> a ⊇ (h, s (tail fsG), gsubst s' (subst sub_inc e)) with begin
    introduce fsG `(∽) h` s' ==> a ⊇ (h, s (tail fsG), gsubst s' (subst sub_inc e)) with _. begin
      lem_index_tail fsG;
      let f : var -> exp = fun (y:var) -> s' (y+1) in
      introduce (forall (x:var{x>0}). EVar? (s' x)) ==> a ⊇ (h, s (tail fsG), gsubst s' (subst sub_inc e)) with _. begin
        eliminate forall b_ (s_:gsub g b_) (fsG_:eval_env g) (h_:history). fsG_ `(∽) h_` s_ ==> a ⊇ (h_, s fsG_, gsubst s_ e) with true f (tail fsG) h;
        shift_sub_equiv_sub_inc_rename #t s' e f
      end;
      introduce (~(forall (x:var{x>0}). EVar? (s' x))) ==> a ⊇ (h, s (tail fsG), gsubst s' (subst sub_inc e)) with _. begin
        eliminate forall b_ (s_:gsub g b_) (fsG_:eval_env g) (h_:history). fsG_ `(∽) h_` s_  ==> a ⊇ (h_, s fsG_, gsubst s_ e) with false f (tail fsG) h;
        shift_sub_equiv_sub_inc_no_rename #t #g s' e f
      end
    end
  end
#pop-options

let equiv_oval_lambda #g (#t1:qType) (#t2:qType) (fs_body:fs_oval (extend t1 g) t2) (body:exp) : Lemma
  (requires fs_body ⊐ body)
  (ensures (fs_oval_lambda fs_body ⊐ ELam body)) =
  lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  let f : fs_oval g (t1 ^-> t2) = fun fsG x -> fs_body (stack fsG x) in
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> (t1 ^-> t2) ⊇ (h, f fsG, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∋ (h++lt_v, fs_v, v) ==> t2 ⊇ (h++lt_v, f fsG fs_v, subst_beta v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fsG' = stack fsG fs_v in
          let h' = h++lt_v in
          eliminate forall b (s':gsub g' b) (fsG':eval_env g') h'. fsG' `(∽) h'` s' ==> t2 ⊇ (h', f (tail #t1 fsG') (hd #t1 #g fsG'), gsubst s' body)
            with false s' fsG' h';
          assert (fsG `(∽) h` s);
          assert (t1 ∋ (h++lt_v, fs_v, v));
          introduce forall (x:var). Some? (g x) ==> Some?.v (g x) ∋ (h++lt_v, index fsG x, s x) with begin
            introduce _ ==> _ with _. begin
              val_type_closed_under_history_extension (Some?.v (g x)) h (index fsG x) (s x)
            end
          end;
          assert (stack fsG fs_v `(∽) h'` gsub_extend s t1 v);
          assert (t2 ⊇ (h', f (tail fsG') (hd fsG'), (gsubst s' body)));
          assert (hd (stack fsG fs_v) == fs_v);
          assert (t2 ⊇ (h', f (tail fsG') fs_v, (gsubst s' body)));
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

let helper_equiv_oval_app_steps_pre (e e':closed_exp) (h:history) (lt:local_trace h) (t1 t2:qType) (fs_e1:get_Type (t1 ^-> t2)) (fs_e2:get_Type t1) (fs_e:get_Type t2) (e1 e2:closed_exp) =
  (fs_e == fs_e1 fs_e2) /\
  (e == EApp e1 e2) /\
  (e_beh e e' h lt) /\
  ((t1 ^-> t2) ⊇ (h, fs_e1, e1)) /\
  (forall (lt:local_trace h). t1 ⊇ (h++lt, fs_e2, e2))

let helper_equiv_oval_app_steps #e #e' #h #lt #t1 #t2 #fs_e1 #fs_e2 #fs_e #e1 #e2 (sq:squash (helper_equiv_oval_app_steps_pre e e' h lt t1 t2 fs_e1 fs_e2 fs_e e1 e2)) : squash (t2 ∋ (h, fs_e, e') /\ lt == []) =
  assert (forall e1' lt1. e_beh e1 e1' h lt1 ==> (ELam? e1' /\ is_closed e1'));
  FStar.Squash.bind_squash #(steps e e' h lt) () (fun sts1 ->
  let t1_typ = type_quotation_to_typ (get_rel t1) in
  let t2_typ = type_quotation_to_typ (get_rel t2) in
  let (e11, (| lt1, lt' |)) = destruct_steps_eapp_e1 e1 e2 e' h lt sts1 t1_typ t2_typ in
  lem_forall_values_are_values t1 (h++lt1) fs_e2;
  assert (forall e2' (lt2:local_trace (h++lt1)). e_beh e2 e2' (h++lt1) lt2 ==> is_value e2');
  FStar.Squash.bind_squash #(steps (EApp (ELam e11) e2) e' (h++lt1) lt') () (fun sts2 ->
  let (e2', (| lt2, lt'' |)) = destruct_steps_eapp_e2 e11 e2 e' (h++lt1) lt' sts2 in
  eliminate forall e1' lt1. e_beh e1 e1' h lt1 ==> ((t1 ^-> t2) ∋ (h, fs_e1, e1') /\ lt1 == []) with (ELam e11) lt1;
  lem_value_is_irred (ELam e11);
  eliminate forall e2' lt2. e_beh e2 e2' (h++lt1) lt2 ==> (t1 ∋ (h++lt1, fs_e2, e2') /\ lt2 == []) with e2' lt2;
  lem_value_is_irred e2';
  unfold_contains_arrow t1 t2 h fs_e1 e11;
  assert (t2 ⊇ (h, fs_e, subst_beta e2' e11));
  assert (t2 ∋ (h, fs_e, e'))))

let equiv_oval_app #g
  (#t1:qType) (#t2:qType)
  (fs_e1:fs_oval g (t1 ^-> t2)) (fs_e2:fs_oval g t1)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊐ e1 /\ fs_e2 ⊐ e2)
    (ensures fs_oval_app fs_e1 fs_e2 ⊐ EApp e1 e2) =
  lem_fv_in_env_app g e1 e2;
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> t2 ⊇ (h, (fs_e1 fsG) (fs_e2 fsG), gsubst s (EApp e1 e2)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e2 = fs_e2 fsG in
    let fs_e = fs_e1 fs_e2 in
    let e = EApp (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EApp e1 e2) == e);
    let EApp e1 e2 = e in
    introduce fsG `(∽) h` s ==> t2 ⊇ (h, fs_e, e) with _. begin
      introduce forall (e':closed_exp) lt. e_beh e e' h lt ==> (t2 ∋ (h, fs_e, e') /\ lt == []) with begin
        introduce e_beh e e' h lt ==> (t2 ∋ (h, fs_e, e') /\ lt == []) with _. begin
          lem_shift_type_value_environments h fsG s;
          let steps_pre : squash (helper_equiv_oval_app_steps_pre e e' h lt t1 t2 fs_e1 fs_e2 fs_e e1 e2) = () in
          FStar.Squash.map_squash #_ #(squash (t2 ∋ (h, fs_e, e') /\ lt == [])) steps_pre (fun steps_pre ->
          helper_equiv_oval_app_steps #e #e' #h #lt #t1 #t2 #fs_e1 #fs_e2 #fs_e #e1 #e2 steps_pre)
        end
      end
    end
  end

let helper_equiv_oval_if_steps_pre (e e':closed_exp) (h:history) (lt:local_trace h) (t:qType) (fs_e1:bool) (fs_e2 fs_e3 fs_e:get_Type t) (e1:closed_exp) (e2:closed_exp) (e3:closed_exp) =
  (fs_e == (if fs_e1 then fs_e2 else fs_e3)) /\
  (e == (EIf e1 e2 e3)) /\
  (steps (EIf e1 e2 e3) e' h lt) /\
  (indexed_irred e' (h++lt)) /\
  (qBool ⊇ (h, fs_e1, e1)) /\
  (t ⊇ (h, fs_e2, e2)) /\
  (t ⊇ (h, fs_e3, e3))

let helper_equiv_oval_if_steps #e #e' #h #lt #t #fs_e1 #fs_e2 #fs_e3 #fs_e #e1 #e2 #e3 (sq:squash (helper_equiv_oval_if_steps_pre e e' h lt t fs_e1 fs_e2 fs_e3 fs_e e1 e2 e3)) : squash (t ∋ (h, fs_e, e') /\ lt == []) =
  assert (forall e1' lt1. e_beh e1 e1' h lt1 ==> (ETrue? e1' \/ EFalse? e1'));
  FStar.Squash.bind_squash #(steps e e' h lt) () (fun sts ->
  let (e1', (| lt1, (lt2, lt3) |)) = destruct_steps_eif e1 e2 e3 e' h lt sts in
  assert (qBool ∋ (h, fs_e1, e1') /\ lt1 == []);
  introduce ETrue? e1' ==> (t ∋ (h, fs_e, e') /\ lt == []) with _. begin
    assert (t ∋ (h, fs_e2, e') /\ lt2 == [])
  end;
  introduce EFalse? e1' ==> (t ∋ (h, fs_e, e') /\ lt == []) with _. begin
    assert (t ∋ (h, fs_e3, e') /\ lt3 == [])
  end)

let equiv_oval_if #g
  (#t:qType)
  (fs_e1:fs_oval g qBool) (fs_e2:fs_oval g t) (fs_e3:fs_oval g t)
  (e1:exp) (e2:exp) (e3:exp)
  : Lemma
    (requires fs_e1 ⊐ e1 /\ fs_e2 ⊐ e2 /\ fs_e3 ⊐ e3)
    (ensures fs_oval_if fs_e1 fs_e2 fs_e3 ⊐ EIf e1 e2 e3) =
  lem_fv_in_env_if g e1 e2 e3;
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> t ⊇ (h, (if fs_e1 fsG then fs_e2 fsG else fs_e3 fsG), gsubst s (EIf e1 e2 e3)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e2 = fs_e2 fsG in
    let fs_e3 = fs_e3 fsG in
    let fs_e = if fs_e1 then fs_e2 else fs_e3 in
    let e = EIf (gsubst s e1) (gsubst s e2) (gsubst s e3) in
    assert (gsubst s (EIf e1 e2 e3) == e);
    let EIf e1 e2 e3 = e in
    introduce fsG `(∽) h` s ==> t ⊇ (h, fs_e, e) with _. begin
      introduce forall (e':closed_exp) lt. e_beh e e' h lt ==> (t ∋ (h, fs_e, e') /\ lt == []) with begin
        introduce e_beh e e' h lt ==> (t ∋ (h, fs_e, e') /\ lt == []) with _. begin
          let steps_pre : squash (helper_equiv_oval_if_steps_pre e e' h lt t fs_e1 fs_e2 fs_e3 fs_e e1 e2 e3) = () in
          FStar.Squash.map_squash #_ #(squash (t ∋ (h, fs_e, e') /\ lt == [])) steps_pre (fun steps_pre ->
              helper_equiv_oval_if_steps #e #e' #h #lt #t #fs_e1 #fs_e2 #fs_e3 #fs_e #e1 #e2 #e3 steps_pre)
        end
      end
    end
  end

let helper_equiv_oval_pair_steps_pre (e e':closed_exp) (h:history) (lt:local_trace h) (t1 t2:qType) (fs_e1:get_Type t1) (fs_e2:get_Type t2) (fs_e:get_Type (t1 ^* t2)) (e1 e2:closed_exp) =
  (fs_e == (fs_e1, fs_e2)) /\
  (e == EPair e1 e2) /\
  (e_beh e e' h lt) /\
  (t1 ⊇ (h, fs_e1, e1)) /\
  (forall (lt:local_trace h). t2 ⊇ (h++lt, fs_e2, e2))

let helper_equiv_oval_pair_steps #e #e' #h #lt #t1 #t2 #fs_e1 #fs_e2 #fs_e #e1 #e2 (sq:squash (helper_equiv_oval_pair_steps_pre e e' h lt t1 t2 fs_e1 fs_e2 fs_e e1 e2)) : squash ((t1 ^* t2) ∋ (h, fs_e, e') /\ lt == []) =
  lem_forall_values_are_values t1 h fs_e1;
  assert (forall e1' lt1. e_beh e1 e1' h lt1 ==> is_value e1');
  FStar.Squash.bind_squash #(steps e e' h lt) () (fun steps_e_e' ->
  let (e1', (| lt1, lt' |)) = destruct_steps_epair_e1 e1 e2 e' h lt steps_e_e' in
  lem_forall_values_are_values t2 (h++lt1) fs_e2;
  assert (forall e2' lt2. e_beh e2 e2' (h++lt1) lt2 ==> is_value e2');
  FStar.Squash.bind_squash #(steps (EPair e1' e2) e' (h++lt1) lt') () (fun sts1 ->
  let (e2', (| lt2, lt'' |)) = destruct_steps_epair_e2 e1' e2 e' (h++lt1) lt' sts1 in
  lem_value_is_irred e1';
  lem_value_is_irred e2';
  assert (t1 ∋ (h, fs_e1, e1'));
  assert (t2 ∋ (h, fs_e2, e2'));
  assert ((t1 ^* t2) ∋ (h, fs_e, EPair e1' e2'));
  lem_values_are_expressions (t1 ^* t2) h fs_e (EPair e1' e2')))

let equiv_oval_pair #g
  (#t1 #t2:qType)
  (fs_e1:fs_oval g t1) (fs_e2:fs_oval g t2)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊐ e1 /\ fs_e2 ⊐ e2)
    (ensures fs_oval_pair fs_e1 fs_e2 ⊐ EPair e1 e2) =
  lem_fv_in_env_pair g e1 e2;
  let t = t1 ^* t2 in
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==>  t ⊇ (h, (fs_e1 fsG, fs_e2 fsG), gsubst s (EPair e1 e2)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e2 = fs_e2 fsG in
    let fs_e = (fs_e1, fs_e2) in
    let e = EPair (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EPair e1 e2) == e);
    let EPair e1 e2 = e in
    introduce fsG `(∽) h` s ==>  t ⊇ (h, fs_e, e) with _. begin
      introduce forall (e':closed_exp) lt. e_beh e e' h lt ==> (t ∋ (h, fs_e, e') /\ lt == []) with begin
        introduce _ ==> (t ∋ (h, fs_e, e') /\ lt == []) with _. begin
          lem_shift_type_value_environments h fsG s;
          let steps_pre : squash (helper_equiv_oval_pair_steps_pre e e' h lt t1 t2 fs_e1 fs_e2 fs_e e1 e2) = () in
          FStar.Squash.map_squash #_ #(squash ((t1 ^* t2) ∋ (h, fs_e, e') /\ lt == [])) steps_pre (fun steps_pre ->
          helper_equiv_oval_pair_steps #e #e' #h #lt #t1 #t2 #fs_e1 #fs_e2 #fs_e #e1 #e2 steps_pre)
        end
      end
    end
  end

let helper_equiv_oval_pair_fst_steps_pre (e e':closed_exp) (h:history) (lt:local_trace h) (t1 t2:qType) (fs_e12:get_Type (t1 ^* t2)) (fs_e:get_Type t1) (e12:closed_exp) =
  (fs_e == fst fs_e12) /\
  (e == EFst e12) /\
  (e_beh e e' h lt) /\
  ((t1 ^* t2) ⊇ (h, fs_e12, e12))

let helper_equiv_oval_pair_fst_steps #e #e' #h #lt #t1 #t2 #fs_e12 #fs_e #e12 (sq:squash (helper_equiv_oval_pair_fst_steps_pre e e' h lt t1 t2 fs_e12 fs_e e12)) : squash (t1 ∋ (h, fs_e, e') /\ lt == []) =
  lem_forall_values_are_values (t1 ^* t2) h fs_e12;
  assert (forall e12' lt12. e_beh e12 e12' h lt12 ==> (EPair? e12' /\ is_value e12'));
  FStar.Squash.bind_squash #(steps e e' h lt) () (fun steps_e_e' ->
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
  assert (t1 ∋ (h, fs_e, e1'));
  lem_destruct_steps_epair_fst e1' e2' e' h lt_f;
  assert (t1 ∋ (h, fs_e, e')))


let equiv_oval_pair_fst #g
  (#t1 #t2:qType)
  (fs_e12:fs_oval g (t1 ^* t2))
  (e12:exp)
  : Lemma
    (requires fs_e12 ⊐ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures fs_oval_fmap fs_e12 fst ⊐ (EFst e12)) =
  lem_fv_in_env_fst g e12;
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==>  t1 ⊇ (h, fst (fs_e12 fsG), gsubst s (EFst e12)) with begin
    let fs_e12 = fs_e12 fsG in
    let fs_e = fst fs_e12 in
    let e = EFst (gsubst s e12) in
    assert (gsubst s (EFst e12) == e);
    let EFst e12 = e in
    introduce fsG `(∽) h` s ==> t1 ⊇ (h, fs_e, e) with _. begin
      introduce forall (e':closed_exp) lt. e_beh e e' h lt ==> (t1 ∋ (h, fs_e, e') /\ lt == []) with begin
        introduce e_beh e e' h lt ==> (t1 ∋ (h, fs_e, e') /\ lt == []) with _. begin
          let steps_pre : squash (helper_equiv_oval_pair_fst_steps_pre e e' h lt t1 t2 fs_e12 fs_e e12) = () in
          FStar.Squash.map_squash #_ #(squash (t1 ∋ (h, fs_e, e') /\ lt == [])) steps_pre (fun steps_pre ->
          helper_equiv_oval_pair_fst_steps #e #e' #h #lt #t1 #t2 #fs_e12 #fs_e #e12 steps_pre)
        end
      end
    end
  end

let helper_equiv_oval_pair_snd_steps_pre (e e':closed_exp) (h:history) (lt:local_trace h) (t1 t2:qType) (fs_e12:get_Type (t1 ^* t2)) (fs_e:get_Type t2) (e12:closed_exp) =
  (fs_e == snd fs_e12) /\
  (e == ESnd e12) /\
  (e_beh e e' h lt) /\
  ((t1 ^* t2) ⊇ (h, fs_e12, e12))

let helper_equiv_oval_pair_snd_steps #e #e' #h #lt #t1 #t2 #fs_e12 #fs_e #e12 (sq:squash (helper_equiv_oval_pair_snd_steps_pre e e' h lt t1 t2 fs_e12 fs_e e12)) : squash (t2 ∋ (h, fs_e, e') /\ lt == []) =
  lem_forall_values_are_values (t1 ^* t2) h fs_e12;
  assert (forall e12' lt12. e_beh e12 e12' h lt12 ==> (EPair? e12' /\ is_value e12'));
  FStar.Squash.bind_squash #(steps e e' h lt) () (fun steps_e_e' ->
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
  assert (t2 ∋ (h, fs_e, e2'));
  lem_destruct_steps_epair_snd e1' e2' e' h lt_f;
  assert (t2 ∋ (h, fs_e, e')))

let equiv_oval_pair_snd #g (#t1 #t2:qType) (fs_e12:fs_oval g (t1 ^* t2)) (e12:exp)
  : Lemma
    (requires fs_e12 ⊐ e12)
    (ensures fs_oval_fmap fs_e12 snd ⊐ (ESnd e12)) =
  lem_fv_in_env_snd g e12;
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> t2 ⊇ (h, snd (fs_e12 fsG), gsubst s (ESnd e12)) with begin
    let fs_e12 = fs_e12 fsG in
    let fs_e = snd fs_e12 in
    let e = ESnd (gsubst s e12) in
    assert (gsubst s (ESnd e12) == e);
    let ESnd e12 = e in
    introduce fsG `(∽) h` s ==> t2 ⊇ (h, fs_e, e) with _. begin
      introduce forall (e':closed_exp) lt. e_beh e e' h lt ==> (t2 ∋ (h, fs_e, e') /\ lt == []) with begin
        introduce e_beh e e' h lt ==> (t2 ∋ (h, fs_e, e') /\ lt == []) with _. begin
        let steps_pre : squash (helper_equiv_oval_pair_snd_steps_pre e e' h lt t1 t2 fs_e12 fs_e e12) = () in
        FStar.Squash.map_squash #_ #(squash (t2 ∋ (h, fs_e, e') /\ lt == [])) steps_pre (fun steps_pre ->
        helper_equiv_oval_pair_snd_steps #e #e' #h #lt #t1 #t2 #fs_e12 #fs_e #e12 steps_pre)
        end
      end
    end
  end

let helper_equiv_oval_inl_steps_pre (ex ex':closed_exp) (h:history) (lt:local_trace h) (t1 t2:qType) (fs_e:get_Type t1) (fs_ex:get_Type (t1 ^+ t2)) (e:closed_exp) =
  (fs_ex == Inl #(get_Type t1) #(get_Type t2) fs_e) /\
  (ex == EInl e) /\
  (e_beh ex ex' h lt) /\
  (t1 ⊇ (h, fs_e, e))

let helper_equiv_oval_inl_steps #ex #ex' #h #lt #t1 #t2 #fs_e #fs_ex #e (sq:squash (helper_equiv_oval_inl_steps_pre ex ex' h lt t1 t2 fs_e fs_ex e)) : squash ((t1 ^+ t2) ∋ (h, fs_ex, ex') /\ lt == []) =
  lem_forall_values_are_values t1 h fs_e;
  assert (forall e' lt'. e_beh e e' h lt' ==> is_value e');
  FStar.Squash.bind_squash #(steps ex ex' h lt) () (fun steps_e_e' ->
  let (e', (| lt12, lt_f |)) = destruct_steps_einl e ex' h lt steps_e_e' in
  lem_value_is_irred e';
  lem_value_is_irred (EInl e');
  assert (t1 ∋ (h, fs_e, e') /\ lt12 == []);
  lem_destruct_steps_einl e' ex' h lt_f;
  assert ((t1 ^+ t2) ∋ (h, fs_ex, ex')))

let equiv_oval_inl #g (#t1 t2:qType) (fs_e:fs_oval g t1) (e:exp) : Lemma
  (requires fs_e ⊐ e)
  (ensures fs_oval_fmap #g #t1 #(t1 ^+ t2) fs_e Inl ⊐ (EInl e)) =
  lem_fv_in_env_inl g e;
  let t = t1 ^+ t2 in
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> (t1 ^+ t2) ⊇ (h, Inl (fs_e fsG), gsubst s (EInl e)) with begin
    let fs_e = fs_e fsG in
    let fs_ex = Inl #(get_Type t1) #(get_Type t2) fs_e in
    let ex = EInl (gsubst s e) in
    assert (gsubst s (EInl e) == ex);
    let EInl e = ex in
    introduce fsG `(∽) h` s ==> t ⊇ (h, fs_ex, ex) with _. begin
      introduce forall (ex':closed_exp) lt. e_beh ex ex' h lt ==> (t ∋ (h, fs_ex, ex') /\ lt == []) with begin
        introduce _ ==> (t ∋ (h, fs_ex, ex') /\ lt == []) with _. begin
        let steps_pre : squash (helper_equiv_oval_inl_steps_pre ex ex' h lt t1 t2 fs_e fs_ex e) = () in
        FStar.Squash.map_squash #_ #(squash (t ∋ (h, fs_ex, ex') /\ lt == [])) steps_pre (fun steps_pre ->
        helper_equiv_oval_inl_steps #ex #ex' #h #lt #t1 #t2 #fs_e #fs_ex #e steps_pre)
        end
      end
    end
  end

let helper_equiv_oval_inr_steps_pre (ex ex':closed_exp) (h:history) (lt:local_trace h) (t1 t2:qType) (fs_e:get_Type t2) (fs_ex:get_Type (t1 ^+ t2)) (e:closed_exp) =
  (fs_ex == Inr #(get_Type t1) #(get_Type t2) fs_e) /\
  (ex == EInr e) /\
  (e_beh ex ex' h lt) /\
  (t2 ⊇ (h, fs_e, e))

let helper_equiv_oval_inr_steps #ex #ex' #h #lt #t1 #t2 #fs_e #fs_ex #e (sq:squash (helper_equiv_oval_inr_steps_pre ex ex' h lt t1 t2 fs_e fs_ex e)) : squash ((t1 ^+ t2) ∋ (h, fs_ex, ex') /\ lt == []) =
  lem_forall_values_are_values t2 h fs_e;
  assert (forall e' lt'. e_beh e e' h lt' ==> is_value e');
  FStar.Squash.bind_squash #(steps ex ex' h lt) () (fun steps_e_e' ->
  let (e', (| lt12, lt_f |)) = destruct_steps_einr e ex' h lt steps_e_e' in
  lem_value_is_irred e';
  lem_value_is_irred (EInr e');
  assert (t2 ∋ (h, fs_e, e') /\ lt12 == []);
  lem_destruct_steps_einr e' ex' h lt_f;
  assert ((t1 ^+ t2) ∋ (h, fs_ex, ex')))

let equiv_oval_inr #g (t1 #t2:qType) (fs_e:fs_oval g t2) (e:exp) : Lemma
  (requires fs_e ⊐ e)
  (ensures fs_oval_fmap #g #t2 #(t1 ^+ t2) fs_e Inr ⊐ (EInr e)) =
  lem_fv_in_env_inr g e;
  let t = t1 ^+ t2 in
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> (t1 ^+ t2) ⊇ (h, Inr (fs_e fsG), gsubst s (EInr e)) with begin
    let fs_e = fs_e fsG in
    let fs_ex = Inr #(get_Type t1) #(get_Type t2) fs_e in
    let ex = EInr (gsubst s e) in
    assert (gsubst s (EInr e) == ex);
    let EInr e = ex in
    introduce fsG `(∽) h` s ==> t ⊇ (h, fs_ex, ex) with _. begin
      introduce forall (ex':closed_exp) lt. e_beh ex ex' h lt ==> (t ∋ (h, fs_ex, ex') /\ lt == []) with begin
        introduce _ ==> (t ∋ (h, fs_ex, ex') /\ lt == []) with _. begin
        let steps_pre : squash (helper_equiv_oval_inr_steps_pre ex ex' h lt t1 t2 fs_e fs_ex e) = () in
        FStar.Squash.map_squash #_ #(squash (t ∋ (h, fs_ex, ex') /\ lt == [])) steps_pre (fun steps_pre ->
        helper_equiv_oval_inr_steps #ex #ex' #h #lt #t1 #t2 #fs_e #fs_ex #e steps_pre)
        end
      end
    end
  end

let helper_equiv_oval_case_steps_pre (e e':closed_exp) (h:history) (lt:local_trace h) (t1 t2 t3:qType) (fs_case:get_Type (t1 ^+ t2)) (fs_lc_lam:get_Type (t1 ^-> t3)) (fs_rc_lam:get_Type (t2 ^-> t3)) (fs_e:get_Type t3) (e_case:closed_exp) (e_lc:exp{is_closed (ELam e_lc)}) (e_rc:exp{is_closed (ELam e_rc)}) =
  (fs_e == (match fs_case with
           | Inl x -> fs_lc_lam x
           | Inr x -> fs_rc_lam x)) /\
  (e == (ECase e_case e_lc e_rc)) /\
  (steps (ECase e_case e_lc e_rc) e' h lt) /\
  (indexed_irred e' (h++lt)) /\
  ((t1 ^+ t2) ⊇ (h, fs_case, e_case)) /\
  ((t1 ^-> t3) ⊇ (h, fs_lc_lam, ELam e_lc)) /\
  ((t2 ^-> t3) ⊇ (h, fs_rc_lam, ELam e_rc))

let helper_equiv_oval_case_steps #e #e' #h #lt #t1 #t2 #t3 #fs_case #fs_lc_lam #fs_rc_lam #fs_e #e_case #e_lc #e_rc (sq:squash (helper_equiv_oval_case_steps_pre e e' h lt t1 t2 t3 fs_case fs_lc_lam fs_rc_lam fs_e e_case e_lc e_rc)) : squash (t3 ∋ (h, fs_e, e') /\ lt == []) =
  lem_forall_values_are_values (t1 ^+ t2) h fs_case;
  assert (forall e_case' lt'. e_beh e_case e_case' h lt' ==> ((EInl? e_case' \/ EInr? e_case') /\ is_value e_case'));
  FStar.Squash.bind_squash #(steps e e' h lt) () (fun sts ->
    let t1_typ = type_quotation_to_typ (get_rel t1) in
    let t2_typ = type_quotation_to_typ (get_rel t2) in
    let (e_case', (| lt1, (lt2, lt3) |)) = destruct_steps_ecase e_case e_lc e_rc e' h lt sts t1_typ t2_typ in
    match e_case' with
    | EInl e_c' -> begin
      assert (steps (ELam e_lc) (ELam e_lc) h []);
      lem_value_is_irred (ELam e_lc);
      assert ((t1 ^-> t3) ∋ (h, fs_lc_lam, ELam e_lc));
      unfold_contains_arrow t1 t3 h fs_lc_lam e_lc;
      assert (t3 ⊇ (h, fs_e, subst_beta e_c' e_lc));
      assert (t3 ∋ (h, fs_e, e'))
      end
    | EInr e_c' -> begin
      assert (steps (ELam e_rc) (ELam e_rc) h []);
      lem_value_is_irred (ELam e_rc);
      assert ((t2 ^-> t3) ∋ (h, fs_rc_lam, ELam e_rc));
      unfold_contains_arrow t2 t3 h fs_rc_lam e_rc;
      assert (t3 ⊇ (h, fs_e, subst_beta e_c' e_rc));
      assert (t3 ∋ (h, fs_e, e'))
      end
    | _ -> false_elim ())

#push-options "--z3rlimit 10000"
let equiv_oval_case
  #g
  (#t1 #t2 #t3:qType)
  (fs_case:fs_oval g (t1 ^+ t2))
  (fs_lc:fs_oval (extend t1 g) t3)
  (fs_rc:fs_oval (extend t2 g) t3)
  (e_case e_lc e_rc:exp)
  : Lemma
    (requires fs_case ⊐ e_case /\ fs_lc ⊐ e_lc /\ fs_rc ⊐ e_rc)
    (ensures fs_oval_case fs_case fs_lc fs_rc ⊐ ECase e_case e_lc e_rc) =
  lem_fv_in_env_case g t1 t2 e_case e_lc e_rc;
  lem_fv_in_env_lam g t1 e_lc;
  lem_fv_in_env_lam g t2 e_rc;
  equiv_oval_lambda #g #t1 #t3 fs_lc e_lc;
  equiv_oval_lambda #g #t2 #t3 fs_rc e_rc;
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> t3 ⊇ (h,
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
    introduce fsG `(∽) h` s ==> t3 ⊇ (h, fs_e, e) with _. begin
      introduce forall (e':closed_exp) lt. e_beh e e' h lt ==> (t3 ∋ (h, fs_e, e') /\ lt == []) with begin
        introduce e_beh e e' h lt ==> (t3 ∋ (h, fs_e, e') /\ lt == []) with _. begin
          assert ((t1 ^-> t3) ⊇ (h, fs_lc_lam, ELam e_lc));
          assert ((t2 ^-> t3) ⊇ (h, fs_rc_lam, ELam e_rc));
          let steps_pre : squash (helper_equiv_oval_case_steps_pre e e' h lt t1 t2 t3 fs_case fs_lc_lam fs_rc_lam fs_e e_case e_lc e_rc) = () in
          FStar.Squash.map_squash #_ #(squash (t3 ∋ (h, fs_e, e') /\ lt == [])) steps_pre (fun steps_pre ->
            helper_equiv_oval_case_steps #e #e' #h #lt #t1 #t2 #t3 #fs_case #fs_lc_lam #fs_rc_lam #fs_e #e_case #e_lc #e_rc steps_pre)
        end
      end
    end
  end
#pop-options

let equiv_oval_lambda_oprod #g (#t1:qType) (#t2:qType) (fs_body:fs_oprod (extend t1 g) t2) (body:exp)
  : Lemma
    (requires fs_body ⊒ body)
    (ensures fs_oval_lambda_oprod fs_body ⊐ (ELam body)) =
  lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  let f : fs_oval g (t1 ^->!@ t2) = fun fsG x -> fs_body (stack fsG x) in
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> (t1 ^->!@ t2) ⊇ (h, f fsG, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∋ (h++lt_v, fs_v, v) ==> t2 ⫄ (h++lt_v, (f fsG) fs_v, subst_beta v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fsG' = stack fsG fs_v in
          let h' = h++lt_v in
          eliminate forall b (s':gsub g' b) (fsG':eval_env g') h'. fsG' `(∽) h'` s' ==> t2 ⫄ (h', f (tail #t1 fsG') (hd #t1 #g fsG'), gsubst s' body)
            with false s' fsG' h';
          assert (fsG `(∽) h` s);
          assert (t1 ∋ (h++lt_v, fs_v, v));
          introduce forall (x:var). Some? (g x) ==> Some?.v (g x) ∋ (h++lt_v, index fsG x, s x) with begin
            introduce _ ==> _ with _. begin
              val_type_closed_under_history_extension (Some?.v (g x)) h (index fsG x) (s x)
            end
          end;
          assert (stack fsG fs_v `(∽) h'` gsub_extend s t1 v);
          assert (t2 ⫄ (h', f (tail fsG') (hd fsG'), gsubst s' body));
          assert (hd (stack fsG fs_v) == fs_v);
          assert (t2 ⫄ (h', f (tail fsG') fs_v, gsubst s' body));
          assert (t2 ⫄ (h', f fsG fs_v, gsubst s' body));
          lem_substitution s t1 v body;
          assert (t2 ⫄ (h', f fsG fs_v, subst_beta v body'))
        end
      end;
      assert ((t1 ^->!@ t2) ∋ (h, f fsG, gsubst s (ELam body)));
      lem_values_are_expressions (t1 ^->!@ t2) h (f fsG) (gsubst s (ELam body));
      assert ((t1 ^->!@ t2) ⊇ (h, f fsG, gsubst s (ELam body)))
    end
  end

let equiv_oprod_return #g (#t:qType) (fs_x:fs_oval g t) (x:exp)
  : Lemma
    (requires fs_x ⊐ x)
    (ensures fs_oprod_return fs_x ⊒ x) =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> t ⫄ (h, return (fs_x fsG), gsubst s x) with begin
    introduce _ ==> _ with _. begin
      let fs_x = fs_x fsG in
      let fs_e = return fs_x in
      let e = gsubst s x in
      introduce forall (lt:local_trace h) (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e') /\ (fs_beh fs_e h lt fs_r)) with begin
        introduce e_beh e e' h lt ==> (exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
        assert (t ⊇ (h, fs_x, e));
        eliminate forall e' lt'. e_beh e e' h lt' ==> (t ∋ (h, fs_x, e') /\ lt' == []) with e' lt;
        assert (t ∋ (h++lt, fs_x, e'));
        lem_thetaP_return fs_x h
        end
      end
    end
  end

let helper_equiv_oprod_bind_steps_pre (e e':closed_exp) (h:history) (lt:local_trace h) (a:qType) (b:qType) (fs_k':(get_Type a) -> io (get_Type b)) (fs_m:io (get_Type a)) (fs_e':io (get_Type b)) (m:closed_exp) (k':exp) =
  (fs_e' == io_bind fs_m fs_k') /\
  (e == EApp (ELam k') m) /\
  (e_beh e e' h lt) /\
  ((a ^->!@ b) ⊇ (h, fs_k', (ELam k'))) /\
  (forall (lt:local_trace h). a ⫄ (h++lt, fs_m, m))

#push-options "--split_queries always --z3rlimit 32"
let helper_equiv_oprod_bind_steps #e #e' #h #lt #a #b #fs_k' #fs_m #fs_e' #m #k' (sq:squash (helper_equiv_oprod_bind_steps_pre e e' h lt a b fs_k' fs_m fs_e' m k')) : squash (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e' h lt fs_r) =
  assert (forall k_ lt1. e_beh (ELam k') k_ h lt1 ==> (ELam? k_ /\ is_closed k_));
  FStar.Squash.bind_squash #(steps e e' h lt) () (fun sts1 ->
  let a_typ = type_quotation_to_typ (get_rel a) in
  let b_typ = type_quotation_to_typ (get_rel b) in
  let (k1, (| lt1, lt' |)) = destruct_steps_eapp_e1 (ELam k') m e' h lt sts1 a_typ b_typ in
  lem_forall_values_are_values_prod a h;
  assert (forall m' (lt2:local_trace (h++lt1)). e_beh m m' (h++lt1) lt2 ==> is_value m');
  FStar.Squash.bind_squash #(steps (EApp (ELam k1) m) e' (h++lt1) lt') () (fun sts2 ->
  let (m', (| lt2, lt'' |)) = destruct_steps_eapp_e2 k1 m e' (h++lt1) lt' sts2 in
  eliminate forall e' lt. e_beh (ELam k') e' h lt ==> ((a ^->!@ b) ∋ (h, fs_k', e') /\ lt == []) with (ELam k1) lt1;
  lem_value_is_irred (ELam k1);
  eliminate forall m' lt2. e_beh m m' (h++lt1) lt2 ==> (exists (fs_r_m:get_Type a). a ∋ ((h++lt1)++lt2, fs_r_m, m') /\ fs_beh fs_m (h++lt1) lt2 fs_r_m) with m' lt2;
  lem_value_is_irred m';
  unfold_contains_io_arrow a b h fs_k' k1;
  eliminate exists (fs_r_m:get_Type a). a ∋ ((h++lt1)++lt2, fs_r_m, m') /\ fs_beh fs_m h lt2 fs_r_m
  returns exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e' h lt fs_r with _. begin
  eliminate exists (fs_r':get_Type b). b ∋ (((h++lt1)++lt2)++lt'', fs_r', e') /\ fs_beh (fs_k' fs_r_m) ((h++lt1)++lt2) lt'' fs_r'
  returns exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e' h lt fs_r with _. begin
  lem_thetaP_bind #(get_Type a) #(get_Type b) fs_m (h++lt1) lt2 fs_r_m fs_k' lt'' fs_r'
  end
  end))
#pop-options

let equiv_oprod_bind #g (#a #b:qType) (fs_m:fs_oprod g a) (fs_k:fs_oprod (extend a g) b) (m k:exp)
  : Lemma
    (requires fs_m ⊒ m /\ fs_k ⊒ k)
    (ensures (fs_oprod_bind fs_m fs_k) ⊒ (EApp (ELam k) m)) =
  lem_fv_in_env_lam g a k;
  lem_fv_in_env_app g (ELam k) m;
  equiv_oval_lambda_oprod fs_k k;
  let fs_k' : fs_oval g (a ^->!@ b) = fun fsG x -> fs_k (stack fsG x) in
  introduce forall b' (s:gsub g b') fsG h. fsG `(∽) h` s ==> b ⫄ (h, io_bind (fs_m fsG) (fun x -> fs_k (stack fsG x)), gsubst s (EApp (ELam k) m)) with begin
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
    introduce fsG `(∽) h` s ==> b ⫄ (h, fs_e, e) with _. begin
      introduce forall lt (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
        introduce e_beh e e' h lt ==> (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e' h lt fs_r) with _. begin
          lem_shift_type_value_environments h fsG s;
          let steps_pre : squash (helper_equiv_oprod_bind_steps_pre e e' h lt a b fs_k' fs_m fs_e' m k') = () in
          FStar.Squash.map_squash #_ #(squash (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e' h lt fs_r)) steps_pre (fun steps_pre ->
            helper_equiv_oprod_bind_steps #e #e' #h #lt #a #b #fs_k' #fs_m #fs_e' #m #k' steps_pre)
        end
      end
    end
  end

let helper_equiv_oprod_app_oval_oval_steps_pre (e e':closed_exp) (h:history) (lt:local_trace h) (a b:qType) (fs_f:get_Type (a ^->!@ b)) (fs_x:get_Type a) (fs_e:io (get_Type b)) (f x:closed_exp) =
  (fs_e == fs_f fs_x) /\
  (e == EApp f x) /\
  (e_beh e e' h lt) /\
  ((a ^->!@ b) ⊇ (h, fs_f, f)) /\
  (forall (lt:local_trace h). a ⊇ (h++lt, fs_x, x))

let helper_equiv_oprod_app_oval_oval_steps #e #e' #h #lt #a #b #fs_f #fs_x #fs_e #f #x (sq:squash (helper_equiv_oprod_app_oval_oval_steps_pre e e' h lt a b fs_f fs_x fs_e f x)) : squash (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) =
  assert (forall f' lt1. e_beh f f' h lt1 ==> (ELam? f' /\ is_closed f'));
  FStar.Squash.bind_squash #(steps e e' h lt) () (fun sts1 ->
  let a_typ = type_quotation_to_typ (get_rel a) in
  let b_typ = type_quotation_to_typ (get_rel b) in
  let (f1, (| lt1, lt' |)) = destruct_steps_eapp_e1 f x e' h lt sts1 a_typ b_typ in
  lem_forall_values_are_values a (h++lt1) fs_x;
  assert (forall x' (lt2:local_trace (h++lt1)). e_beh x x' (h++lt1) lt2 ==> is_value x');
  FStar.Squash.bind_squash #(steps (EApp (ELam f1) x) e' (h++lt1) lt') () (fun sts2 ->
  let (x', (| lt2, lt'' |)) = destruct_steps_eapp_e2 f1 x e' (h++lt1) lt' sts2 in
  eliminate forall f' lt1. e_beh f f' h lt1 ==> ((a ^->!@ b) ∋ (h, fs_f, f') /\ lt1 == []) with (ELam f1) lt1;
  lem_value_is_irred (ELam f1);
  eliminate forall x' lt2. e_beh x x' h lt2 ==> (a ∋ (h, fs_x, x') /\ lt2 == []) with x' lt2;
  lem_value_is_irred x';
  unfold_contains_io_arrow a b h fs_f f1;
  assert (b ⫄ (h, fs_e, subst_beta x' f1));
  assert (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r)))

let equiv_oprod_app_oval_oval #g (#a #b:qType) (fs_f:fs_oval g (a ^->!@ b)) (fs_x:fs_oval g a) (f x:exp)
  : Lemma
    (requires fs_f ⊐ f /\ fs_x ⊐ x)
    (ensures (fs_oprod_app_oval_oval fs_f fs_x) ⊒ (EApp f x)) =
  lem_fv_in_env_app g f x;
  introduce forall b' (s:gsub g b') fsG h. fsG `(∽) h` s ==> b ⫄ (h, (fs_f fsG) (fs_x fsG), gsubst s (EApp f x)) with begin
    let fs_f = fs_f fsG in
    let fs_x = fs_x fsG in
    let fs_e = fs_f fs_x in
    let e = EApp (gsubst s f) (gsubst s x) in
    assert (gsubst s (EApp f x) == e);
    let EApp f x = e in
    introduce fsG `(∽) h` s ==> b ⫄ (h, fs_e, e) with _. begin
      introduce forall lt (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:get_Type b). b  ∋ (h++lt, fs_r, e') /\ (fs_beh fs_e h lt fs_r)) with begin
        introduce _ ==> (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
        lem_shift_type_value_environments h fsG s;
        let steps_pre : squash (helper_equiv_oprod_app_oval_oval_steps_pre e e' h lt a b fs_f fs_x fs_e f x) = () in
        FStar.Squash.map_squash #_ #(squash (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r)) steps_pre (fun steps_pre ->
        helper_equiv_oprod_app_oval_oval_steps #e #e' #h #lt #a #b #fs_f #fs_x #fs_e #f #x steps_pre)
        end
      end
    end
  end

let helper_equiv_oprod_if_oval_steps_pre (ex ex':closed_exp) (h:history) (lt:local_trace h) (a:qType) (fs_c:bool) (fs_t fs_e fs_ex:fs_prod a) (c t e:closed_exp) =
  (fs_ex == (if fs_c then fs_t else fs_e)) /\
  (ex == (EIf c t e)) /\
  (e_beh ex ex' h lt) /\
  (qBool ⊇ (h, fs_c, c)) /\
  (a ⫄ (h, fs_t, t)) /\
  (a ⫄ (h, fs_e, e))

let helper_equiv_oprod_if_oval_steps #ex #ex' #h #lt #a #fs_c #fs_t #fs_e #fs_ex #c #t #e (sq:squash (helper_equiv_oprod_if_oval_steps_pre ex ex' h lt a fs_c fs_t fs_e fs_ex c t e)) : squash (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, ex') /\ fs_beh fs_ex h lt fs_r) =
  assert (forall c' lt'. e_beh c c' h lt' ==> (ETrue? c' \/ EFalse? c'));
  FStar.Squash.bind_squash #(steps ex ex' h lt) () (fun sts ->
  let (c', (| lt1, (lt2, lt3) |)) = destruct_steps_eif c t e ex' h lt sts in
  assert (qBool ∋ (h, fs_c, c') /\ lt1 == []);
  introduce ETrue? c' ==> (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, ex') /\ fs_beh fs_ex h lt fs_r) with _. begin
    assert (exists (fs_r:get_Type a). a ∋ (h++lt2, fs_r, ex') /\ fs_beh fs_t h lt2 fs_r)
  end;
  introduce EFalse? c' ==> (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, ex') /\ fs_beh fs_ex h lt fs_r) with _. begin
    assert (exists (fs_r:get_Type a). a ∋ (h++lt3, fs_r, ex') /\ fs_beh fs_e h lt3 fs_r)
  end)

let equiv_oprod_if_oval #g (#a:qType) (fs_c:fs_oval g qBool) (fs_t fs_e:fs_oprod g a) (c t e:exp)
  : Lemma
    (requires fs_c ⊐ c /\ fs_t ⊒ t /\ fs_e ⊒ e)
    (ensures (fs_oprod_if_oval fs_c fs_t fs_e) ⊒ (EIf c t e)) =
  lem_fv_in_env_if g c t e;
  introduce forall b' (s:gsub g b') fsG h. fsG `(∽) h` s ==> a ⫄ (h, (if (fs_c fsG) then (fs_t fsG) else (fs_e fsG)), gsubst s (EIf c t e)) with begin
    let fs_c = fs_c fsG in
    let fs_t = fs_t fsG in
    let fs_e = fs_e fsG in
    let fs_ex = if fs_c then fs_t else fs_e in
    let ex = EIf (gsubst s c) (gsubst s t) (gsubst s e) in
    assert (gsubst s (EIf c t e) == ex);
    let EIf c t e = ex in
    introduce fsG `(∽) h` s ==> a ⫄ (h, fs_ex, ex) with _. begin
      introduce forall lt (ex':closed_exp). e_beh ex ex' h lt ==> (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, ex') /\ fs_beh fs_ex h lt fs_r) with begin
        introduce e_beh ex ex' h lt ==> (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, ex') /\ fs_beh fs_ex h lt fs_r) with _. begin
          let steps_pre : squash (helper_equiv_oprod_if_oval_steps_pre ex ex' h lt a fs_c fs_t fs_e fs_ex c t e) = () in
          FStar.Squash.map_squash #_ #(squash (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, ex') /\ fs_beh fs_ex h lt fs_r)) steps_pre (fun steps_pre ->
            helper_equiv_oprod_if_oval_steps #ex #ex' #h #lt #a #fs_c #fs_t #fs_e #fs_ex #c #t #e steps_pre)
        end
      end
    end
  end

let helper_equiv_oprod_case_oval_steps_pre (e e':closed_exp) (h:history) (lt:local_trace h) (a b c:qType) (fs_cond:get_Type (a ^+ b)) (fs_inlc:get_Type (a ^->!@ c)) (fs_inrc:get_Type (b ^->!@ c)) (fs_e:fs_prod c) (cond:closed_exp) (inlc:exp{is_closed (ELam inlc)}) (inrc:exp{is_closed (ELam inrc)}) =
  (fs_e == (match fs_cond with
           | Inl x -> fs_inlc x
           | Inr x -> fs_inrc x)) /\
  (e == (ECase cond inlc inrc)) /\
  e_beh (ECase cond inlc inrc) e' h lt /\
  ((a ^+ b) ⊇ (h, fs_cond, cond)) /\
  ((a ^->!@ c) ⊇ (h, fs_inlc, ELam inlc)) /\
  ((b ^->!@ c) ⊇ (h, fs_inrc, ELam inrc))

let helper_equiv_oprod_case_oval_steps #e #e' #h #lt #a #b #c #fs_cond #fs_inlc #fs_inrc #fs_e #cond #inlc #inrc (sq:squash (helper_equiv_oprod_case_oval_steps_pre e e' h lt a b c fs_cond fs_inlc fs_inrc fs_e cond inlc inrc)) : squash (exists (fs_r:get_Type c). c ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) =
  lem_forall_values_are_values (a ^+ b) h fs_cond;
  assert (forall cond' lt'. e_beh cond cond' h lt' ==> ((EInl? cond' \/ EInr? cond') /\ is_value cond'));
  FStar.Squash.bind_squash #(steps e e' h lt) () (fun sts ->
    let a_typ = type_quotation_to_typ (get_rel a) in
    let b_typ = type_quotation_to_typ (get_rel b) in
    let (cond', (| lt1, (lt2, lt3) |)) = destruct_steps_ecase cond inlc inrc e' h lt sts a_typ b_typ in
    match cond' with
    | EInl c' -> begin
      assert (steps (ELam inlc) (ELam inlc) h []);
      lem_value_is_irred (ELam inlc);
      assert ((a ^->!@ c) ∋ (h, fs_inlc, ELam inlc));
      unfold_contains_io_arrow a c h fs_inlc inlc;
      assert (c ⫄ (h, fs_e, subst_beta c' inlc));
      assert (exists (fs_r:get_Type c). c ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r)
      end
    | EInr c' -> begin
      assert (steps (ELam inrc) (ELam inrc) h []);
      lem_value_is_irred (ELam inrc);
      assert ((b ^->!@ c) ∋ (h, fs_inrc, ELam inrc));
      unfold_contains_io_arrow b c h fs_inrc inrc;
      assert (c ⫄ (h, fs_e, subst_beta c' inrc));
      assert (exists (fs_r:get_Type c). c ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r)
      end
    | _ -> false_elim ()
  )

#push-options "--z3rlimit 10000"
let equiv_oprod_case_oval #g (#a #b #c:qType) (fs_cond:fs_oval g (a ^+ b)) (fs_inlc:fs_oprod (extend a g) c) (fs_inrc:fs_oprod (extend b g) c) (cond inlc inrc:exp)
  : Lemma
    (requires fs_cond ⊐ cond /\ fs_inlc ⊒ inlc /\ fs_inrc ⊒ inrc)
    (ensures (fs_oprod_case_oval fs_cond fs_inlc fs_inrc) ⊒ (ECase cond inlc inrc)) =
  lem_fv_in_env_case g a b cond inlc inrc;
  lem_fv_in_env_lam g a inlc;
  lem_fv_in_env_lam g b inrc;
  equiv_oval_lambda_oprod fs_inlc inlc;
  equiv_oval_lambda_oprod fs_inrc inrc;
  introduce forall b' (s:gsub g b') fsG h. fsG `(∽) h` s ==> c ⫄ (h,
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
    introduce fsG `(∽) h` s ==> c ⫄ (h, fs_e, e) with _. begin
      introduce forall lt (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:get_Type c). c ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
        introduce e_beh e e' h lt /\ indexed_irred e' (h++lt) ==> (exists (fs_r:get_Type c). c ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
          assert ((a ^->!@ c) ⊇ (h, fs_inlc', ELam inlc));
          assert ((b ^->!@ c) ⊇ (h, fs_inrc', ELam inrc));
          let steps_pre : squash (helper_equiv_oprod_case_oval_steps_pre e e' h lt a b c fs_cond fs_inlc' fs_inrc' fs_e cond inlc inrc) = () in
          FStar.Squash.map_squash #_ #(squash (exists (fs_r:get_Type c). c ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r)) steps_pre (fun steps_pre ->
            helper_equiv_oprod_case_oval_steps #e #e' #h #lt #a #b #c #fs_cond #fs_inlc' #fs_inrc' #fs_e #cond #inlc #inrc steps_pre)
        end
      end
    end
  end
#pop-options

let helper_equiv_oprod_openfile_oval_steps_pre (e e':closed_exp) (h:history) (lt:local_trace h) (fs_fnm:bool) (fs_e:io (get_Type (qFileDescr ^+ qUnit))) (fnm:closed_exp) =
  (fs_e == openfile fs_fnm) /\
  (e == EOpen fnm) /\
  (e_beh e e' h lt) /\
  (qBool ⊇ (h, fs_fnm, fnm))

let helper_equiv_oprod_openfile_oval_steps #e #e' #h #lt #fs_fnm #fs_e #fnm (sq:squash (helper_equiv_oprod_openfile_oval_steps_pre e e' h lt fs_fnm fs_e fnm)) : squash (exists (fs_r:get_Type (qFileDescr ^+ qUnit)). (qFileDescr ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) =
  lem_forall_values_are_values qBool h fs_fnm;
  FStar.Squash.bind_squash #(steps e e' h lt) () (fun steps_e_e' ->
  let (fnm', (| lt1, lt' |)) = destruct_steps_eopen_str fnm e' h lt steps_e_e' in
  FStar.Squash.bind_squash #(steps (EOpen fnm') e' (h++lt1) lt') () (fun sts1 ->
  let (e_r, (| lt2, (lt3, lt4) |)) = destruct_steps_eopen fnm' e' (h++lt1) lt' sts1 in
  assert (qBool ⊇ (h, fs_fnm, fnm));
  lem_value_is_irred fnm';
  match e_r with
  | EInl (EFileDescr fd) -> begin
    lem_value_is_irred (EFileDescr fd);
    lem_value_is_irred (EInl (EFileDescr fd));
    lem_destruct_steps_einl (EFileDescr fd) e' ((h++lt1)++lt2) lt3;
    assert ((qFileDescr ^+ qUnit) ∋ (h++lt, Inl fd, EInl (EFileDescr fd)));
    assert (lt == [EvOpen fs_fnm (Inl fd)]);
    lem_theta_open fs_fnm (Inl fd) h
    end
  | EInr EUnit -> begin
    lem_value_is_irred EUnit;
    lem_value_is_irred (EInr EUnit);
    lem_destruct_steps_einr EUnit e' ((h++lt1)++lt2) lt4;
    assert ((qFileDescr ^+ qUnit) ∋ (h++lt, Inr (), EInr EUnit));
    assert (lt == [EvOpen fs_fnm (Inr ())]);
    lem_theta_open fs_fnm (Inr ()) h
    end))

let equiv_oprod_openfile_oval #g (fs_fnm:fs_oval g qBool) (fnm:exp)
  : Lemma
    (requires fs_fnm ⊐ fnm)
    (ensures fs_oprod_openfile_oval fs_fnm ⊒ EOpen fnm)
  =
  lem_fv_in_env_openfile g fnm;
  introduce forall b (s:gsub g b) (fsG:eval_env g) (h:history). fsG `(∽) h` s ==> (qFileDescr ^+ qUnit) ⫄ (h, openfile (fs_fnm fsG), gsubst s (EOpen fnm)) with begin
    let fs_fnm = fs_fnm fsG in
    let fs_e = openfile fs_fnm in
    let e = EOpen (gsubst s fnm) in
    assert (gsubst s (EOpen fnm) == e);
    let EOpen fnm = e in
    introduce fsG `(∽) h` s ==> (qFileDescr ^+ qUnit) ⫄ (h, fs_e, e) with _. begin
      introduce forall (lt:local_trace h) (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:get_Type (qFileDescr ^+ qUnit)). (qFileDescr ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
        introduce e_beh e e' h lt ==> (exists (fs_r:get_Type (qFileDescr ^+ qUnit)). (qFileDescr ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
        let steps_pre : squash (helper_equiv_oprod_openfile_oval_steps_pre e e' h lt fs_fnm fs_e fnm) = () in
        FStar.Squash.map_squash #_ #(squash (exists (fs_r:get_Type (qFileDescr ^+ qUnit)). (qFileDescr ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r)) steps_pre (fun steps_pre ->
        helper_equiv_oprod_openfile_oval_steps #e #e' #h #lt #fs_fnm #fs_e #fnm steps_pre)
        end
      end
    end
  end

let helper_equiv_oprod_read_oval_steps_pre (e e':closed_exp) (h:history) (lt:local_trace h) (fs_fd:get_Type qFileDescr) (fs_e:io (get_Type (qBool ^+ qUnit))) (fd:closed_exp) =
  (fs_e == read fs_fd) /\
  (e == ERead fd) /\
  (e_beh e e' h lt) /\
  (qFileDescr ⊇ (h, fs_fd, fd))

let helper_equiv_oprod_read_oval_steps #e #e' #h #lt #fs_fd #fs_e #fd (sq:squash (helper_equiv_oprod_read_oval_steps_pre e e' h lt fs_fd fs_e fd)) : squash (exists (fs_r:get_Type (qBool ^+ qUnit)). (qBool ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) =
  lem_forall_values_are_values qFileDescr h fs_fd;
  FStar.Squash.bind_squash #(steps e e' h lt) () (fun steps_e_e' ->
  let (fd', (| lt1, lt' |)) = destruct_steps_eread_fd fd e' h lt steps_e_e' in
  FStar.Squash.bind_squash #(steps (ERead fd') e' (h++lt1) lt') () (fun sts1 ->
  let (e_r, (| lt2, (lt3, lt4, lt5) |)) = destruct_steps_eread fd' e' (h++lt1) lt' sts1 in
  assert (qFileDescr ⊇ (h, fs_fd, fd));
  lem_value_is_irred fd';
  match e_r with
  | EInl ETrue -> begin
    lem_value_is_irred ETrue;
    lem_value_is_irred (EInl ETrue);
    lem_destruct_steps_einl ETrue e' ((h++lt1)++lt2) lt3;
    assert ((qBool ^+ qUnit) ∋ (h++lt, Inl true, EInl ETrue));
    assert (lt == [EvRead fs_fd (Inl true)]);
    lem_theta_read fs_fd (Inl true) h
    end
  | EInl EFalse -> begin
    lem_value_is_irred EFalse;
    lem_value_is_irred (EInl EFalse);
    lem_destruct_steps_einl EFalse e' ((h++lt1)++lt2) lt4;
    assert ((qBool ^+ qUnit) ∋ (h++lt, Inl false, EInl EFalse));
    assert (lt == [EvRead fs_fd (Inl false)]);
    lem_theta_read fs_fd (Inl false) h
    end
  | EInr EUnit -> begin
    lem_value_is_irred EUnit;
    lem_value_is_irred (EInr EUnit);
    lem_destruct_steps_einr EUnit e' ((h++lt1)++lt2) lt5;
    assert ((qBool ^+ qUnit) ∋ (h++lt, Inr (), EInr EUnit));
    assert (lt == [EvRead fs_fd (Inr ())]);
    lem_theta_read fs_fd (Inr ()) h
    end))

let equiv_oprod_read_oval #g (fs_fd:fs_oval g qFileDescr) (fd:exp)
  : Lemma
    (requires fs_fd ⊐ fd)
    (ensures fs_oprod_read_oval fs_fd ⊒ ERead fd)
  =
  lem_fv_in_env_read g fd;
  introduce forall b (s:gsub g b) (fsG:eval_env g) (h:history). fsG `(∽) h` s ==> (qBool ^+ qUnit) ⫄ (h, read (fs_fd fsG), gsubst s (ERead fd)) with begin
    let fs_fd = fs_fd fsG in
    let fs_e = read fs_fd in
    let e = ERead (gsubst s fd) in
    assert (gsubst s (ERead fd) == e);
    let ERead fd = e in
    introduce fsG `(∽) h` s ==> (qBool ^+ qUnit) ⫄ (h, fs_e, e) with _. begin
      introduce forall (lt:local_trace h) (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:get_Type (qBool ^+ qUnit)). (qBool ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
        introduce e_beh e e' h lt ==> (exists (fs_r:get_Type (qBool ^+ qUnit)). (qBool ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
        let steps_pre : squash (helper_equiv_oprod_read_oval_steps_pre e e' h lt fs_fd fs_e fd) = () in
        FStar.Squash.map_squash #_ #(squash (exists (fs_r:get_Type (qBool ^+ qUnit)). (qBool ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r)) steps_pre (fun steps_pre ->
        helper_equiv_oprod_read_oval_steps #e #e' #h #lt #fs_fd #fs_e #fd steps_pre)
        end
      end
    end
  end

let helper_equiv_oprod_write_oval_steps_pre (e e':closed_exp) (h:history) (lt:local_trace h) (fs_fd:file_descr) (fs_msg:bool) (fs_e:fs_prod (qUnit ^+ qUnit)) (fd msg:closed_exp) =
  (fs_e == write (fs_fd, fs_msg)) /\
  (e == (EWrite fd msg)) /\
  e_beh (EWrite fd msg) e' h lt /\
  (qFileDescr ⊇ (h, fs_fd, fd)) /\
  (forall (lt:local_trace h). qBool ⊇ (h++lt, fs_msg, msg))

#push-options "--z3rlimit 10000"
let helper_equiv_oprod_write_oval_steps #e #e' #h #lt #fs_fd #fs_msg #fs_e #fd #msg (sq:squash (helper_equiv_oprod_write_oval_steps_pre e e' h lt fs_fd fs_msg fs_e fd msg)) : squash (exists (fs_r:get_Type (qUnit ^+ qUnit)). (qUnit ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) =
  lem_forall_values_are_values qFileDescr h fs_fd;
  FStar.Squash.bind_squash #(steps e e' h lt) () (fun sts ->
  let (fd', (| lt1, lt' |)) = destruct_steps_ewrite_fd fd msg e' h lt sts in
  FStar.Squash.bind_squash #(steps (EWrite fd' msg) e' (h++lt1) lt') () (fun sts1 ->
  let (msg', (| lt2, lt'' |)) = destruct_steps_ewrite_arg fd' msg e' (h++lt1) lt' sts1 in
  FStar.Squash.bind_squash #(steps (EWrite fd' msg') e' ((h++lt1)++lt2) lt'') () (fun sts2 ->
  let (e_r, (| lt3, (lt4, lt5) |)) = destruct_steps_ewrite fd' msg' e' ((h++lt1)++lt2) lt'' sts2 in
  assert (qFileDescr ⊇ (h, fs_fd, fd));
  lem_value_is_irred fd';
  assert (qBool ⊇ (h, fs_msg, msg));
  lem_value_is_irred msg';
  match e_r with
  | EInl EUnit -> begin
    lem_value_is_irred EUnit;
    lem_value_is_irred (EInl EUnit);
    lem_destruct_steps_einl EUnit e' (((h++lt1)++lt2)++lt3) lt4;
    assert ((qUnit ^+ qUnit) ∋ (h++lt, Inl (), EInl EUnit));
    assert (lt == [EvWrite (fs_fd, fs_msg) (Inl ())]);
    lem_theta_write (fs_fd, fs_msg) (Inl ()) h
    end
  | EInr EUnit -> begin
    lem_value_is_irred EUnit;
    lem_value_is_irred (EInr EUnit);
    lem_destruct_steps_einr EUnit e' (((h++lt1)++lt2)++lt3) lt5;
    assert ((qUnit ^+ qUnit) ∋ (h++lt, Inr (), EInr EUnit));
    assert (lt == [EvWrite (fs_fd, fs_msg) (Inr ())]);
    lem_theta_write (fs_fd, fs_msg) (Inr ()) h
    end)))
#pop-options

let equiv_oprod_write_oval #g (fs_fd:fs_oval g qFileDescr) (fs_msg:fs_oval g qBool) (fd msg:exp)
  : Lemma
    (requires fs_fd ⊐ fd /\ fs_msg ⊐ msg)
    (ensures fs_oprod_write_oval fs_fd fs_msg ⊒ EWrite fd msg)
  =
  lem_fv_in_env_write g fd msg;
  introduce forall b (s:gsub g b) (fsG:eval_env g) (h:history). fsG `(∽) h` s ==> (qUnit ^+ qUnit) ⫄ (h, write (fs_fd fsG, fs_msg fsG), gsubst s (EWrite fd msg)) with begin
    let fs_fd = fs_fd fsG in
    let fs_msg = fs_msg fsG in
    let fs_e = write (fs_fd, fs_msg) in
    let e = EWrite (gsubst s fd) (gsubst s msg) in
    assert (gsubst s (EWrite fd msg) == e);
    let EWrite fd msg = e in
    introduce fsG `(∽) h` s ==> (qUnit ^+ qUnit) ⫄ (h, fs_e, e) with _. begin
      introduce forall (lt:local_trace h) (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:get_Type (qUnit ^+ qUnit)). (qUnit ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
        introduce e_beh e e' h lt ==> (exists (fs_r:get_Type (qUnit ^+ qUnit)). (qUnit ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
          lem_shift_type_value_environments h fsG s;
          let steps_pre : squash (helper_equiv_oprod_write_oval_steps_pre e e' h lt fs_fd fs_msg fs_e fd msg) = () in
          FStar.Squash.map_squash #_ #(squash (exists (fs_r:get_Type (qUnit ^+ qUnit)). (qUnit ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r)) steps_pre (fun steps_pre ->
          helper_equiv_oprod_write_oval_steps #e #e' #h #lt #fs_fd #fs_msg #fs_e #fd #msg steps_pre)
        end
      end
    end
  end

let helper_equiv_oprod_close_oval_steps_pre (e e':closed_exp) (h:history) (lt:local_trace h) (fs_fd:get_Type qFileDescr) (fs_e:io (get_Type (qUnit ^+ qUnit))) (fd:closed_exp) =
  (fs_e == close fs_fd) /\
  (e == EClose fd) /\
  (e_beh e e' h lt) /\
  (qFileDescr ⊇ (h, fs_fd, fd))

let helper_equiv_oprod_close_oval_steps #e #e' #h #lt #fs_fd #fs_e #fd (sq:squash (helper_equiv_oprod_close_oval_steps_pre e e' h lt fs_fd fs_e fd)) : squash (exists (fs_r:get_Type (qUnit ^+ qUnit)). (qUnit ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) =
  lem_forall_values_are_values qFileDescr h fs_fd;
  FStar.Squash.bind_squash #(steps e e' h lt) () (fun steps_e_e' ->
  let (fd', (| lt1, lt' |)) = destruct_steps_eclose_fd fd e' h lt steps_e_e' in
  FStar.Squash.bind_squash #(steps (EClose fd') e' (h++lt1) lt') () (fun sts1 ->
  let (e_r, (| lt2, (lt3, lt4) |)) = destruct_steps_eclose fd' e' (h++lt1) lt' sts1 in
  assert (qFileDescr ⊇ (h, fs_fd, fd));
  lem_value_is_irred fd';
  match e_r with
  | EInl EUnit -> begin
    lem_value_is_irred EUnit;
    lem_value_is_irred (EInl EUnit);
    lem_destruct_steps_einl EUnit e' ((h++lt1)++lt2) lt3;
    assert ((qUnit ^+ qUnit) ∋ (h++lt, Inl (), EInl EUnit));
    assert (lt == [EvClose (get_fd fd') (Inl ())]);
    lem_theta_close fs_fd (Inl ()) h
    end
  | EInr EUnit -> begin
    lem_value_is_irred EUnit;
    lem_value_is_irred (EInr EUnit);
    lem_destruct_steps_einr EUnit e' ((h++lt1)++lt2) lt4;
    assert ((qUnit ^+ qUnit) ∋ (h++lt, Inr (), EInr EUnit));
    assert (lt == [EvClose (get_fd fd') (Inr ())]);
    lem_theta_close fs_fd (Inr ()) h
    end))

let equiv_oprod_close_oval #g (fs_fd:fs_oval g qFileDescr) (fd:exp)
  : Lemma
    (requires fs_fd ⊐ fd)
    (ensures fs_oprod_close_oval fs_fd ⊒ EClose fd)
  =
  lem_fv_in_env_close g fd;
  introduce forall b (s:gsub g b) (fsG:eval_env g) (h:history). fsG `(∽) h` s ==> (qUnit ^+ qUnit) ⫄ (h, close (fs_fd fsG), gsubst s (EClose fd)) with begin
    let fs_fd = fs_fd fsG in
    let fs_e = close fs_fd in
    let e = EClose (gsubst s fd) in
    assert (gsubst s (EClose fd) == e);
    let EClose fd = e in
    introduce fsG `(∽) h` s ==> (qUnit ^+ qUnit) ⫄ (h, fs_e, e) with _. begin
      introduce forall (lt:local_trace h) (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:get_Type (qUnit ^+ qUnit)). (qUnit ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
        introduce e_beh e e' h lt ==> (exists (fs_r:get_Type (qUnit ^+ qUnit)). (qUnit ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
        let steps_pre : squash (helper_equiv_oprod_close_oval_steps_pre e e' h lt fs_fd fs_e fd) = () in
        FStar.Squash.map_squash #_ #(squash (exists (fs_r:get_Type (qUnit ^+ qUnit)). (qUnit ^+ qUnit) ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r)) steps_pre (fun steps_pre ->
        helper_equiv_oprod_close_oval_steps #e #e' #h #lt #fs_fd #fs_e #fd steps_pre)
        end
      end
    end
  end

let equiv_oprod_unit g : Lemma (fs_oprod_return_val g qUnit () ⊒ EUnit) =
  equiv_oval_unit g;
  equiv_oprod_return (fs_oval_return g qUnit ()) EUnit

let equiv_oprod_true g : Lemma (fs_oprod_return_val g qBool true ⊒ ETrue) =
  equiv_oval_true g;
  equiv_oprod_return (fs_oval_return g qBool true) ETrue

let equiv_oprod_false g : Lemma (fs_oprod_return_val g qBool false ⊒ EFalse) =
  equiv_oval_false g;
  equiv_oprod_return (fs_oval_return g qBool false) EFalse

let equiv_oprod_if #g
  (#t:qType)
  (fs_e1:fs_oprod g qBool) (fs_e2:fs_oprod g t) (fs_e3:fs_oprod g t)
  (e1:exp) (e2:exp) (e3:exp)
  : Lemma
    (requires fs_e1 ⊒ e1 /\ fs_e2 ⊒ e2 /\ fs_e3 ⊒ e3)
    (ensures fs_oprod_if fs_e1 fs_e2 fs_e3 ⊒ EIf e1 e2 e3) =
  admit ()

let equiv_oprod_file_descr g fd : Lemma (fs_oprod_return_val g qFileDescr fd ⊒ EFileDescr fd) =
  equiv_oval_file_descr g fd;
  equiv_oprod_return (fs_oval_return g qFileDescr fd) (EFileDescr fd)

let equiv_oprod_var g (x:var{Some? (g x)}) : Lemma (fs_oprod_var g x ⊒ EVar x) =
  equiv_oval_var g x;
  equiv_oprod_return (fs_oval_var g x) (EVar x) 

let lem_io_bind_cong #a #b (m m':io a) (k k':a -> io b) :
  Lemma (requires m == m' /\ k == k')
        (ensures io_bind m k == io_bind m' k') = ()

let continuation_equivalence (#a #b:Type) (k k':a -> io b) :
  Lemma (requires forall x. k x == k' x)
        (ensures k == k') = admit ()

#push-options "--split_queries always" //--z3rlimit 32"
let equiv_oprod_app #g (#a #b:qType) (fs_f:fs_oprod g (a ^->!@ b)) (fs_x:fs_oprod g a) (f x:exp)
  : Lemma
    (requires fs_f ⊒ f /\ fs_x ⊒ x)
    (ensures fs_oprod_app fs_f fs_x ⊒ EApp f x)
  =
  assume (fv_in_env g x);
  assume (fv_in_env g f);
  assume (fv_in_env g (EApp f x));
  introduce forall b' (s:gsub g b') fsG h. fsG `(∽) h` s ==> b ⫄ (h, io_bind (fs_f fsG) (fun (x_:get_Type (a ^->!@ b)) -> (fun (fsG_:eval_env (extend (a ^->!@ b) g)) -> (fun (f':get_Type (a ^->!@ b)) -> fs_oprod_bind fs_x (fun (fsG':eval_env (extend a g)) -> (fun (x':get_Type a) -> fs_oprod_return_prod _ _ (f' x')) (hd fsG') (tail fsG'))) (hd fsG_) (tail fsG_)) (stack fsG x_)), gsubst s (EApp f x)) with begin
  introduce _ ==> _ with _. begin
    let fs_f = fs_f fsG in
    let fs_e = io_bind fs_f (fun (x_:get_Type (a ^->!@ b)) -> (fun (fsG_:eval_env (extend (a ^->!@ b) g)) -> (fun (f':get_Type (a ^->!@ b)) -> fs_oprod_bind fs_x (fun (fsG':eval_env (extend a g)) -> (fun (x':get_Type a) -> fs_oprod_return_prod _ _ (f' x')) (hd fsG') (tail fsG'))) (hd fsG_) (tail fsG_)) (stack fsG x_)) in
    let e = EApp (gsubst s f) (gsubst s x) in
    assert (gsubst s (EApp f x) == e);
    let EApp f x = e in
    introduce fsG `(∽) h` s ==> b ⫄ (h, fs_e, e) with _. begin
      introduce forall lt (e':closed_exp). e_beh e e' h lt ==> (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with begin
        introduce e_beh e e' h lt ==> (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r) with _. begin
          lem_forall_values_are_values_prod (a ^->!@ b) h;
          assert (forall f' lt1. e_beh f f' h lt1 ==> (ELam? f' /\ is_closed f'));
          FStar.Squash.bind_squash #(steps e e' h lt) () (fun sts1 ->
          let a_typ = type_quotation_to_typ (get_rel a) in
          let b_typ = type_quotation_to_typ (get_rel b) in
          let (f1, (| lt1, lt' |)) = destruct_steps_eapp_e1 f x e' h lt sts1 a_typ b_typ in
          assert ((a ^->!@ b) ⫄ (h, fs_f, f));
          assert (e_beh f (ELam f1) h lt1 ==> (exists (fs_r_f:get_Type (a ^->!@ b)). (a ^->!@ b) ∋ (h++lt1, fs_r_f, (ELam f1)) /\ fs_beh fs_f h lt1 fs_r_f));
          lem_value_is_irred (ELam f1);
          eliminate exists (fs_r_f:get_Type (a ^->!@ b)). (a ^->!@ b) ∋ (h++lt1, fs_r_f, (ELam f1)) /\ fs_beh fs_f h lt1 fs_r_f
          returns exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r with _. begin
          assert (a ⫄ (h, (fs_x fsG), x));
          lem_shift_type_value_environments h fsG s;
          assert (a ⫄ (h++lt1, (fs_x fsG), x));
          lem_forall_values_are_values_prod a (h++lt1);
          assert (forall x' (lt2:local_trace (h++lt1)) (fs_r:get_Type a). a ∋ ((h++lt1)++lt2, fs_r, x') ==> is_value x');
          assert (forall x' (lt2:local_trace (h++lt1)). e_beh x x' (h++lt1) lt2 ==> is_value x');
          FStar.Squash.bind_squash #(steps (EApp (ELam f1) x) e' (h++lt1) lt') () (fun sts2 ->
          let (x', (| lt2, lt'' |)) = destruct_steps_eapp_e2 f1 x e' (h++lt1) lt' sts2 in
          assert (e_beh x x' (h++lt1) lt2 ==> (exists (fs_r_x:get_Type a). a ∋ ((h++lt1)++lt2, fs_r_x, x') /\ fs_beh (fs_x fsG) (h++lt1) lt2 fs_r_x));
          lem_value_is_irred x';
          eliminate exists (fs_r_x:get_Type a). a ∋ ((h++lt1)++lt2, fs_r_x, x') /\ fs_beh (fs_x fsG) (h++lt1) lt2 fs_r_x
          returns exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r with _. begin
	  unfold_contains_io_arrow a b (h++lt1) fs_r_f f1;
          assert (b ⫄ ((h++lt1)++lt2, fs_r_f fs_r_x, subst_beta x' f1));
          eliminate exists (fs_r_fx:get_Type b). b ∋ (((h++lt1)++lt2)++lt'', fs_r_fx, e') /\ fs_beh (fs_r_f fs_r_x) ((h++lt1)++lt2) lt'' fs_r_fx
          returns exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r with _. begin
          assert (thetaP (fs_r_f fs_r_x) ((h++lt1)++lt2) lt'' fs_r_fx);
          assert (thetaP (fs_x fsG) (h++lt1) lt2 fs_r_x);
          lem_thetaP_bind (fs_x fsG) (h++lt1) lt2 fs_r_x fs_r_f lt'' fs_r_fx;
          assert (thetaP (io_bind (fs_x fsG) fs_r_f) (h++lt1) (lt2@lt'') fs_r_fx);
          assert (thetaP fs_f h lt1 fs_r_f);
          lem_thetaP_bind fs_f h lt1 fs_r_f (fun (x:get_Type (a ^->!@ b)) -> io_bind (fs_x fsG) x) (lt2@lt'') fs_r_fx;
          introduce forall x1. (fun (x_:get_Type (a ^->!@ b)) -> (fun (fsG_:eval_env (extend (a ^->!@ b) g)) -> (fun (f':get_Type (a ^->!@ b)) -> fs_oprod_bind fs_x (fun (fsG':eval_env (extend a g)) -> (fun (x':get_Type a) -> fs_oprod_return_prod _ _ (f' x')) (hd fsG') (tail fsG'))) (hd fsG_) (tail fsG_)) (stack fsG x_)) x1 == (fun (x:get_Type (a ^->!@ b)) -> io_bind (fs_x fsG) x) x1 with begin
            lem_hd_stack fsG x1;
            tail_stack_inverse fsG x1;
            assert (fs_oprod_bind fs_x (fun (fsG':eval_env (extend a g)) -> (fun (x':get_Type a) -> fs_oprod_return_prod _ _ ((hd (stack fsG x1)) x')) (hd fsG') (tail fsG')) (tail (stack fsG x1)) == fs_oprod_bind fs_x (fun (fsG':eval_env (extend a g)) -> (fun (x':get_Type a) -> fs_oprod_return_prod _ _ (x1 x')) (hd fsG') (tail fsG')) (tail (stack fsG x1))) by (FStar.Tactics.compute ());
            assert (fs_oprod_bind fs_x (fun (fsG':eval_env (extend a g)) -> (fun (x':get_Type a) -> fs_oprod_return_prod _ _ (x1 x')) (hd fsG') (tail fsG')) (tail (stack fsG x1)) == io_bind (fs_x (tail (stack fsG x1))) (fun y -> (fun (fsG':eval_env (extend a g)) -> (fun (x':get_Type a) -> fs_oprod_return_prod _ _ (x1 x')) (hd fsG') (tail fsG')) (stack (tail (stack fsG x1)) y))) by (FStar.Tactics.compute ());
            assert (io_bind (fs_x (tail (stack fsG x1))) (fun y -> (fun (fsG':eval_env (extend a g)) -> (fun (x':get_Type a) -> fs_oprod_return_prod _ _ (x1 x')) (hd fsG') (tail fsG')) (stack (tail (stack fsG x1)) y)) == io_bind (fs_x (tail (stack fsG x1))) (fun y -> (fun (x':get_Type a) -> fs_oprod_return_prod _ _ (x1 x')) (hd (stack fsG y)) (tail (stack fsG y)))) by (FStar.Tactics.compute ());
            assert (io_bind (fs_x (tail (stack fsG x1))) (fun y -> (fun (x':get_Type a) -> fs_oprod_return_prod _ _ (x1 x')) (hd (stack fsG y)) (tail (stack fsG y))) == io_bind (fs_x (tail (stack fsG x1))) (fun y -> (x1 (hd (stack fsG y))))) by (FStar.Tactics.compute ());
            assert (tail (stack fsG x1) == fsG);
            assert ((fs_x (tail (stack fsG x1))) == (fs_x fsG));
            introduce forall y'. (fun y -> (x1 (hd (stack fsG y)))) y' == x1 y' with begin
              lem_hd_stack fsG y'
            end;
            continuation_equivalence (fun y -> (x1 (hd (stack fsG y)))) x1
          end;
          continuation_equivalence (fun (x_:get_Type (a ^->!@ b)) -> (fun (fsG_:eval_env (extend (a ^->!@ b) g)) -> (fun (f':get_Type (a ^->!@ b)) -> fs_oprod_bind fs_x (fun (fsG':eval_env (extend a g)) -> (fun (x':get_Type a) -> fs_oprod_return_prod _ _ (f' x')) (hd fsG') (tail fsG'))) (hd fsG_) (tail fsG_)) (stack fsG x_)) (fun (x:get_Type (a ^->!@ b)) -> io_bind (fs_x fsG) x);
          lem_io_bind_cong fs_f fs_f (fun (x_:get_Type (a ^->!@ b)) -> (fun (fsG_:eval_env (extend (a ^->!@ b) g)) -> (fun (f':get_Type (a ^->!@ b)) -> fs_oprod_bind fs_x (fun (fsG':eval_env (extend a g)) -> (fun (x':get_Type a) -> fs_oprod_return_prod _ _ (f' x')) (hd fsG') (tail fsG'))) (hd fsG_) (tail fsG_)) (stack fsG x_)) (fun (x:get_Type (a ^->!@ b)) -> io_bind (fs_x fsG) x);
          assume (io_bind fs_f (fun (x_:get_Type (a ^->!@ b)) -> (fun (fsG_:eval_env (extend (a ^->!@ b) g)) -> (fun (f':get_Type (a ^->!@ b)) -> fs_oprod_bind fs_x (fun (fsG':eval_env (extend a g)) -> (fun (x':get_Type a) -> fs_oprod_return_prod _ _ (f' x')) (hd fsG') (tail fsG'))) (hd fsG_) (tail fsG_)) (stack fsG x_)) == io_bind fs_f (fun (x:get_Type (a ^->!@ b)) -> io_bind (fs_x fsG) x))
          end
          end)
          end)
        end
      end
    end
  end
  end
#pop-options

let equiv_oprod_lambda #g (#t1:qType) (#t2:qType)
  (fs_body:fs_oprod (extend t1 g) t2)
  (body:exp)
  : Lemma
    (requires fs_body ⊒ body)
    (ensures fs_oprod_lambda fs_body ⊒ (ELam body))
  =
  equiv_oval_lambda_oprod #g #t1 #t2 fs_body body;
  equiv_oprod_return (fs_oval_lambda_oprod fs_body) (ELam body)

let equiv_oprod_inl #g (t1 t2:qType) (fs_e:fs_oprod g t1) (e:exp)
  : Lemma
    (requires fs_e ⊒ e)
    (ensures fs_oprod_fmap #g #t1 #(t1 ^+ t2) fs_e Inl ⊒ (EInl e))
  = admit ()

let equiv_oprod_inr #g (t1 t2:qType) (fs_e:fs_oprod g t2) (e:exp)
  : Lemma
    (requires fs_e ⊒ e)
    (ensures fs_oprod_fmap #g #t2 #(t1 ^+ t2) fs_e Inr ⊒ (EInr e))
  =
  admit ()

let equiv_oprod_pair #g
  (#t1 #t2:qType)
  (fs_e1:fs_oprod g t1) (fs_e2:fs_oprod g t2)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ⊒ e1 /\ fs_e2 ⊒ e2)
    (ensures fs_oprod_pair fs_e1 fs_e2 ⊒ EPair e1 e2) =
  admit ()

let equiv_oprod_fst #g
  (#t1 #t2:qType)
  (fs_e12:fs_oprod g (t1 ^* t2))
  (e12:exp)
  : Lemma
    (requires fs_e12 ⊒ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures fs_oprod_fmap fs_e12 fst ⊒ (EFst e12))
  = admit ()

let equiv_oprod_snd #g (#t1 #t2:qType) (fs_e12:fs_oprod g (t1 ^* t2)) (e12:exp)
  : Lemma
    (requires fs_e12 ⊒ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures fs_oprod_fmap fs_e12 snd ⊒ (ESnd e12)) =
  admit ()

let equiv_oprod_case #g (#a #b #c:qType)
  (fs_cond:fs_oprod g (a ^+ b))
  (fs_inlc:fs_oprod (extend a g) c)
  (fs_inrc:fs_oprod (extend b g) c)
  (cond inlc inrc:exp)
  : Lemma
    (requires fs_cond ⊒ cond /\ fs_inlc ⊒ inlc /\ fs_inrc ⊒ inrc)
    (ensures (fs_oprod_case fs_cond fs_inlc fs_inrc) ⊒ (ECase cond inlc inrc)) =
  admit ()

let equiv_oprod_openfile #g (fs_fnm:fs_oprod g qBool) (fnm:exp)
  : Lemma
    (requires fs_fnm ⊒ fnm)
    (ensures fs_oprod_openfile fs_fnm ⊒ EOpen fnm)
  = admit ()

let equiv_oprod_read #g (fs_fd:fs_oprod g qFileDescr) (fd:exp)
  : Lemma
    (requires fs_fd ⊒ fd)
    (ensures fs_oprod_read fs_fd ⊒ ERead fd)
  = admit ()

let equiv_oprod_write #g (fs_fd:fs_oprod g qFileDescr) (fs_msg:fs_oprod g qBool) (fd msg:exp)
  : Lemma
    (requires fs_fd ⊒ fd /\ fs_msg ⊒ msg)
    (ensures fs_oprod_write fs_fd fs_msg ⊒ EWrite fd msg)
  = admit ()

let equiv_oprod_close #g (fs_fd:fs_oprod g qFileDescr) (fd:exp)
  : Lemma
    (requires fs_fd ⊒ fd)
    (ensures fs_oprod_close fs_fd ⊒ EClose fd)
  = admit ()
