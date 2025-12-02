module ExpRel

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open QTyp
open IO
open Trace

(** Section 8.1: https://www.cs.uoregon.edu/research/summerschool/summer24/lectures/Ahmed.pdf **)

let io_oexp (g:typ_env) (t:qType) =
  eval_env g -> io (get_Type t)

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __closed terms__. **)
let rec (∋) (t:qType) (p:(history * fs_val t * closed_exp)) : Tot Type0 (decreases %[get_rel t;0]) =
  let (h, fs_v, e) = p in
  match get_rel t with // way to "match" on F* types
  | QUnit -> fs_v == () /\ e == EUnit
  | QBool -> (fs_v == true /\ e == ETrue) \/ (fs_v == false /\ e == EFalse)
  | QArr #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> t2 = fs_v in
    match e with
    | ELam e' ->
      (forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∋ (h++lt_v, fs_v, v) ==>
        pack qt2 ⦂ (h++lt_v, fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
  | QArrIO #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> io t2 = fs_v in
    match e with
    | ELam e' -> // instead quantify over h'' - extensions of the history
      (forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∋ (h++lt_v, fs_v, v) ==>
        pack qt2 ⪾ (h++lt_v, fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
  | QPair #t1 #t2 qt1 qt2 -> begin
    match e with
    | EPair e1 e2 -> (** e1 and e2 are values. no need to quantify over lts **)
        pack qt1 ∋ (h, fst #t1 #t2 fs_v, e1) /\ pack qt2 ∋ (h, snd #t1 #t2 fs_v, e2)
    | _ -> False
  end
  | QSum #t1 #t2 qt1 qt2 -> begin
    let fs_v : either t1 t2 = fs_v in
    match fs_v, e with
    | Inl fs_v', EInl e' -> pack qt1 ∋ (h, fs_v', e')
    | Inr fs_v', EInr e' -> pack qt2 ∋ (h, fs_v', e')
    | _ -> False
  end
                           (** vvvvvvvvvv defined over values **)
and (⦂) (t:qType) (p:history * fs_val t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
  let (h, fs_e, e) = p in
  forall (e':closed_exp).
    steps e e' h [] ==> indexed_irred e' h ==>
    t ∋ (h, fs_e, e')
                           (** vvvvvvvvvv defined over producers **)
and (⪾) (t:qType) (p:history * fs_prod t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
  let (h, fs_e, e) = p in
  forall lt (e':closed_exp).
    steps e e' h lt ==> indexed_irred e' (h++lt) ==>
    (exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e'))// /\ (forall p. theta fs_e h p ==> p lt fs_r))
                           (** TODO: ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ check this **)

let lem_values_are_expressions t h fs_e e : (** lemma used by Amal **)
  Lemma (requires t ∋ (h, fs_e, e))
        (ensures  t ⦂ (h, fs_e, e)) = admit ()

let lem_values_are_producers t h fs_e e : (** lemma used by Amal **)
  Lemma (requires t ∋ (h, fs_e, e))
        (ensures  t ⪾ (h, io_return fs_e, e)) = admit ()

let rec lem_values_are_values t h fs_e (e:closed_exp) :
  Lemma (requires t ∋ (h, fs_e, e))
        (ensures is_value e)
        (decreases e) =
  match get_rel t with
  | QUnit -> ()
  | QBool -> ()
  | QArr _ _ -> ()
  | QArrIO _ _ -> ()
  | QPair #t1 #t2 qt1 qt2 ->
    let EPair e1 e2 = e in
    lem_values_are_values (pack qt1) h (fst #t1 #t2 fs_e) e1;
    lem_values_are_values (pack qt2) h (snd #t1 #t2 fs_e) e2
  | QSum #t1 #t2 qt1 qt2 ->
    match fs_e, e with
    | Inl fs_e', EInl e' -> lem_values_are_values (pack qt1) h fs_e' e'
    | Inr fs_e', EInr e' -> lem_values_are_values (pack qt2) h fs_e' e'

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

let (∽) (#g:typ_env) #b (h:history) (fsG:eval_env g) (s:gsub g b) : Type0 =
  forall (x:var). Some? (g x) ==>
    Some?.v (g x) ∋ (h, index fsG x, s x)
  (**  TODO      ^^^ not like in Amal's work. she uses an exp relation - but this is what she meant, because index fsG x is necessarily a value **)

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __open terms__. **)
let equiv_oval (#g:typ_env) (t:qType) (fs_e:fs_oval g t) (e:exp) : Type0 =
  fv_in_env g e /\
  forall b (s:gsub g b) (fsG:eval_env g) (h:history).
    fsG `(∽) h` s ==> t ⦂ (h, fs_e fsG, gsubst s e)

let equiv_oprod (#g:typ_env) (t:qType) (fs_e:fs_oprod g t) (e:exp) : Type0 =
  fv_in_env g e /\
  forall b (s:gsub g b) (fsG:eval_env g) (h:history).
    fsG `(∽) h` s ==> t ⪾ (h, fs_e fsG, gsubst s e)

let equiv_val (#t:qType) (fs_e:fs_val t) (e:exp) : Type0 =
  equiv_oval #empty t (fun _ -> fs_e) e

let equiv_prod (#t:qType) (fs_e:fs_prod t) (e:exp) : Type0 =
  equiv_oprod #empty t (fun _ -> fs_e) e

let safety_val (#t:qType) (fs_e:fs_val t) (e:exp) : Lemma
  (requires (equiv_val fs_e e))
  (ensures safe e) =
  admit ()

let safety (#t:qType) (fs_e:fs_prod t) (e:exp) : Lemma
  (requires (equiv_prod fs_e e))
  (ensures safe e) =
  introduce forall (e':closed_exp) (h:history) (lt:local_trace h).
    steps e e' h lt ==> is_value e' \/ can_step e' with begin
    introduce steps e e' h lt ==> is_value e' \/ can_step e' with _. begin
      introduce irred e' ==> is_value e' with _. begin
        eliminate forall b (s:gsub empty b) (fsG:eval_env empty) (h:history).
          fsG `(∽) h` s ==> t ⪾ (h, fs_e, gsubst s e)
        with  true gsub_empty empty_eval h;
        assert (t ⪾ (h, fs_e, e));
        eliminate exists fs_r. t ∋ (h++lt, fs_r, e')// /\ (forall p. theta fs_e h p ==> p lt fs_r)
        returns is_value e' with _. begin
          assert (t ∋ (h++lt, fs_r, e'));
          lem_values_are_values t (h++lt) fs_r e';
          assert (is_value e')
        end
      end
    end
  end

let (≈) (#g:typ_env) (#t:qType) (fs_v:fs_oval g t) (e:exp) : Type0 =
  equiv_oval #g t fs_v e

(** Equiv closed terms **)
let lem_equiv_val (#t:qType) (fs_e:fs_val t) (e:closed_exp) :
  Lemma (requires equiv_val fs_e e)
        (ensures forall h. t ⦂ (h, fs_e, e)) =
  admit ()

let lem_equiv_val' (#t:qType) (fs_e:fs_val t) (e:closed_exp) :
  Lemma (requires forall h. t ⦂ (h, fs_e, e))
        (ensures equiv_val fs_e e) =
  admit ()

let lem_equiv_prod (#t:qType) (fs_e:fs_prod t) (e:closed_exp) :
  Lemma (requires equiv_prod fs_e e)
        (ensures forall h. t ⪾ (h, fs_e, e)) =
  eliminate forall b (s:gsub empty b) (fsG:eval_env empty). forall h.
    fsG `(∽) h` s ==> t ⪾ (h, (fun _ -> fs_e) fsG, gsubst s e) with true gsub_empty empty_eval

let lem_equiv_prod' (g:typ_env) (#t:qType) (fs_e:fs_prod t) (e:closed_exp) :
  Lemma (requires (forall h. t ⪾ (h, fs_e, e)))
        (ensures equiv_prod fs_e e) =
  introduce forall b (s:gsub empty b) (fsG:eval_env empty) (h':history).
    fsG `(∽) h'` s ==> t ⪾ (h', (fun _ -> fs_e) fsG, gsubst s e) with begin
    introduce fsG `(∽) h'` s ==> t ⪾ (h', (fun _ -> fs_e) fsG, gsubst s e) with _. begin
      assert (gsubst s e == e);
      assert ((fun _ -> fs_e) fsG == fs_e);
      eliminate forall h. t ⪾ (h, fs_e, e) with h'
    end
  end

(** Rules **)

open QExp (** just to use the helpers functions **)

let equiv_unit g
  : Lemma (helper_unit g `equiv_oval qUnit` EUnit)
  =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qUnit ⦂ (h, (), gsubst s EUnit) with begin
    introduce _ ==> _ with _. begin
      assert (qUnit ∋ (h, (), EUnit));
      lem_values_are_expressions qUnit h () EUnit
    end
  end

let equiv_true g
  : Lemma (helper_true g `equiv_oval qBool` ETrue)
  =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qBool ⦂ (h, true, gsubst s ETrue) with begin
    introduce _ ==> _ with _. begin
      assert (qBool ∋ (h, true, ETrue));
      lem_values_are_expressions qBool h true ETrue
    end
  end

let equiv_false g
  : Lemma (helper_false g `equiv_oval qBool` EFalse)
  =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qBool ⦂ (h, false, gsubst s EFalse) with begin
    introduce _ ==> _ with _. begin
      assert (qBool ∋ (h, false, EFalse));
      lem_values_are_expressions qBool h false EFalse
    end
  end

let equiv_var g (x:var{Some? (g x)})
  : Lemma ((fun (fsG:eval_env g) -> index fsG x) ≈ EVar x)
  =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> Some?.v (g x) ⦂ (h, index fsG x, gsubst s (EVar x)) with begin
    introduce _ ==> _ with _. begin
      assert (Some?.v (g x) ∋ (h, index fsG x, s x));
      lem_values_are_expressions (Some?.v (g x)) h (index fsG x) (s x)
    end
  end

(** Used in compilation **)
let equiv_var0 (g:typ_env) (t:qType)
  : Lemma (helper_var0 g t ≈ EVar 0)
  =
  introduce forall b (s:gsub (extend t g) b) fsG h. fsG `(∽) h` s ==>  t ⦂ (h, hd fsG, gsubst s (EVar 0)) with begin
    introduce _ ==> _ with _. begin
      index_0_hd fsG;
      assert (t ∋ (h, hd fsG, s 0));
      lem_values_are_expressions t h (hd fsG) (s 0)
    end
  end

(** Used in compilation **)
let equiv_varS (#g:typ_env) #a #t (s:fs_oval g a) (e:exp)
  : Lemma
      (requires (s ≈ e))
      (ensures (helper_varS t s ≈ subst sub_inc e))
  = admit ()

let equiv_lam #g (#t1:qType) (#t2:qType) (fs_body:fs_oval (extend t1 g) t2) (body:exp) : Lemma
  (requires fs_body ≈ body)
  (ensures (helper_lambda fs_body ≈ ELam body)) =
  admit () (**
  lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  let f : fs_oval g (t1 ^-> t2) = fun fsG x -> fs_body (stack fsG x) in
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==>  (t1 ^-> t2) ⦂ (f fsG, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:fs_val t1). t1 ∋ (fs_v, v) ==>  t2 ⦂ (f fsG fs_v, subst_beta v body') with begin
>>>>>>> master
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fsG' = stack fsG fs_v in
          let h' = h++lt_v in
          eliminate forall b (s':gsub g' b) (fsG':eval_env g') h'. fsG' `(∽) h'` s' ==> t2 ⦂ (h', io_bind (f (tail #t1 fsG')) (fun f -> io_return (f (hd #t1 #g fsG'))), (gsubst s' body))
            with false s' fsG' h';
          assert (fsG `(∽) h` s);
          assume (stack fsG fs_v `(∽) h'` gsub_extend s t1 v); 
          assert (t2 ⦂ (h', io_bind (f (tail fsG')) (fun f -> io_return (f (hd fsG'))), (gsubst s' body)));
          assert ((hd fsG') == fs_v);
          assert (t2 ⦂ (h', io_bind (f (tail fsG')) (fun f -> io_return (f fs_v)), (gsubst s' body)));
          assert (t2 ⦂ (h', io_bind (f fsG) (fun f -> io_return (f fs_v)), (gsubst s' body)));
          lem_substitution s t1 v body;
          assert (t2 ⦂ (h', io_bind (f fsG) (fun f -> io_return (f fs_v)), subst_beta v body'))
        end
      end;
      //let f' = fun x -> io_bind (f fsG) (fun f -> io_return (f x)) in
      //let _ : io (get_Type t2) = io_bind (f fsG) (fun f -> io_return (f 
      //let _ : get_Type t1 -> io (get_Type (t1 ^-> t2)) = fun x -> f fsG in
      assert ((t1 ^-> t2) ∋ (h, f fsG, gsubst s (ELam body)));
      lem_values_are_expressions (t1 ^-> t2) h (f fsG) (gsubst s (ELam body));
      assert ((t1 ^-> t2) ⦂ (h, f fsG, gsubst s (ELam body)))
    end
  end**)


#push-options "--z3rlimit 5000 --fuel 5000"
let equiv_app #g
  (#t1:qType) (#t2:qType)
  (fs_e1:fs_oval g (t1 ^-> t2)) (fs_e2:fs_oval g t1)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2)
    (ensures (helper_app fs_e1 fs_e2 ≈ EApp e1 e2))
  = admit () (**
  lem_fv_in_env_app g e1 e2;
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==> t2 ⦂ ((fs_e1 fsG) (fs_e2 fsG), gsubst s (EApp e1 e2)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e2 = fs_e2 fsG in
    let fs_e = io_bind (fs_e1) (fun f -> io_bind fs_e2 (fun x -> io_return (f x))) in
    let e = EApp (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EApp e1 e2) == e);
    let EApp e1 e2 = e in
    introduce fsG `(∽) h` s ==> t2 ⦂ (h, fs_e, e) with _. begin
      introduce forall lt (e':closed_exp). steps e e' h lt /\ irred e' (h++lt) ==> (exists fs_r. t2 ∋ (h++lt, fs_r, e')) (*/\ (forall p. theta fs_e h p ==> p lt fs_r))*) with begin
        introduce _ ==> (exists fs_r. t2 ∋ (h++lt, fs_r, e')) (*/\ (forall p. theta fs_e h p ==> p lt fs_r))*) with _. begin
          let steps_e_e' : squash (steps e e' h lt) = () in
          FStar.Squash.map_squash #_ #(squash ((exists fs_r. t2 ∋ (h++lt, fs_r, e') (*/\ (forall p. theta fs_e h p ==> p lt fs_r)*)))) steps_e_e' (fun steps_e_e' ->
            assume (equiv_closed fs_e2 e2);
            safety #t1 fs_e2 e2;
            let t1_typ = type_quotation_to_typ (get_rel t1) in
            let t2_typ = type_quotation_to_typ (get_rel t2) in
            assume (forall h'. sem_expr_shape (TArr t1_typ t2_typ) e1 h');
            let (e11, e2', (| lt2, (| lt1, lt3 |) |)) = destruct_steps_eapp e1 e2 e' h lt steps_e_e' t1_typ t2_typ in
            //let fs_e1' : (get_Type t1) -> io (get_Type t2) = fun x -> io_bind fs_e1 (fun f -> io_return (f x)) in
            assume ((t1 ^-> t2) ∋ ((h++lt2)++lt1, fs_e1, ELam e11)); (** TODO/Cezar: this was working before the refactoring **)
            introduce True ==> exists fs_r2. t1 ∋ (h++lt2, fs_r2, e2') with _. begin
              assert (t1 ⦂ (h, fs_e2, e2));
              assert (steps e2 e2' h lt2);
              assume (irred e2' (h++lt2))
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
  end**)

let equiv_if #g (#t:qType) (fs_e1:fs_oval g qBool) (fs_e2:fs_oval g t) (fs_e3:fs_oval g t) (e1:exp) (e2:exp) (e3:exp) : Lemma
  (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2 /\ fs_e3 ≈ e3)
  (ensures helper_if fs_e1 fs_e2 fs_e3 ≈ EIf e1 e2 e3) =
  admit ()
  (**
  lem_fv_in_env_if g e1 e2 e3;
  introduce forall b (s:gsub g b) fsG. fsG ∽ s ==> t ⦂ ((if fs_e1 fsG then fs_e2 fsG else fs_e3 fsG), gsubst s (EIf e1 e2 e3)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e = if fs_e1 then fs_e2 fsG else fs_e3 fsG in
    let e = EIf (gsubst s e1) (gsubst s e2) (gsubst s e3) in
    assert (gsubst s (EIf e1 e2 e3) == e);
    let EIf e1 e2 e3 = e in
    introduce fsG `(∽) h` s ==> t ⦂ (h, fs_e, e) with _. begin
      introduce forall lt (e':closed_exp). steps e e' h lt /\ irred e' (h++lt) ==> (exists fs_r. t ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r)) with begin
        introduce _ ==> (exists fs_r. t ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r)) with _. begin
          let steps_e_e' : squash (steps e e' h lt) = () in
          FStar.Squash.map_squash #_ #(squash (exists fs_r. t ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r))) steps_e_e' (fun steps_e_e' ->
            assume (equiv_closed fs_e1 e1);
            safety #qBool fs_e1 e1;
            assume (equiv_closed (fs_e2 fsG) e2);
            safety #t (fs_e2 fsG) e2;
            assume (equiv_closed (fs_e3 fsG) e3);
            safety #t (fs_e3 fsG) e3;
            let (e1', (| lt1, (lt2, lt3) |)) = destruct_steps_eif e1 e2 e3 e' h lt steps_e_e' in
            assert (qBool ⦂ (h, fs_e1, e1));
            assert (qBool ∋ (h, fs_e1, e1'));
            assert (ETrue? e1' ==> (t ∋ (h++lt1, fs_e2 fsG, e')));
            assert (EFalse? e1' ==> (t ∋ (h++lt1, fs_e3 fsG, e')));
            assert (t ∋ (h++lt, fs_e, e'))
          )
        end
      end
    end
  end**)
#pop-options

let equiv_pair #g (#t1 #t2:qType) (fs_e1:fs_oval g t1) (fs_e2:fs_oval g t2) (e1:exp) (e2:exp) : Lemma
  (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2)
  (ensures helper_pair fs_e1 fs_e2 ≈ EPair e1 e2) =
  admit ()
  (**
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
  end **)

let equiv_pair_fst_app #g (#t1 #t2:qType) (fs_e12:fs_oval g (t1 ^* t2)) (e12:exp) : Lemma
  (requires fs_e12 ≈ e12) (** is this too strict? we only care for the left to be equivalent. **)
  (ensures helper_fst fs_e12 ≈ (EFst e12)) =
  admit ()
  (**
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
**)

let equiv_pair_snd_app #g (#t1 #t2:qType) (fs_e12:fs_oval g (t1 ^* t2)) (e12:exp)
  : Lemma
    (requires fs_e12 ≈ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures helper_snd fs_e12 ≈ (ESnd e12))
  =
  admit ()
  (**
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
  **)

let equiv_inl #g (#t1 t2:qType) (fs_e:fs_oval g t1) (e:exp) : Lemma
  (requires fs_e ≈ e)
  (ensures helper_inl t2 fs_e ≈ (EInl e)) =
  admit ()

let equiv_inr #g (t1 #t2:qType) (fs_e:fs_oval g t2) (e:exp) : Lemma
  (requires fs_e ≈ e)
  (ensures helper_inr t1 fs_e ≈ (EInr e)) =
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
    (ensures helper_case fs_case fs_lc fs_rc ≈ ECase e_case e_lc e_rc)
  = admit ()

let equiv_lam_prod #g (#t1:qType) (#t2:qType) (fs_body:fs_oprod (extend t1 g) t2) (body:exp)
  : Lemma
    (requires fs_body `equiv_oprod t2`  body)
    (ensures helper_lambda_prod fs_body `equiv_oval (t1 ^->!@ t2)` (ELam body))
  = admit ()

let equiv_oprod_read g
  : Lemma
    (requires True)
    (ensures (fun fsG -> read ()) `equiv_oprod #g qBool` ERead)
  = admit ()

let equiv_oprod_write #g (fs_arg:fs_oval g qBool) (arg:exp)
  : Lemma
    (requires fs_arg ≈ arg)
    (ensures (fun fsG -> write (fs_arg fsG)) `equiv_oprod #g qUnit` EWrite arg)
  = admit ()

let equiv_oprod_return #g (#t:qType) (fs_x:fs_oval g t) (x:exp)
  : Lemma
    (requires fs_x ≈ x)
    (ensures helper_return_prod fs_x `equiv_oprod t` x)
  = admit ()

let equiv_oprod_bind #g (#a #b:qType) (fs_m:fs_oprod g a) (fs_k:fs_oprod (extend a g) b) (m k:exp)
  : Lemma
    (requires fs_m `equiv_oprod a` m /\ fs_k `equiv_oprod b` k)
    (ensures (helper_bind_prod fs_m fs_k) `equiv_oprod b` (EApp (ELam k) m))
  = admit ()

let equiv_oprod_app #g (#a #b:qType) (fs_f:fs_oval g (a ^->!@ b)) (fs_x:fs_oval g a) (f x:exp)
  : Lemma
    (requires fs_f ≈ f /\ fs_x ≈ x)
    (ensures (helper_app_prod fs_f fs_x) `equiv_oprod b` (EApp f x))
  = admit ()

let equiv_oprod_if #g (#a:qType) (fs_c:fs_oval g qBool) (fs_t fs_e:fs_oprod g a) (c t e:exp)
  : Lemma
    (requires fs_c ≈ c /\ fs_t `equiv_oprod a` t /\ fs_e `equiv_oprod a` e)
    (ensures (helper_if_prod fs_c fs_t fs_e) `equiv_oprod a` (EIf c t e))
  = admit ()

let equiv_oprod_case #g (#a #b #c:qType) (fs_cond:fs_oval g (a ^+ b)) (fs_inlc:fs_oprod (extend a g) c) (fs_inrc:fs_oprod (extend b g) c) (cond inlc inrc:exp)
  : Lemma
    (requires fs_cond ≈ cond /\ fs_inlc `equiv_oprod c` inlc /\ fs_inrc `equiv_oprod c` inrc)
    (ensures (helper_case_prod fs_cond fs_inlc fs_inrc) `equiv_oprod c` (ECase cond inlc inrc))
  = admit ()
