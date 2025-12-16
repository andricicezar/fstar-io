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
  forall (e':closed_exp) lt.
    steps e e' h lt ==> indexed_irred e' (h++lt) ==>
    (t ∋ (h, fs_e, e') /\ lt == [] /\ (forall p. p lt fs_e))
                           (** vvvvvvvvvv defined over producers **)
and (⪾) (t:qType) (p:history * fs_prod t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
  let (h, fs_e, e) = p in
  forall (lt:local_trace h) (e':closed_exp).
    steps e e' h lt ==> indexed_irred e' (h++lt)  ==>
    (exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r))
                           (** TODO: ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ check this **)

let theta_history_independence' #t (e e':closed_exp) (fs_e:fs_prod t) (h:history) (lt:local_trace h) (fs_r:get_Type t):
  Lemma (requires steps e e' h lt /\ 
                  indexed_irred e' (h++lt) /\
                  t ∋ (h++lt, fs_r, e') /\
                  (forall p. theta fs_e h p ==> p lt fs_r))
        (ensures forall h' (lt':local_trace h') p. theta fs_e h' p ==> p lt' fs_r) =
  introduce forall h' lt' p. theta fs_e h' p ==> p lt' fs_r with begin
    introduce theta fs_e h' p ==> p lt' fs_r with _. begin
      admit ()
    end
  end

let rec val_type_history_independence (t:qType) (h:history) (fs_v:fs_val t) (e:closed_exp) :
  Lemma (requires t ∋ (h, fs_v, e))
        (ensures forall h'. t ∋ (h', fs_v, e))
        (decreases %[get_rel t;0]) =
  introduce forall h'. t ∋ (h', fs_v, e) with begin
  match get_rel t with
  | QUnit -> ()
  | QBool -> ()
  | QArr #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> t2 = fs_v in
    match e with
    | ELam e' -> begin
      introduce forall (v:value) (fs_v':t1) (lt_v':local_trace h'). pack qt1 ∋ (h'++lt_v', fs_v', v) ==> pack qt2 ⦂ (h'++lt_v', fs_f fs_v', subst_beta v e') with begin
        introduce pack qt1 ∋ (h'++lt_v', fs_v', v) ==> pack qt2 ⦂ (h'++lt_v', fs_f fs_v', subst_beta v e') with _. begin
          eliminate forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∋ (h++lt_v, fs_v, v) ==> pack qt2 ⦂ (h++lt_v, fs_f fs_v, subst_beta v e') with v fs_v' [];
          val_type_history_independence (pack qt1) (h'++lt_v') fs_v' v;
          exp_type_history_independence (pack qt2) h (fs_f fs_v') (subst_beta v e')
          end
        end
      end
    | _ -> false_elim ()
    end
  | QArrIO #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> io t2 = fs_v in
    match e with
    | ELam e' -> begin
      introduce forall (v:value) (fs_v':t1) (lt_v':local_trace h'). pack qt1 ∋ (h'++lt_v', fs_v', v) ==> pack qt2 ⪾ (h'++lt_v', fs_f fs_v', subst_beta v e') with begin
        introduce pack qt1 ∋ (h'++lt_v', fs_v', v) ==> pack qt2 ⪾ (h'++lt_v', fs_f fs_v', subst_beta v e') with _. begin
          eliminate forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∋ (h++lt_v, fs_v, v) ==> pack qt2 ⪾ (h++lt_v, fs_f fs_v, subst_beta v e') with v fs_v' [];
          val_type_history_independence (pack qt1) (h'++lt_v') fs_v' v;
          io_exp_type_history_independence (pack qt2) h (fs_f fs_v') (subst_beta v e')
          end
        end
      end
    | _ -> false_elim ()
    end
  | QPair #t1 #t2 qt1 qt2 -> begin
    match e with
    | EPair e1 e2 -> begin
      val_type_history_independence (pack qt1) h (fst #t1 #t2 fs_v) e1;
      val_type_history_independence (pack qt2) h (snd #t1 #t2 fs_v) e2
      end
    | _ -> false_elim ()
    end
  | QSum #t1 #t2 qt1 qt2 -> begin
    let fs_v : either t1 t2 = fs_v in
    match fs_v, e with
    | Inl fs_v', EInl e' -> val_type_history_independence (pack qt1) h fs_v' e'
    | Inr fs_v', EInr e' -> val_type_history_independence (pack qt2) h fs_v' e'
    | _ -> false_elim ()
    end
  end

and exp_type_history_independence (t:qType) (h:history) (fs_e:fs_val t) (e:closed_exp) :
  Lemma (requires t ⦂ (h, fs_e, e))
        (ensures forall h'. t ⦂ (h', fs_e, e))
        (decreases %[get_rel t;1]) = admit ()
  (*introduce forall h'. t ⦂ (h', fs_e, e) with begin
    introduce forall (e':closed_exp) lt'. steps e e' h' lt' /\ indexed_irred e' (h'++lt') ==> (t ∋ (h', fs_e, e') /\ lt' == []) with begin
      introduce steps e e' h' lt' /\ indexed_irred e' (h'++lt') ==> (t ∋ (h', fs_e, e') /\ lt' == []) with _. begin
        FStar.Squash.bind_squash #(steps e e' h' lt') () (fun sts ->
          steps_history_independence sts;
          eliminate forall h_. exists lt_. steps e e' h_ lt_ with h;
          eliminate exists lt_. steps e e' h lt_
          returns (t ∋ (h', fs_e, e') /\ lt' == []) with _. begin
            eliminate forall e_ lt_. steps e e_ h lt_ /\ indexed_irred e_ (h++lt_) ==> (t ∋ (h, fs_e, e_) /\ lt_ == []) with e' lt_;
            indexed_irred_history_independence e' (h'++lt');
            val_type_history_independence t h fs_e e'
          end)
      end
    end
  end*)

and io_exp_type_history_independence (t:qType) (h:history) (fs_e:fs_prod t) (e:closed_exp) :
  Lemma (requires t ⪾ (h, fs_e, e))
        (ensures forall h'. t ⪾ (h', fs_e, e))
        (decreases %[get_rel t;1]) =
  introduce forall h'. t ⪾ (h', fs_e, e) with begin
    introduce forall lt' (e':closed_exp). steps e e' h' lt' /\ indexed_irred e' (h'++lt') ==> (exists (fs_r:get_Type t). t ∋ (h'++lt', fs_r, e') /\ (forall p. theta fs_e h' p ==> p lt' fs_r)) with begin
      introduce steps e e' h' lt' /\ indexed_irred e' (h'++lt') ==> (exists (fs_r:get_Type t). t ∋ (h'++lt', fs_r, e') /\ (forall p. theta fs_e h' p ==> p lt' fs_r)) with _. begin
        FStar.Squash.bind_squash #(steps e e' h' lt') () (fun sts ->
          steps_history_independence sts;
          eliminate forall h_. exists lt_. steps e e' h_ lt_ with h;
          eliminate exists lt_. steps e e' h lt_
          returns (exists (fs_r:get_Type t). t ∋ (h'++lt', fs_r, e') /\ (forall p. theta fs_e h' p ==> p lt' fs_r)) with _. begin
            eliminate forall lt_ e_. steps e e_ h lt_ /\ indexed_irred e_ (h++lt_) ==> (exists (fs_r:get_Type t). t ∋ (h++lt_, fs_r, e_) /\ (forall p. theta fs_e h p ==> p lt_ fs_r)) with lt_ e';
            indexed_irred_history_independence e' (h'++lt');
            eliminate exists (fs_r:get_Type t). t ∋ (h++lt_, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt_ fs_r)
            returns (exists (fs_r:get_Type t). t ∋ (h'++lt', fs_r, e') /\ (forall p. theta fs_e h' p ==> p lt' fs_r)) with _. begin
              val_type_history_independence t (h++lt_) fs_r e';
              //theta_history_independence #(get_Type t) fs_e h lt_ fs_r;
              assume (forall p. theta fs_e h' p ==> p lt' fs_r);
              ()
            end
          end)
      end
    end
  end

let lem_values_in_exp_rel_are_in_val_rel t fs_e (e:value) :
  Lemma (requires forall h. t ⦂ (h, fs_e, e))
        (ensures  forall h. t ∋ (h, fs_e, e)) = admit () (** TODO **)

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

let safety_prod (#t:qType) (fs_e:fs_prod t) (e:exp) : Lemma
  (requires (equiv_prod fs_e e))
  (ensures safe e) =
  introduce forall (e':closed_exp) (h:history) (lt:local_trace h).
    steps e e' h lt ==> is_value e' \/ indexed_can_step e' (h++lt) with begin
    introduce steps e e' h lt ==> is_value e' \/ indexed_can_step e' (h++lt) with _. begin
      introduce indexed_irred e' (h++lt) ==> is_value e' with _. begin
        eliminate forall b (s:gsub empty b) (fsG:eval_env empty) (h:history).
          fsG `(∽) h` s ==> t ⪾ (h, fs_e, gsubst s e)
        with  true gsub_empty empty_eval h;
        assert (t ⪾ (h, fs_e, e));
        eliminate exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r)
        returns is_value e' with _. begin
          assert (t ∋ (h++lt, fs_r, e'));
          lem_values_are_values t (h++lt) fs_r e';
          assert (is_value e')
        end
      end
    end
  end

let sem_expr_shape_val (#t:qType) (fs_e:fs_val t) (e:closed_exp) (h:history) :
  Lemma (requires equiv_val fs_e e)
        (ensures indexed_sem_expr_shape (type_quotation_to_typ (get_rel t)) e h) =  admit ()

let sem_expr_shape_prod (#t:qType) (fs_e:fs_prod t) (e:closed_exp) (h:history) :
  Lemma (requires equiv_prod fs_e e)
        (ensures indexed_sem_expr_shape (type_quotation_to_typ (get_rel t)) e h) =
  introduce forall e' (lt:local_trace h). steps e e' h lt /\ indexed_irred e' (h++lt) ==> sem_value_shape (type_quotation_to_typ (get_rel t)) e' with begin
    introduce steps e e' h lt /\ indexed_irred e' (h++lt) ==> sem_value_shape (type_quotation_to_typ (get_rel t)) e' with _. begin
      eliminate forall b (s:gsub empty b) (fsG:eval_env empty) (h:history).
          fsG `(∽) h` s ==> t ⪾ (h, fs_e, gsubst s e)
      with  true gsub_empty empty_eval h;
      assert (t ⪾ (h, fs_e, e))
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
  (ensures (helper_lambda fs_body ≈ ELam body)) = admit ()
  (*lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  let f : fs_oval g (t1 ^-> t2) = fun fsG x -> fs_body (stack fsG x) in
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> (t1 ^-> t2) ⦂ (h, f fsG, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∋ (h++lt_v, fs_v, v) ==> t2 ⦂ (h++lt_v, f fsG fs_v, subst_beta v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fsG' = stack fsG fs_v in
          let h' = h++lt_v in
          eliminate forall b (s':gsub g' b) (fsG':eval_env g') h'. fsG' `(∽) h'` s' ==> t2 ⦂ (h', f (tail #t1 fsG') (hd #t1 #g fsG'), gsubst s' body)
            with false s' fsG' h';
          assert (fsG `(∽) h` s);
          assert (t1 ∋ (h++lt_v, fs_v, v));
          introduce forall (x:var). Some? (g x) ==> Some?.v (g x) ∋ (h++lt_v, index fsG x, s x) with begin
            introduce _ ==> _ with _. begin
              val_type_history_independence (Some?.v (g x)) h (index fsG x) (s x)
            end
          end;
          assert (stack fsG fs_v `(∽) h'` gsub_extend s t1 v);
          assert (t2 ⦂ (h', f (tail fsG') (hd fsG'), (gsubst s' body)));
          assert (hd (stack fsG fs_v) == fs_v);
          assert (t2 ⦂ (h', f (tail fsG') fs_v, (gsubst s' body)));
          assert (t2 ⦂ (h', f fsG fs_v, (gsubst s' body)));
          lem_substitution s t1 v body;
          assert (t2 ⦂ (h', f fsG fs_v, subst_beta v body'))
        end
      end;
      assert ((t1 ^-> t2) ∋ (h, f fsG, gsubst s (ELam body)));
      lem_values_are_expressions (t1 ^-> t2) h (f fsG) (gsubst s (ELam body));
      assert ((t1 ^-> t2) ⦂ (h, f fsG, gsubst s (ELam body)))
    end
  end*)

let unroll_elam (t1 t2:qType) (h:history) (fs_e1:fs_val (t1 ^-> t2)) (e11:exp)
  : Lemma (requires (is_closed (ELam e11)) /\ ((t1 ^-> t2) ∋ (h, fs_e1, ELam e11)))
          (ensures (forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∋ (h++lt_v, fs_v, v) ==> t2 ⦂ (h++lt_v, fs_e1 fs_v, subst_beta v e11))) = admit ()

let unroll_elam_io (t1 t2:qType) (h:history) (fs_e1:fs_val (t1 ^->!@ t2)) (e11:exp)
  : Lemma (requires (is_closed (ELam e11)) /\ ((t1 ^->!@ t2) ∋ (h, fs_e1, ELam e11)))
          (ensures (forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∋ (h++lt_v, fs_v, v) ==> t2 ⪾ (h++lt_v, fs_e1 fs_v, subst_beta v e11))) = admit ()

let unroll_elam_io' (t1 t2:qType) (fs_e1:fs_val (t1 ^->!@ t2)) (e11:exp)
  : Lemma (requires (is_closed (ELam e11)) /\ (forall h. (t1 ^->!@ t2) ∋ (h, fs_e1, ELam e11)))
          (ensures (forall h (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∋ (h++lt_v, fs_v, v) ==> t2 ⪾ (h++lt_v, fs_e1 fs_v, subst_beta v e11))) =
  introduce forall h. forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∋ (h++lt_v, fs_v, v) ==> t2 ⪾ (h++lt_v, fs_e1 fs_v, subst_beta v e11) with
    unroll_elam_io t1 t2 h fs_e1 e11


#push-options "--z3rlimit 5000 --fuel 5000"
let equiv_app #g
  (#t1:qType) (#t2:qType)
  (fs_e1:fs_oval g (t1 ^-> t2)) (fs_e2:fs_oval g t1)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2)
    (ensures (helper_app fs_e1 fs_e2 ≈ EApp e1 e2)) =
  lem_fv_in_env_app g e1 e2;
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> t2 ⦂ (h, (fs_e1 fsG) (fs_e2 fsG), gsubst s (EApp e1 e2)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e2 = fs_e2 fsG in
    let fs_e = fs_e1 fs_e2 in
    let e = EApp (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EApp e1 e2) == e);
    let EApp e1 e2 = e in
    introduce fsG `(∽) h` s ==> t2 ⦂ (h, fs_e, e) with _. begin
      admit ()
      (*introduce forall (e':closed_exp) lt. steps e e' h lt /\ indexed_irred e' (h++lt) ==> (t2 ∋ (h, fs_e, e') /\ lt == []) with begin
        introduce steps e e' h lt /\ indexed_irred e' (h++lt) ==> (t2 ∋ (h, fs_e, e') /\ lt == []) with _. begin
          let steps_e_e' : squash (steps e e' h lt) = () in
          FStar.Squash.map_squash #_ #(squash (t2 ∋ (h, fs_e, e') /\ lt == [])) steps_e_e' (fun steps_e_e' ->
            exp_type_history_independence t1 h fs_e2 e2;
            exp_type_history_independence (t1 ^-> t2) h fs_e1 e1;
            safety_val #t1 fs_e2 e2;
            safety_val #(t1 ^-> t2) fs_e1 e1;
            sem_expr_shape_val #(t1 ^-> t2) fs_e1 e1 h;
            let t1_typ = type_quotation_to_typ (get_rel t1) in
            let t2_typ = type_quotation_to_typ (get_rel t2) in
            let (e11, e2', (| lt2, (| lt1, lt3 |) |)) = destruct_steps_eapp e1 e2 e' h lt steps_e_e' t1_typ t2_typ in
            eliminate forall e2' lt2. steps e2 e2' h lt2 /\ indexed_irred e2' (h++lt2) ==> (t1 ∋ (h, fs_e2, e2') /\ lt2 == []) with e2' lt2;
            lem_value_is_irred e2';
            assert (t1 ∋ (h, fs_e2, e2') /\ lt2 == []);
            eliminate forall e1' lt1. steps e1 e1' h lt1 /\ indexed_irred e1' (h++lt1) ==> ((t1 ^-> t2) ∋ (h, fs_e1, e1') /\ lt1 == []) with (ELam e11) lt1;
            lem_value_is_irred (ELam e11);
            assert ((t1 ^-> t2) ∋ (h, fs_e1, ELam e11) /\ lt1 == []);
            unroll_elam t1 t2 h fs_e1 e11;
            assert (t2 ⦂ (h, fs_e, subst_beta e2' e11));
            assert (t2 ∋ (h, fs_e, e')))
        end
      end*)
    end
  end
#pop-options

let equiv_if_steps #g (#e #e':closed_exp) (#h:history) (#lt:local_trace h) (sts:squash (steps e e' h lt)) (e1 e2 e3:closed_exp) (#t:qType) (fs_e:fs_val t) (fs_e1:fs_oval g qBool) (fs_e2:fs_oval g t) (fs_e3:fs_oval g t) #b (s:gsub g b) (fsG:eval_env g) :
  Lemma (requires fsG `(∽) h` s /\
                  indexed_irred e' (h++lt) /\
                  fs_e1 ≈ e1 /\ fs_e2 ≈ e2 /\ fs_e3 ≈ e3)
        (ensures t ∋ (h, fs_e, e') /\ lt == []) = admit ()
  (*FStar.Squash.map_squash #_ #(squash (t ∋ (h, fs_e, e') /\ lt == [])) sts (fun sts ->
    exp_type_history_independence qBool h (fs_e1 fsG) e1;
    safety_val #qBool (fs_e1 fsG) e1;
    sem_expr_shape_val #qBool (fs_e1 fsG) e1 h;
    admit ()
  )*)

let equiv_if #g
  (#t:qType)
  (fs_e1:fs_oval g qBool) (fs_e2:fs_oval g t) (fs_e3:fs_oval g t)
  (e1:exp) (e2:exp) (e3:exp)
  : Lemma
    (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2 /\ fs_e3 ≈ e3)
    (ensures helper_if fs_e1 fs_e2 fs_e3 ≈ EIf e1 e2 e3) = admit ()
  (*lem_fv_in_env_if g e1 e2 e3;
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> t ⦂ (h, (if fs_e1 fsG then fs_e2 fsG else fs_e3 fsG), gsubst s (EIf e1 e2 e3)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e2 = fs_e2 fsG in
    let fs_e3 = fs_e3 fsG in
    let fs_e = if fs_e1 then fs_e2 else fs_e3 in
    let e = EIf (gsubst s e1) (gsubst s e2) (gsubst s e3) in
    assert (gsubst s (EIf e1 e2 e3) == e);
    let EIf e1 e2 e3 = e in
    introduce fsG `(∽) h` s ==> t ⦂ (h, fs_e, e) with _. begin
      introduce forall (e':closed_exp) lt. steps e e' h lt /\ indexed_irred e' (h++lt) ==> (t ∋ (h, fs_e, e') /\ lt == []) with begin
        introduce steps e e' h lt /\ indexed_irred e' (h++lt) ==> (t ∋ (h, fs_e, e') /\ lt == []) with _. begin
          let steps_e_e' : squash (steps e e' h lt) = () in
          FStar.Squash.map_squash #_ #(squash (t ∋ (h, fs_e, e') /\ lt == [])) steps_e_e' (fun steps_e_e' ->
            exp_type_history_independence qBool h fs_e1 e1;
            exp_type_history_independence t h fs_e2 e2;
            exp_type_history_independence t h fs_e3 e3;
            safety_val #qBool fs_e1 e1;
            sem_expr_shape_val #qBool fs_e1 e1 h;
            let (e1', (| lt1, (lt2, lt3) |)) = destruct_steps_eif e1 e2 e3 e' h lt steps_e_e' in
            eliminate forall e1' lt1. steps e1 e1' h lt1 /\ indexed_irred e1' (h++lt1) ==> (qBool ∋ (h, fs_e1, e1') /\ lt1 == []) with e1' lt1;
            assert (qBool ∋ (h, fs_e1, e1') /\ lt1 == []);
            assert (ETrue? e1' ==> (steps e2 e' (h++lt1) lt2 /\ lt == lt1 @ lt2));
            eliminate forall e' lt2. steps e2 e' h lt2 /\ indexed_irred e' (h++lt2) ==> (t ∋ (h, fs_e2, e') /\ lt2 == []) with e' lt2;
            assert (EFalse? e1' ==> (steps e3 e' (h++lt1) lt3 /\ lt == lt1 @ lt3));
            //eliminate forall e' lt3. steps e3 e' h lt3 /\ indexed_irred e' (h++lt3) ==> (t ∋ (h, fs_e3, e') /\ lt3 == []) with e' lt3;
            admit ()
          )
        end
      end
    end
  end*)

let equiv_pair #g
  (#t1 #t2:qType)
  (fs_e1:fs_oval g t1) (fs_e2:fs_oval g t2)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2)
    (ensures helper_pair fs_e1 fs_e2 ≈ EPair e1 e2) = admit ()
  (*lem_fv_in_env_pair g e1 e2;
  let t = t1 ^* t2 in
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==>  t ⦂ (h, (fs_e1 fsG, fs_e2 fsG), gsubst s (EPair e1 e2)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e2 = fs_e2 fsG in
    let fs_e = (fs_e1, fs_e2) in
    let e = EPair (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EPair e1 e2) == e);
    let EPair e1 e2 = e in
    introduce fsG `(∽) h` s ==>  t ⦂ (h, fs_e, e) with _. begin
      introduce forall (e':closed_exp) lt. steps e e' h lt /\ indexed_irred e' (h++lt) ==> (t ∋ (h, fs_e, e') /\ lt == []) with begin
        introduce _ ==> (t ∋ (h, fs_e, e') /\ lt == []) with _. begin
          let steps_e_e' : squash (steps e e' h lt) = () in
          FStar.Squash.map_squash #_ #(squash (t ∋ (h, fs_e, e') /\ lt == [])) steps_e_e' (fun steps_e_e' ->
            exp_type_history_independence t1 h fs_e1 e1;
            exp_type_history_independence t2 h fs_e2 e2;
            safety_val #t1 fs_e1 e1;
            safety_val #t2 fs_e2 e2;
            let (e1', e2', (| lt1, (| lt2, lt3 |) |)) = destruct_steps_epair e1 e2 e' h lt steps_e_e' in
            lem_value_is_irred e1';
            lem_value_is_irred e2';
            assert (t1 ∋ (h, fs_e1, e1'));
            assert (t2 ∋ (h, fs_e2, e2'));
            assert (t ∋ (h, fs_e, EPair e1' e2'));
            lem_values_are_expressions t h fs_e (EPair e1' e2')
          )
        end
      end
    end*)

let equiv_pair_fst_app #g
  (#t1 #t2:qType)
  (fs_e12:fs_oval g (t1 ^* t2))
  (e12:exp)
  : Lemma
    (requires fs_e12 ≈ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures helper_fst fs_e12 ≈ (EFst e12)) = admit ()
  (*lem_fv_in_env_fst g e12;
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==>  t1 ⦂ (h, fst (fs_e12 fsG), gsubst s (EFst e12)) with begin
    let fs_e12 = fs_e12 fsG in
    let fs_e = fst fs_e12 in
    let e = EFst (gsubst s e12) in
    assert (gsubst s (EFst e12) == e);
    let EFst e12 = e in
    introduce fsG `(∽) h` s ==> t1 ⦂ (h, fs_e, e) with _. begin
      introduce forall (e':closed_exp) lt. steps e e' h lt /\ indexed_irred e' (h++lt) ==> (t1 ∋ (h, fs_e, e') /\ lt == []) with begin
        introduce steps e e' h lt /\ indexed_irred e' (h++lt) ==> (t1 ∋ (h, fs_e, e') /\ lt == []) with _. begin
          let steps_e_e' : squash (steps e e' h lt) = () in
          FStar.Squash.map_squash #_ #(squash (t1 ∋ (h, fs_e, e') /\ lt == [])) steps_e_e' (fun steps_e_e' ->
            exp_type_history_independence (t1 ^* t2) h fs_e12 e12;
            safety_val #(t1 ^* t2) fs_e12 e12;
            sem_expr_shape_val #(t1 ^* t2) fs_e12 e12 h;
            let t1_typ = type_quotation_to_typ (get_rel t1) in
            let t2_typ = type_quotation_to_typ (get_rel t2) in
            let (e12', (| lt12, lt_f |)) = destruct_steps_epair_fst e12 e' h lt steps_e_e' t1_typ t2_typ in
            lem_value_is_irred e12';
            assert ((t1 ^* t2) ⦂ (h, fs_e12, e12));
            eliminate forall e12' lt12. steps e12 e12' h lt12 /\ indexed_irred e12' (h++lt12) ==> ((t1 ^* t2) ∋ (h, fs_e12, e12') /\ lt12 == []) with e12' lt12;
            assert ((t1 ^* t2) ∋ (h, fs_e12, e12') /\ lt12 == []);
            let EPair e1' e2' = e12' in
            lem_value_is_irred e1';
            lem_value_is_irred e2';
            assert (t1 ∋ (h, fs_e, e1'));
            lem_destruct_steps_epair_fst e1' e2' e' h lt_f;
            assert (t1 ∋ (h, fs_e, e')))
        end
      end
    end
  end*)

let equiv_pair_snd_app #g (#t1 #t2:qType) (fs_e12:fs_oval g (t1 ^* t2)) (e12:exp)
  : Lemma
    (requires fs_e12 ≈ e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures helper_snd fs_e12 ≈ (ESnd e12)) = admit ()
  (*lem_fv_in_env_snd g e12;
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> t2 ⦂ (h, snd (fs_e12 fsG), gsubst s (ESnd e12)) with begin
    let fs_e12 = fs_e12 fsG in
    let fs_e = snd fs_e12 in
    let e = ESnd (gsubst s e12) in
    assert (gsubst s (ESnd e12) == e);
    let ESnd e12 = e in
    introduce fsG `(∽) h` s ==> t2 ⦂ (h, fs_e, e) with _. begin
      introduce forall (e':closed_exp) lt. steps e e' h lt /\ indexed_irred e' (h++lt) ==> (t2 ∋ (h, fs_e, e') /\ lt == []) with begin
        introduce steps e e' h lt /\ indexed_irred e' (h++lt) ==> (t2 ∋ (h, fs_e, e') /\ lt == []) with _. begin
          let steps_e_e' : squash (steps e e' h lt) = () in
          FStar.Squash.map_squash #_ #(squash (t2 ∋ (h, fs_e, e') /\ lt == [])) steps_e_e' (fun steps_e_e' ->
            exp_type_history_independence (t1 ^* t2) h fs_e12 e12;
            safety_val #(t1 ^* t2) fs_e12 e12;
            sem_expr_shape_val #(t1 ^* t2) fs_e12 e12 h;
            let t1_typ = type_quotation_to_typ (get_rel t1) in
            let t2_typ = type_quotation_to_typ (get_rel t2) in
            let (e12', (| lt12, lt_f |)) = destruct_steps_epair_snd e12 e' h lt steps_e_e' t1_typ t2_typ in
            lem_value_is_irred e12';
            assert ((t1 ^* t2) ⦂ (h, fs_e12, e12));
            eliminate forall e12' lt12. steps e12 e12' h lt12 /\ indexed_irred e12' (h++lt12) ==> ((t1 ^* t2) ∋ (h, fs_e12, e12') /\ lt12 == []) with e12' lt12;
            assert ((t1 ^* t2) ∋ (h, fs_e12, e12') /\ lt12 == []);
            let EPair e1' e2' = e12' in
            lem_value_is_irred e1';
            lem_value_is_irred e2';
            assert (t2 ∋ (h, fs_e, e2'));
            lem_destruct_steps_epair_snd e1' e2' e' h lt_f;
            assert (t2 ∋ (h, fs_e, e')))
        end
      end
    end
  end*)

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
    (requires fs_body `equiv_oprod t2` body)
    (ensures helper_lambda_prod fs_body `equiv_oval (t1 ^->!@ t2)` (ELam body)) = admit ()
  (*lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  let f : fs_oval g (t1 ^->!@ t2) = fun fsG x -> fs_body (stack fsG x) in
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> (t1 ^->!@ t2) ⦂ (h, f fsG, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∋ (h++lt_v, fs_v, v) ==> t2 ⪾ (h++lt_v, (f fsG) fs_v, subst_beta v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fsG' = stack fsG fs_v in
          let h' = h++lt_v in
          eliminate forall b (s':gsub g' b) (fsG':eval_env g') h'. fsG' `(∽) h'` s' ==> t2 ⪾ (h', f (tail #t1 fsG') (hd #t1 #g fsG'), gsubst s' body)
            with false s' fsG' h';
          assert (fsG `(∽) h` s);
          assert (t1 ∋ (h++lt_v, fs_v, v));
          introduce forall (x:var). Some? (g x) ==> Some?.v (g x) ∋ (h++lt_v, index fsG x, s x) with begin
            introduce _ ==> _ with _. begin
              val_type_history_independence (Some?.v (g x)) h (index fsG x) (s x)
            end
          end;
          assert (stack fsG fs_v `(∽) h'` gsub_extend s t1 v);
          assert (t2 ⪾ (h', f (tail fsG') (hd fsG'), gsubst s' body));
          assert (hd (stack fsG fs_v) == fs_v);
          assert (t2 ⪾ (h', f (tail fsG') fs_v, gsubst s' body));
          assert (t2 ⪾ (h', f fsG fs_v, gsubst s' body));
          lem_substitution s t1 v body;
          assert (t2 ⪾ (h', f fsG fs_v, subst_beta v body'))
        end
      end;
      assert ((t1 ^->!@ t2) ∋ (h, f fsG, gsubst s (ELam body)));
      lem_values_are_expressions (t1 ^->!@ t2) h (f fsG) (gsubst s (ELam body));
      assert ((t1 ^->!@ t2) ⦂ (h, f fsG, gsubst s (ELam body)))
    end
  end*)

let equiv_oprod_read g
  : Lemma
    (requires True)
    (ensures (fun fsG -> read ()) `equiv_oprod #g (qResexn qBool)` ERead)
  = admit ()
  //introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> 

let equiv_oprod_write #g (fs_arg:fs_oval g qBool) (arg:exp)
  : Lemma
    (requires fs_arg ≈ arg)
    (ensures (fun fsG -> write (fs_arg fsG)) `equiv_oprod #g (qResexn qUnit)` EWrite arg)
  = admit ()

let equiv_oprod_return #g (#t:qType) (fs_x:fs_oval g t) (x:exp)
  : Lemma
    (requires fs_x ≈ x)
    (ensures helper_return_prod fs_x `equiv_oprod t` x) =
  assume (fv_in_env g x);
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> t ⪾ (h, return (fs_x fsG), gsubst s x) with begin
    introduce _ ==> _ with _. begin
      let e = gsubst s x in
      let fs_e = return (fs_x fsG) in
      introduce forall (lt:local_trace h) (e':closed_exp). steps e e' h lt /\ indexed_irred e' (h++lt) ==> (exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r)) with begin
        introduce steps e e' h lt /\ indexed_irred e' (h++lt) ==> (exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r)) with _. begin
        assert (t ⦂ (h, fs_x fsG, e));
        eliminate forall e' lt'. steps e e' h lt' /\ indexed_irred e' (h++lt') ==> (t ∋ (h, fs_x fsG, e') /\ lt' == [] /\ (forall p. p lt (fs_x fsG))) with e' lt
        end
      end
    end
  end

#push-options "--z3rlimit 5000 --fuel 5000"
let equiv_oprod_bind #g (#a #b:qType) (fs_m:fs_oprod g a) (fs_k:fs_oprod (extend a g) b) (m k:exp)
  : Lemma
    (requires fs_m `equiv_oprod a` m /\ fs_k `equiv_oprod b` k)
    (ensures (helper_bind_prod fs_m fs_k) `equiv_oprod b` (EApp (ELam k) m)) =
  assume (fv_in_env (extend a g) k);
  assume (fv_in_env g (ELam k));
  assume (fv_in_env g m);
  lem_fv_in_env_app g (ELam k) m;
  assert (fs_k `equiv_oprod b` k);
  equiv_lam_prod fs_k k;
  let fs_k' : fs_oval g (a ^->!@ b) = fun fsG x -> fs_k (stack fsG x) in
  assert (fs_k' `equiv_oval (a ^->!@ b)` (ELam k));
  introduce forall b' (s:gsub g b') fsG h. fsG `(∽) h` s ==> b ⪾ (h, io_bind (fs_m fsG) (fun x -> fs_k (stack fsG x)), gsubst s (EApp (ELam k) m)) with begin
    let fs_m = fs_m fsG in
    let fs_k' = fs_k' fsG in
    let fs_e = io_bind fs_m (fun x -> fs_k (stack fsG x)) in
    let k' = subst (sub_elam s) k in
    assert (gsubst s (ELam k) == ELam k');
    let e = EApp (ELam k') (gsubst s m) in
    assert (gsubst s (EApp (ELam k) m) == e);
    let EApp (ELam k') m = e in
    introduce fsG `(∽) h` s ==> b ⪾ (h, fs_e, e) with _. begin
      //assert (fv_in_env g (ELam k) /\ forall b' (s:gsub g b') (fsG:eval_env g) (h:history). fsG `(∽) h` s ==> (a ^->!@ b) ⦂ (h, fs_k' fsG, gsubst s (ELam k))); -- why does this fail?
      assume ((a ^->!@ b) ⦂ (h, fs_k', ELam k'));
      introduce forall lt (e':closed_exp). steps e e' h lt /\ indexed_irred e' (h++lt) ==> (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r)) with begin
        introduce steps e e' h lt /\ indexed_irred e' (h++lt) ==> (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r)) with _. begin
          let steps_e_e' : squash (steps e e' h lt) = () in
          FStar.Squash.map_squash #_ #(squash (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r))) steps_e_e' (fun steps_e_e' ->
            io_exp_type_history_independence a h fs_m m;
            exp_type_history_independence (a ^->!@ b) h fs_k' (ELam k');
            safety_prod #a fs_m m;
            safety_val #(a ^->!@ b) fs_k' (ELam k');
            sem_expr_shape_val #(a ^->!@ b) fs_k' (ELam k') h;
            let a_typ = type_quotation_to_typ (get_rel a) in
            let b_typ = type_quotation_to_typ (get_rel b) in
            lem_value_is_irred (ELam k');
            let (k1, m', (| lt2, (| lt1, lt3 |) |)) = destruct_steps_eapp (ELam k') m e' h lt steps_e_e' a_typ b_typ in
            assert (indexed_irred (ELam k') h ==> (lt1 == [] /\ (ELam k') == (ELam k1)));
            assert (lt1 == [] /\ (ELam k') == (ELam k1));
            assert (a ⪾ (h, fs_m, m));
            assert (forall lt2 m'. steps m m' h lt2 /\ indexed_irred m' (h++lt2) ==> (exists (fs_r:get_Type a). a ∋ (h++lt2, fs_r, m') /\ (forall p. theta fs_m h p ==> p lt2 fs_r)));
            lem_value_is_irred m';
            eliminate exists (fs_r:get_Type a). a ∋ (h++lt2, fs_r, m') /\ (forall p. theta fs_m h p ==> p lt2 fs_r)
            returns exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r) with _. begin
              assert (steps (ELam k') (ELam k1) (h++lt2) lt1);
              FStar.Squash.bind_squash #(steps (ELam k') (ELam k1) (h++lt2) lt1) () (fun sts ->
              steps_history_independence sts;
              eliminate forall h_. exists lt_. steps (ELam k') (ELam k1) h_ lt_ with h;
              eliminate exists lt_. steps (ELam k') (ELam k1) h lt_
              returns exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r) with _. begin
                assume (lt1 == lt_);
                assert (steps (ELam k') (ELam k1) h lt1);
                lem_value_is_irred (ELam k1);
                assert (indexed_irred (ELam k1) (h++lt1));
                //((a ^->!@ b) ⦂ (h, fs_k', ELam k'))
                eliminate forall e' lt. steps (ELam k') e' h lt /\ indexed_irred e' (h++lt) ==> ((a ^->!@ b) ∋ (h, fs_k', e') /\ lt1 == [] /\ (forall p. p lt1 fs_k')) with (ELam k1) lt1;
                assert ((a ^->!@ b) ∋ (h, fs_k', (ELam k1)) /\ lt1 == [] /\ (forall p. p lt1 fs_k'));
                unroll_elam_io a b h fs_k' k1;
                assert (b ⪾ (h++lt2, fs_k' fs_r, subst_beta m' k1));
                //assert (fs_k' fs_r == 
                //assert (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ (forall p. theta 
                admit ()
              end)
            end
            (*
            FStar.Squash.bind_squash #(steps (ELam k') (ELam k1) (h++lt2) lt1) () (fun sts ->
              steps_history_independence sts;
              eliminate forall h_. exists lt_. steps (ELam k') (ELam k1) h_ lt_ with h;
              eliminate exists lt_. steps (ELam k') (ELam k1) h lt_
              returns (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r)) with _. begin
                assume (lt1 == lt_);
                assert (steps (ELam k') (ELam k1) h lt1);
                lem_value_is_irred (ELam k1);
                assert (indexed_irred (ELam k1) (h++lt1));
                //((a ^->!@ b) ⦂ (h, fs_k', ELam k'))
                eliminate forall e' lt. steps (ELam k') e' h lt /\ indexed_irred e' (h++lt) ==> ((a ^->!@ b) ∋ (h, fs_k', e') /\ lt1 == [] /\ (forall p. p lt1 fs_k')) with (ELam k1) lt1;
                assert ((a ^->!@ b) ∋ (h, fs_k', (ELam k1)) /\ lt1 == [] /\ (forall p. p lt1 fs_k'));
                unroll_elam_io a b h fs_k' k1;
                assert (b ⪾ (h, fs_e, subst_beta m' k1));
                //assert (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r));
                admit ()
              end*)
            (*eliminate forall elam_k lt1. steps (ELam k') elam_k h lt1 /\ indexed_irred elam_k (h++lt1) ==> ((a ^->!@ b) ∋ (h, fs_k', elam_k) /\ lt1 == [] /\ (forall p. p lt1 fs_k')) with (ELam k1) lt1; // this requires m to not be an IO computation, which is not given to us by the premise*)
            //admit ()
          )
        end
      end
    end
  end
#pop-options

//#push-options "--z3rlimit 5000 --fuel 5000"
let equiv_oprod_app #g (#a #b:qType) (fs_f:fs_oval g (a ^->!@ b)) (fs_x:fs_oval g a) (f x:exp)
  : Lemma
    (requires fs_f ≈ f /\ fs_x ≈ x)
    (ensures (helper_app_prod fs_f fs_x) `equiv_oprod b` (EApp f x)) =
  lem_fv_in_env_app g f x;
  introduce forall b' (s:gsub g b') fsG h. fsG `(∽) h` s ==> b ⪾ (h, (fs_f fsG) (fs_x fsG), gsubst s (EApp f x)) with begin
    let fs_f = fs_f fsG in
    let fs_x = fs_x fsG in
    let fs_e = fs_f fs_x in
    let e = EApp (gsubst s f) (gsubst s x) in
    assert (gsubst s (EApp f x) == e);
    let EApp f x = e in
    introduce fsG `(∽) h` s ==> b ⪾ (h, fs_e, e) with _. begin
      introduce forall lt (e':closed_exp). steps e e' h lt /\ indexed_irred e' (h++lt) ==> (exists (fs_r:get_Type b). b  ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r)) with begin
        introduce _ ==> (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r)) with _. begin
          let steps_e_e' : squash (steps e e' h lt) = () in
          FStar.Squash.map_squash #_ #(squash (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r))) steps_e_e' (fun steps_e_e' ->
            exp_type_history_independence a h fs_x x;
            exp_type_history_independence (a ^->!@ b) h fs_f f;
            safety_val #a fs_x x;
            safety_val #(a ^->!@ b) fs_f f;
            sem_expr_shape_val #(a ^->!@ b) fs_f f h;
            let a_typ = type_quotation_to_typ (get_rel a) in
            let b_typ = type_quotation_to_typ (get_rel b) in
            let (f1, x', (| lt2, (| lt1, lt3 |) |)) = destruct_steps_eapp f x e' h lt steps_e_e' a_typ b_typ in
            assert (a ⦂ (h, fs_x, x));
            assert (forall x' lt2. steps x x' h lt2 /\ indexed_irred x' (h++lt2) ==> (a ∋ (h, fs_x, x') /\ lt2 == [] /\ (forall p. p lt2 fs_x)));
            lem_value_is_irred x';
            assert (a ∋ (h, fs_x, x') /\ lt2 == [] /\ (forall p. p lt2 fs_x));
            eliminate forall f' lt1. steps f f' h lt1 /\ indexed_irred f' (h++lt1) ==> ((a ^->!@ b) ∋ (h, fs_f, f') /\ lt1 == [] /\ (forall p. p lt1 fs_f)) with (ELam f1) lt1;
            lem_value_is_irred (ELam f1);
            assert ((a ^->!@ b) ∋ (h, fs_f, (ELam f1)) /\ lt1 == [] /\ (forall p. p lt1 fs_f));
            unroll_elam_io a b h fs_f f1;
            assert (b ⪾ (h, fs_e, subst_beta x' f1));
            assert (exists (fs_r:get_Type b). b ∋ (h++lt, fs_r, e') /\ (forall p. theta fs_e h p ==> p lt fs_r)))
        end
      end
    end
  end
//#pop-options

#push-options "--z3rlimit 5000 --fuel 5000"
let equiv_oprod_if #g (#a:qType) (fs_c:fs_oval g qBool) (fs_t fs_e:fs_oprod g a) (c t e:exp)
  : Lemma
    (requires fs_c ≈ c /\ fs_t `equiv_oprod a` t /\ fs_e `equiv_oprod a` e)
    (ensures (helper_if_prod fs_c fs_t fs_e) `equiv_oprod a` (EIf c t e)) =
  lem_fv_in_env_if g c t e;
  introduce forall b' (s:gsub g b') fsG h. fsG `(∽) h` s ==> a ⪾ (h, (if (fs_c fsG) then (fs_t fsG) else (fs_e fsG)), gsubst s (EIf c t e)) with begin
    let fs_c = fs_c fsG in
    let fs_t = fs_t fsG in
    let fs_e = fs_e fsG in
    let fs_ex = if fs_c then fs_t else fs_e in
    let ex = EIf (gsubst s c) (gsubst s t) (gsubst s e) in
    assert (gsubst s (EIf c t e) == ex);
    let EIf c t e = ex in
    introduce fsG `(∽) h` s ==> a ⪾ (h, fs_ex, ex) with _. begin
      introduce forall lt (ex':closed_exp). steps ex ex' h lt /\ indexed_irred ex' (h++lt) ==> (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, ex') /\ (forall p. theta fs_ex h p ==> p lt fs_r)) with begin
        introduce steps ex ex' h lt /\ indexed_irred ex' (h++lt) ==> (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, ex') /\ (forall p. theta fs_ex h p ==> p lt fs_r)) with _. begin
          let steps_e_e' : squash (steps ex ex' h lt) = () in
          FStar.Squash.map_squash #_ #(squash (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, ex') /\ (forall p. theta fs_ex h p ==> p lt fs_r))) steps_e_e' (fun steps_e_e' ->
            exp_type_history_independence qBool h fs_c c;
            io_exp_type_history_independence a h fs_t t;
            io_exp_type_history_independence a h fs_e e;
            safety_val #qBool fs_c c;
            sem_expr_shape_val #qBool fs_c c h;
            let (c', (| lt1, (lt2, lt3) |)) = destruct_steps_eif c t e ex' h lt steps_e_e' in
            assert (qBool ⦂ (h, fs_c, c));
            assert (forall c' lt1. steps c c' h lt1 /\ indexed_irred c' (h++lt1) ==> (qBool ∋ (h, fs_c, c') /\ lt1 == [] /\ (forall p. p lt1 fs_c)));
            assert (qBool ∋ (h, fs_c, c') /\ lt1 == [] /\ (forall p. p lt1 fs_c));
            assert (ETrue? c' ==> (steps t ex' (h++lt1) lt2 /\ lt == lt1 @ lt2));
            assert (a ⪾ (h, fs_t, t));
            //assert (forall t' lt. steps t t' h lt /\ indexed_irred t' (h++lt) ==> (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, t') /\ (forall p. theta fs_t h p ==> p lt fs_r))); 
            //assert (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, ex') /\ (forall p. theta fs_t h p ==> p lt fs_r));
            admit ()
          )
        end
      end
    end
  end
#pop-options


let equiv_oprod_case #g (#a #b #c:qType) (fs_cond:fs_oval g (a ^+ b)) (fs_inlc:fs_oprod (extend a g) c) (fs_inrc:fs_oprod (extend b g) c) (cond inlc inrc:exp)
  : Lemma
    (requires fs_cond ≈ cond /\ fs_inlc `equiv_oprod c` inlc /\ fs_inrc `equiv_oprod c` inrc)
    (ensures (helper_case_prod fs_cond fs_inlc fs_inrc) `equiv_oprod c` (ECase cond inlc inrc))
  = admit ()


     (*assert (qBool ⦂ (h, fs_c, c));
      assert (forall c'. steps c c' h [] /\ indexed_irred c' h ==> qBool ∋ (h, fs_c, c'));
      assert (a ⪾ (h, fs_t fsG, t));
      assume (forall lt t'. steps t t' h lt /\ indexed_irred t' (h++lt) ==> (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, t') /\ (forall p. theta (fs_t fsG) h p ==> p lt fs_r)));
      assert (a ⪾ (h, fs_e fsG, e));
      assume (forall lt e'. steps e e' h lt /\ indexed_irred e' (h++lt) ==> (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, e') /\ (forall p. theta (fs_t fsG) h p ==> p lt fs_r)));
      introduce forall lt (ex':closed_exp). steps ex ex' h lt /\ indexed_irred ex' (h++lt) ==> (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, ex') /\ (forall p. theta fs_ex h p ==> p lt fs_r)) with begin
        introduce _ ==> (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, ex') /\ (forall p. theta fs_ex h p ==> p lt fs_r)) with _. begin
          //FStar.Squash.bind_squash #(steps ex ex' h lt) () (fun sts ->
            //exp_type_history_independence qBool h fs_c c;
            //io_exp_type_history_independence a h (fs_t fsG) t;
            //io_exp_type_history_independence a h (fs_e fsG) e;
            //safety_val #qBool fs_c c;
            //sem_expr_shape_val #qBool fs_c c h;
            //let (c', (| lt1, (lt2, lt3) |)) = destruct_steps_eif c t e ex' h lt sts in
            //assume (exists (fs_r:get_Type a). a ∋ (h++lt, fs_r, ex') /\ (forall p. theta fs_ex h p ==> p lt fs_r));
            admit ()
        end
      end
    end
  end*)
