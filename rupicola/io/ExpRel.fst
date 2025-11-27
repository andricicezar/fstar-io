module ExpRel

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open QTyp
open IO
open Trace

type io_cexp (t:qType) =
  io (get_Type t)

let io_oexp (g:typ_env) (t:qType) =
  eval_env g -> io (get_Type t)

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __closed terms__. **)
let rec (∋) (t:qType) (p:(history * (get_Type t) * closed_exp)) : Tot Type0 (decreases %[get_rel t;0]) =
  let (h, fs_v, e) = p in
  match get_rel t with // way to "match" on F* types
  | QUnit -> fs_v == () /\ e == EUnit
  | QBool -> (fs_v == true /\ e == ETrue) \/ (fs_v == false /\ e == EFalse)
  | QArr #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> t2 = fs_v in
    match e with
    | ELam e' ->
      (forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∋ (h++lt_v, fs_v, v) ==>
        pack qt2 ∶(h++lt_v, fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
  | QArrIO #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> io t2 = fs_v in
    match e with
    | ELam e' -> // instead quantify over h'' - extensions of the history
      (forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∋ (h++lt_v, fs_v, v) ==>
        pack qt2 ⦂ (h++lt_v, fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
  | QPair #t1 #t2 qt1 qt2 -> begin
    match e with
    | EPair e1 e2 -> (** e1 and e2 are values. no need to quantify over lts **)
        pack qt1 ∋ (h, fst #t1 #t2 fs_v, e1) /\ pack qt2 ∋ (h, snd #t1 #t2 fs_v, e2)
    | _ -> False
  end
                           (** vvvvvvvvvv defined over F* values **)
and (∶) (t:qType) (p:history * get_Type t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
  let (h, fs_e, e) = p in
  forall (e':closed_exp).
    steps e e' h [] ==> irred e' h ==>
    t ∋ (h, fs_e, e')
                           (** vvvvvvvvvv defined over IO computations **)
and (⦂) (t:qType) (p:history * io_cexp t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
  let (h, fs_e, e) = p in
  forall lt (e':closed_exp).
    steps e e' h lt ==> irred e' (h++lt) ==>
    (exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e'))// /\ (forall p. theta fs_e h p ==> p lt fs_r))
                           (** TODO: ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ check this **)

(**  forall lt fs_r.
    (forall p. theta fs_e h p ==> p lt fs_r) ==>
      (forall (e':closed_exp). steps e e' h lt ==>  t ∋ (h++lt, fs_r, e'))**)

(** Section 8.1: https://www.cs.uoregon.edu/research/summerschool/summer24/lectures/Ahmed.pdf **)

let lem_values_are_expressions t h fs_e e : (** lemma used by Amal **)
  Lemma (requires t ∋ (h, fs_e, e))
        (ensures  t ⦂ (h, io_return fs_e, e)) = admit ()

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
let equiv (#g:typ_env) (t:qType) (fs_e:io_oexp g t) (e:exp) : Type0 =
  fv_in_env g e /\
  forall b (s:gsub g b) (fsG:eval_env g) (h:history).
    fsG `(∽) h` s ==> t ⦂ (h, fs_e fsG, gsubst s e)

let equiv_closed (#t:qType) (fs_e:io_cexp t) (e:closed_exp) : Type0 =
  equiv #empty t (fun _ -> fs_e) e

let safety (#t:qType) (fs_e:io_cexp t) (e:closed_exp) : Lemma
  (requires equiv_closed fs_e e)
  (ensures (forall h. safe e h)) =
  introduce forall h (e':closed_exp) (lt:local_trace h).
    steps e e' h lt ==> is_value e' \/ can_step e' (h++lt) with begin
    introduce steps e e' h lt ==> is_value e' \/ can_step e' (h++lt) with _. begin
      introduce irred e' (h++lt) ==> is_value e' with _. begin
        eliminate forall b (s:gsub empty b) (fsG:eval_env empty) (h:history).
          fsG `(∽) h` s ==> t ⦂ (h, fs_e, gsubst s e)
        with  true gsub_empty empty_eval h;
        assert (t ⦂ (h, fs_e, e));
        eliminate exists fs_r. t ∋ (h++lt, fs_r, e') ///\ (forall p. theta fs_e h p ==> p lt fs_r)
        returns is_value e' with _. begin
          assert (t ∋ (h++lt, fs_r, e'));
          lem_values_are_values t (h++lt) fs_r e';
          assert (is_value e')
        end
      end
    end
  end

let (≈) (#g:typ_env) (#t:qType) (fs_v:io_oexp g t) (e:exp) : Type0 =
  equiv #g t fs_v e

(** Equiv closed terms **)
let equiv_closed_terms (#t:qType) (fs_e:io_cexp t) (e:closed_exp) :
  Lemma (requires equiv #empty t (fun _ -> fs_e) e)
        (ensures (forall h. t ⦂ (h, fs_e, e))) =
  eliminate forall b (s:gsub empty b) (fsG:eval_env empty). forall (h:history).
    fsG `(∽) h` s ==> t ⦂ (h, (fun _ -> fs_e) fsG, gsubst s e) with true gsub_empty empty_eval

let lem_equiv_exp_are_equiv (g:typ_env) (#t:qType) (fs_e:io_cexp t) (e:closed_exp) :
  Lemma (requires (forall h. t ⦂ (h, fs_e, e)))
        (ensures equiv #empty t (fun _ -> fs_e) e) =
  introduce forall b (s:gsub empty b) (fsG:eval_env empty) (h':history).
    fsG `(∽) h'` s ==> t ⦂ (h', (fun _ -> fs_e) fsG, gsubst s e) with begin
    introduce fsG `(∽) h'` s ==> t ⦂ (h', (fun _ -> fs_e) fsG, gsubst s e) with _. begin
      assert (gsubst s e == e);
      assert ((fun _ -> fs_e) fsG == fs_e);
      eliminate forall h. t ⦂ (h, fs_e, e) with h'
    end
  end

(** Rules **)

let equiv_unit g
  : Lemma ((fun (_:eval_env g) -> io_return ()) `equiv qUnit` EUnit)
  =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qUnit ⦂ (h, io_return (), gsubst s EUnit) with begin
    introduce _ ==> _ with _. begin
      assert (qUnit ∋ (h, (), EUnit));
      lem_values_are_expressions qUnit h () EUnit
    end
  end

let equiv_true g
  : Lemma ((fun (_:eval_env g) -> io_return true) `equiv qBool` ETrue)
  =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qBool ⦂ (h, io_return true, gsubst s ETrue) with begin
    introduce _ ==> _ with _. begin
      assert (qBool ∋ (h, true, ETrue));
      lem_values_are_expressions qBool h true ETrue
    end
  end

let equiv_false g
  : Lemma ((fun (_:eval_env g) -> io_return false) `equiv qBool` EFalse)
  =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> qBool ⦂ (h, io_return false, gsubst s EFalse) with begin
    introduce _ ==> _ with _. begin
      assert (qBool ∋ (h, false, EFalse));
      lem_values_are_expressions qBool h false EFalse
    end
  end

let equiv_var g (x:var{Some? (g x)})
  : Lemma ((fun (fsG:eval_env g) -> io_return (index fsG x)) ≈ EVar x)
  =
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> Some?.v (g x) ⦂ (h, io_return (index fsG x), gsubst s (EVar x)) with begin
    introduce _ ==> _ with _. begin
      assert (Some?.v (g x) ∋ (h, index fsG x, s x));
      lem_values_are_expressions (Some?.v (g x)) h (index fsG x) (s x)
    end
  end

//#push-options "--split_queries always --fuel 3000 --z3rlimit 32"
let equiv_lam #g (t1:qType) (t2:qType) (f:io_oexp g (t1 ^-> t2)) (body:exp) : Lemma
  (requires equiv t2 (fun (fsG:eval_env (extend t1 g)) -> io_bind (f (tail #t1 fsG)) (fun f -> io_return (f (hd fsG)))) body)
  (ensures equiv _ f (ELam body)) =
  lem_fv_in_env_lam g t1 body;
  let g' = extend t1 g in
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> (t1 ^-> t2) ⦂ (h, f fsG, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:get_Type t1) (lt_v:local_trace h). t1 ∋ ((h++lt_v), fs_v, v) ==> t2 ⦂ ((h++lt_v), io_bind (f fsG) (fun f -> io_return (f fs_v)), subst_beta v body') with begin
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
  end
//#pop-options

let equiv_app #g
  (#t1:qType) (#t2:qType)
  (fs_e1:io_oexp g (t1 ^-> t2)) (fs_e2:io_oexp g t1)
  (e1:exp) (e2:exp)
  : Lemma
    (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2)
    (ensures
        (≈) #g #t2
        (fun fsG -> io_bind (fs_e1 fsG) (fun f -> io_bind (fs_e2 fsG) (fun x -> io_return (f x))))
        (EApp e1 e2)) = admit ()
  (*lem_fv_in_env_app g e1 e2;
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> t2 ⦂ (h, io_bind (fs_e1 fsG) (fun f -> io_bind (fs_e2 fsG) (fun x -> io_return (f x))), gsubst s (EApp e1 e2)) with begin
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
            assert (exists fs_r2. t1 ∋ (h++lt2, fs_r2, e2'));
            eliminate exists fs_r2. t1 ∋ (h++lt2, fs_r2, e2') returns (exists fs_r2. t2 ∋ (h++lt, fs_r2, e')) with  _. begin 
              (*eliminate forall (v:value) (fs_v:get_Type t1) (lt_v:local_trace h). t1 ∋ (h++lt_v, fs_v, v) ==>
                t2 ⦂ (h++lt_v, io_bind (fs_e1) (fun f -> f fs_v), subst_beta v e11)
              with e2' fs_r2 lt2;*)
              assume (t2 ⦂ (h++lt2, fs_e, subst_beta e2' e11));
              assert (t2 ∋ (h++lt, fs_r2, e'))
           end
          )
        end
      end
    end
  end*)

let equiv_if #g (#t:qType) (fs_e1:io_oexp g qBool) (fs_e2:io_oexp g t) (fs_e3:io_oexp g t) (e1:exp) (e2:exp) (e3:exp) : Lemma
  (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2 /\ fs_e3 ≈ e3)
  (ensures (
    (fun fsG ->
      io_bind (fs_e1 fsG) (fun b -> if b then fs_e2 fsG else fs_e3 fsG))
    ≈
    (EIf e1 e2 e3))) = admit ()
  (*lem_fv_in_env_if g e1 e2 e3;
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> t ⦂ (h, io_bind (fs_e1 fsG) (fun b -> if b then fs_e2 fsG else fs_e3 fsG), gsubst s (EIf e1 e2 e3)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e = io_bind fs_e1 (fun b -> if b then fs_e2 fsG else fs_e3 fsG) in
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
  end*)

let equiv_pair #g (#t1 #t2:qType) (fs_e1:io_oexp g t1) (fs_e2:io_oexp g t2) (e1:exp) (e2:exp) : Lemma
  (requires equiv t1 fs_e1 e1 /\ equiv t2 fs_e2 e2)
  (ensures equiv #g (t1 ^* t2) (fun fsG -> (fs_e1 fsG, fs_e2 fsG)) (EPair e1 e2)) =
  lem_fv_in_env_pair g e1 e2;
  let t = t1 ^* t2 in
  introduce forall b (s:gsub g b) fsG h. fsG `(∽) h` s ==> t ⦂ (h, io_return (fs_e1 fsG, fs_e2 fsG), gsubst s (EPair e1 e2)) with begin
    let fs_e1 = fs_e1 fsG in
    let fs_e2 = fs_e2 fsG in
    let fs_e = (fs_e1, fs_e2) in
    let e = EPair (gsubst s e1) (gsubst s e2) in
    assert (gsubst s (EPair e1 e2) == e);
    let EPair e1 e2 = e in
    introduce fsG `(∽) h` s ==> t ⦂ (h, io_return fs_e, e) with _. begin
      introduce forall lt (e':closed_exp). steps e e' h lt /\ irred e' (h++lt) ==> (exists fs_r. t ∋ (h++lt, fs_r, e')) with begin
        introduce steps e e' h lt /\ irred e' (h++lt) ==> (exists (fs_r:get_Type t). t ∋ (h++lt, fs_e, e')) with _. begin
          let steps_e_e' : squash (steps e e' h lt) = () in
          FStar.Squash.map_squash #_ #(squash (exists (fs_r:get_Type t). t ∋ (h++lt, fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            safety #t1 fs_e1 e1;
            safety #t2 fs_e2 e2;
            let (e1', e2', (| lt1, (| lt2, lt3 |) |)) = destruct_steps_epair e1 e2 e' h lt steps_e_e' in
            assert (t1 ∋ (h, fs_e1, e1'));
            assert (t2 ∋ (h++lt1, fs_e2, e2'));
            assert (t ∋ (h, fs_e, EPair e1' e2'));
            lem_values_are_expressions t h fs_e (EPair e1' e2')
          )
        end
      end
    end
  end

(**
let equiv_pair_fst_app #g (#t1 #t2:qType) (fs_e12:fs_oexp g (t1 ^* t2)) (e12:exp) : Lemma
  (requires equiv #g (t1 ^* t2) fs_e12 e12) (** is this too strict? we only care for the left to be equivalent. **)
  (ensures equiv #g t1 (fun fsG -> fst (fs_e12 fsG)) (EFst e12)) =
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
    (ensures equiv #g ((t1 ^* t2) ^-> t1) (fun _ -> fst #(get_Type t1) #(get_Type t2)) (ELam (EFst (EVar 0))))
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
          equiv_pair_fst_app #empty #t1 #t2 (fun _ -> fs_v) v;
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

let equiv_pair_snd_app #g (#t1 #t2:qType) (fs_e12:fs_oexp g (t1 ^* t2)) (e12:exp)
  : Lemma
    (requires equiv #g (t1 ^* t2) fs_e12 e12) (** is this too strict? we only care for the left to be equivalent. **)
    (ensures equiv #g t2 (fun fsG -> snd (fs_e12 fsG)) (ESnd e12))
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
    (ensures equiv #g ((t1 ^* t2) ^-> t2) (fun _ -> snd #(get_Type t1) #(get_Type t2)) (ELam (ESnd (EVar 0))))
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
          equiv_pair_snd_app #empty #t1 #t2 (fun _ -> fs_v) v;
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
**)
