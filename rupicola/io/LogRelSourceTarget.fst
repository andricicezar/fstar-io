module LogRelSourceTarget

open FStar.Classical.Sugar
open FStar.List.Tot

open QTyp
open STLC
open IO
open Trace

(** Section 8.1: https://www.cs.uoregon.edu/research/summerschool/summer24/lectures/Ahmed.pdf **)

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __closed terms__. **)
let rec (∋) (t:qType) (p:(history * fs_val t * closed_exp)) : Tot Type0 (decreases %[get_rel t;0]) =
  let (h, fs_v, e) = p in
  match get_rel t with // way to "match" on F* types
  | QUnit -> fs_v == () /\ e == EUnit
  | QBool -> (fs_v == true /\ e == ETrue) \/ (fs_v == false /\ e == EFalse)
  | QFileDescriptor ->  e == EFileDescr fs_v
  | QString -> (match e with | EString s -> fs_v == s | _ -> False)
  | QArr #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> t2 = fs_v in
    match e with
    | ELam e' ->
      (forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∋ (h++lt_v, fs_v, v) ==>
        pack qt2 ⊇ (h++lt_v, fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
  | QArrIO #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> io t2 = fs_v in
    match e with
    | ELam e' -> // instead quantify over h'' - extensions of the history
      (forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∋ (h++lt_v, fs_v, v) ==>
        pack qt2 ⫄ (h++lt_v, fs_f fs_v, subst_beta v e'))
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
and (⊇) (t:qType) (p:history * fs_val t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
  let (h, fs_e, e) = p in
  forall (e':closed_exp) lt.
    e_beh e e' h lt ==>
    (t ∋ (h, fs_e, e') /\ lt == [])
                           (** vvvvvvvvvv defined over producers **)
and (⫄) (t:qType) (p:history * fs_prod t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
  let (h, fs_e, e) = p in
  forall lt.
    (forall e'. e_beh e e' h lt ==>
      (exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r))

let valid_contains (#t:qType) (fs_e:fs_val t) (e:value) : Type0 =
  forall (h:history). t ∋ (h, fs_e, e)

let valid_superset_val (#t:qType) (fs_e:fs_val t) (e:value) : Type0 =
  forall (h:history). t ⊇ (h, fs_e, e)

let valid_superset_prod (#t:qType) (fs_e:fs_prod t) (e:closed_exp) : Type0 =
  forall (h:history). t ⫄ (h, fs_e, e)

let lem_values_valid_superset_val_valid_contains t (fs_e:fs_val t) (e:value) :
  Lemma (requires valid_superset_val fs_e e)
        (ensures  valid_contains fs_e e) = admit () (** TODO **)

let rec lem_values_are_values t h fs_e (e:closed_exp) :
  Lemma (requires t ∋ (h, fs_e, e))
        (ensures is_value e)
        (decreases e) =
  match get_rel t with
  | QUnit -> ()
  | QBool -> ()
  | QFileDescriptor -> ()
  | QString -> ()
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

let lem_values_are_expressions t h fs_e e : (** lemma used by Amal **)
  Lemma (requires t ∋ (h, fs_e, e))
        (ensures  t ⊇ (h, fs_e, e)) =
  lem_values_are_values t h fs_e e;
  lem_value_is_irred e;
  introduce forall (e':closed_exp) (lt:local_trace h). e_beh e e' h lt ==> (t ∋ (h, fs_e, e') /\ lt == []) with begin
    introduce e_beh e e' h lt ==> (t ∋ (h, fs_e, e') /\ lt == []) with h_beh. begin
      eliminate steps e e' h lt /\ indexed_irred e' (h++lt)
      returns (t ∋ (h, fs_e, e') /\ lt == []) with sq_sts _. begin
        assert (indexed_irred e h);
        FStar.Squash.bind_squash sq_sts (fun (sts:steps e e' h lt) ->
          let _ = lem_irred_implies_srefl_steps sts in
          assert (e == e');
          assert (lt == []);
          assert (t ∋ (h, fs_e, e'));
          FStar.Squash.get_proof (t ∋ (h, fs_e, e') /\ lt == [])
        )
      end
    end
  end

let lem_values_are_producers t h fs_e e : (** lemma used by Amal **)
  Lemma (requires t ∋ (h, fs_e, e))
        (ensures  t ⫄ (h, io_return fs_e, e)) =
  lem_values_are_values t h fs_e e;
  lem_value_is_irred e;
  introduce forall (e':closed_exp) (lt : local_trace h). e_beh e e' h lt ==> 
      (exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e') /\ fs_beh (io_return fs_e) h lt fs_r) with begin
    introduce e_beh e e' h lt ==> 
        (exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e') /\ fs_beh (io_return fs_e) h lt fs_r) with h_beh. begin
      eliminate steps e e' h lt /\ indexed_irred e' (h++lt)
      returns (exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e') /\ fs_beh (io_return fs_e) h lt fs_r)
      with sq_sts _. begin
        assert (indexed_irred e h);
        FStar.Squash.bind_squash sq_sts (fun (sts:steps e e' h lt) ->
          let _ = lem_irred_implies_srefl_steps sts in
          assert (e == e');
          assert (lt == []);
          assert (t ∋ (h, fs_e, e));
          lem_fs_beh_return fs_e h;
          assert (fs_beh (io_return fs_e) h [] fs_e);
          FStar.Squash.get_proof (exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e') /\ fs_beh (io_return fs_e) h lt fs_r)
        )
      end
    end
  end

let lem_forall_values_are_values t h fs_e :
  Lemma (forall (e:closed_exp). t ∋ (h, fs_e, e) ==> is_value e) =
  introduce forall e. t ∋ (h, fs_e, e) ==> is_value e with begin
    introduce _ ==> _ with _. begin
      lem_values_are_values t h fs_e e
    end
  end

let lem_forall_values_are_values_prod t h :
  Lemma (forall (e:closed_exp) (lt:local_trace h) (fs_r:get_Type t). t ∋ (h++lt, fs_r, e) ==> is_value e) =
  introduce forall e lt fs_r. t ∋ (h++lt, fs_r, e) ==> is_value e with begin
    introduce _ ==> _ with _. begin
      lem_values_are_values t (h++lt) fs_r e
    end
  end

(** F* Evaluation Environment : variable -> value **)
let (∽) (#g:typ_env) #b (h:history) (fsG:eval_env g) (s:gsub g b) : Type0 =
  forall (x:var). Some? (g x) ==>
    Some?.v (g x) ∋ (h, index fsG x, s x)
  (**  TODO      ^^^ not like in Amal's work. she uses an exp relation - but this is what she meant, because index fsG x is necessarily a value **)

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __open terms__. **)
let superset_oval (#g:typ_env) (t:qType) (fs_e:fs_oval g t) (e:exp) : Type0 =
  fv_in_env g e /\
  forall b (s:gsub g b) (fsG:eval_env g) (h:history).
    fsG `(∽) h` s ==> t ⊇ (h, fs_e fsG, gsubst s e)

let (⊐) (#g:typ_env) (#t:qType) (fs_v:fs_oval g t) (e:exp) : Type0 =
  superset_oval #g t fs_v e

let superset_oprod (#g:typ_env) (t:qType) (fs_e:fs_oprod g t) (e:exp) : Type0 =
  fv_in_env g e /\
  forall b (s:gsub g b) (fsG:eval_env g) (h:history).
    fsG `(∽) h` s ==> t ⫄ (h, fs_e fsG, gsubst s e)

let (⊒) (#g:typ_env) (#t:qType) (fs_v:fs_oprod g t) (e:exp) : Type0 =
  superset_oprod #g t fs_v e

let lem_value_superset_valid_contains t (fs_e:fs_oval empty t) (e:value) :
  Lemma (requires fs_e ⊐ e)
        (ensures  valid_contains #t (fs_e empty_eval) e) =
  introduce forall h. t ∋ (h, fs_e empty_eval, e) with begin
    eliminate forall b (s:gsub empty b) (fsG:eval_env empty) (h:history).
      fsG `(∽) h` s ==> t ⊇ (h, fs_e empty_eval, gsubst s e) with false gsub_empty empty_eval h;
    assert (t ⊇ (h, fs_e empty_eval, e));
    lem_values_valid_superset_val_valid_contains t (fs_e empty_eval) e;
    assert (t ∋ (h, fs_e empty_eval, e))
  end

let lem_closed_superset_valid_prod g (fsG:eval_env g) #t #b (s:gsub g b) (fs_e:fs_oprod g t) (e:exp) :
  Lemma (requires fs_e ⊒ e /\ (forall h. fsG `(∽) h` s))
        (ensures  valid_superset_prod #t (fs_e fsG) (gsubst s e)) =
  introduce forall h. t ⫄ (h, fs_e fsG, gsubst s e) with begin
    eliminate forall b (s:gsub g b) (fsG:eval_env g) (h:history).
      fsG `(∽) h` s ==> t ⫄ (h, fs_e fsG, gsubst s e) with b s fsG h
  end

let rec val_type_closed_under_history_extension (t:qType) (h:history) (fs_v:fs_val t) (e:closed_exp) :
  Lemma (requires t ∋ (h, fs_v, e))
        (ensures forall lt. t ∋ (h++lt, fs_v, e))
        (decreases %[get_rel t;0]) =
  introduce forall lt. t ∋ (h++lt, fs_v, e) with begin
  match get_rel t with
  | QUnit -> ()
  | QBool -> ()
  | QFileDescriptor -> ()
  | QString -> ()
  | QArr #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> t2 = fs_v in
    let ELam e' = e in
    introduce forall (v:value) (fs_v':t1) (lt_v':local_trace (h++lt)). pack qt1 ∋ ((h++lt)++lt_v', fs_v', v) ==> pack qt2 ⊇ ((h++lt)++lt_v', fs_f fs_v', subst_beta v e') with begin
      introduce pack qt1 ∋ ((h++lt)++lt_v', fs_v', v) ==> _ with _. begin
        eliminate forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∋ (h++lt_v, fs_v, v) ==> pack qt2 ⊇ (h++lt_v, fs_f fs_v, subst_beta v e') with v fs_v' (lt @ lt_v');
        trans_history h lt lt_v'
      end
    end
    end
  | QArrIO #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> io t2 = fs_v in
    let ELam e' = e in
    introduce forall (v:value) (fs_v':t1) (lt_v':local_trace (h++lt)). pack qt1 ∋ ((h++lt)++lt_v', fs_v', v) ==> pack qt2 ⫄ ((h++lt)++lt_v', fs_f fs_v', subst_beta v e') with begin
      introduce pack qt1 ∋ ((h++lt)++lt_v', fs_v', v) ==> _ with _. begin
        eliminate forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∋ (h++lt_v, fs_v, v) ==> pack qt2 ⫄ (h++lt_v, fs_f fs_v, subst_beta v e') with v fs_v' (lt @ lt_v');
        trans_history h lt lt_v'
      end
    end
    end
  | QPair #t1 #t2 qt1 qt2 -> begin
    let EPair e1 e2 = e in
    val_type_closed_under_history_extension (pack qt1) h (fst #t1 #t2 fs_v) e1;
    val_type_closed_under_history_extension (pack qt2) h (snd #t1 #t2 fs_v) e2
    end
  | QSum #t1 #t2 qt1 qt2 -> begin
    let fs_v : either t1 t2 = fs_v in
    match fs_v, e with
    | Inl fs_v', EInl e' -> val_type_closed_under_history_extension (pack qt1) h fs_v' e'
    | Inr fs_v', EInr e' -> val_type_closed_under_history_extension (pack qt2) h fs_v' e'
    | _ -> false_elim ()
    end
  end

let lem_shift_type_value_environments (#g:typ_env) #b (h:history) (fsG:eval_env g) (s:gsub g b) :
  Lemma (forall (lt:local_trace h). fsG `(∽) h` s ==> fsG `(∽) (h++lt)` s) =
  introduce forall (lt:local_trace h). fsG `(∽) h` s ==> fsG `(∽) (h++lt)` s with begin
    introduce _ ==> _ with _. begin
      introduce forall (x:var). Some? (g x) ==> Some?.v (g x) ∋ (h++lt, index fsG x, s x) with begin
        introduce _ ==> _ with _. begin
          val_type_closed_under_history_extension (Some?.v (g x)) h (index fsG x) (s x)
        end
      end
    end
  end

let safety_prod (#t:qType) (fs_e:fs_prod t) (e:closed_exp) : Lemma
  (requires (valid_superset_prod fs_e e))
  (ensures safe e) =
  introduce forall (e':closed_exp) (h:history) (lt:local_trace h).
    steps e e' h lt ==> is_value e' \/ indexed_can_step e' (h++lt) with begin
    introduce steps e e' h lt ==> is_value e' \/ indexed_can_step e' (h++lt) with _. begin
      introduce indexed_irred e' (h++lt) ==> is_value e' with _. begin
        eliminate forall b (s:gsub empty b) (fsG:eval_env empty) (h:history).
          fsG `(∽) h` s ==> t ⫄ (h, fs_e, gsubst s e)
        with  true gsub_empty empty_eval h;
        assert (t ⫄ (h, fs_e, e));
        eliminate exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e') /\ fs_beh fs_e h lt fs_r
        returns is_value e' with _. begin
          assert (t ∋ (h++lt, fs_r, e'));
          lem_values_are_values t (h++lt) fs_r e';
          assert (is_value e')
        end
      end
    end
  end

open FStar.Tactics.V1

let unfold_contains_arrow (t1 t2:qType) (h:history) (fs_e1:fs_val (t1 ^-> t2)) (e11:exp)
  : Lemma
    (requires is_closed (ELam e11) /\ (t1 ^-> t2) ∋ (h, fs_e1, ELam e11))
    (ensures forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∋ (h++lt_v, fs_v, v) ==> t2 ⊇ (h++lt_v, fs_e1 fs_v, subst_beta v e11))
  by (explode ();
    bump_nth 4;
    let x = nth_binder (-2) in
    let x', x'' = destruct_and x in
    clear x;
    let (x'0, x'1) = destruct_and x' in
    clear x';
    binder_retype x'1;
      norm [delta_once [`%op_u8715;`%(^->);`%get_rel; `%Mkdtuple2?._2;`%Mkdtuple2?._1]; zeta; delta; iota];
      l_to_r [`lem_pack_get_rel];
    trefl ();
    let x''' = instantiate x'' (fresh_uvar None) in
    clear x'';
    mapply x''';
    clear x''')
  = ()

let unfold_contains_io_arrow (t1 t2:qType) (fs_e1:fs_val (t1 ^->!@ t2)) (e11:exp) (h:history)
  : Lemma
    (requires (is_closed (ELam e11)) /\ ((t1 ^->!@ t2) ∋ (h, fs_e1, ELam e11)))
    (ensures (forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∋ (h++lt_v, fs_v, v) ==> t2 ⫄ (h++lt_v, fs_e1 fs_v, subst_beta v e11)))
  by (explode ();
    bump_nth 4;
    let x = nth_binder (-2) in
    let x', x'' = destruct_and x in
    clear x;
    let (x'0, x'1) = destruct_and x' in
    clear x';
    binder_retype x'1;
      norm [delta_once [`%op_u8715;`%(^->!@);`%get_rel; `%Mkdtuple2?._2;`%Mkdtuple2?._1]; zeta; delta; iota];
      l_to_r [`lem_pack_get_rel];
    trefl ();
    let x''' = instantiate x'' (fresh_uvar None) in
    clear x'';
    mapply x''')
  = ()

(** Unused
let sem_expr_shape_val (#t:qType) (fs_e:fs_val t) (e:exp) (h:history) :
  Lemma (requires equiv_val fs_e e)
        (ensures indexed_sem_expr_shape (type_quotation_to_typ (get_rel t)) e h) =  admit ()
**)
(** Unused **)
let sem_expr_shape_prod (#t:qType) (fs_e:fs_prod t) (e:closed_exp) (h:history) :
  Lemma (requires valid_superset_prod fs_e e)
        (ensures indexed_sem_expr_shape (type_quotation_to_typ (get_rel t)) e h) =
  introduce forall e' (lt:local_trace h). e_beh e e' h lt ==> sem_value_shape (type_quotation_to_typ (get_rel t)) e' with begin
    introduce e_beh e e' h lt ==> sem_value_shape (type_quotation_to_typ (get_rel t)) e' with _. begin
      eliminate forall b (s:gsub empty b) (fsG:eval_env empty) (h:history).
          fsG `(∽) h` s ==> t ⫄ (h, fs_e, gsubst s e)
      with  true gsub_empty empty_eval h;
      assert (t ⫄ (h, fs_e, e));
      eliminate exists (fs_r:get_Type t). t ∋ (h++lt, fs_r, e')
      returns sem_value_shape (type_quotation_to_typ (get_rel t)) e' with _. begin
      lem_values_are_values t (h++lt) fs_r e'
      end
    end
  end
