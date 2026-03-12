module LambdaIO.DestructLemmas

open FStar.Squash
open LambdaIO

// DESTRUCT LEMMAS

let can_step_eapp_when_reduced (e1:closed_exp{ELam? e1 /\ is_closed e1}) (e2:closed_exp) (h:history) : Lemma
  (requires indexed_safe e2 h)
  (ensures (exists e' oev. step (EApp e1 e2) e' h oev))
  =
  (**
     We case analyze if e1 can step or if e2 can step,
       and for each case, we build a step accordingly **)

  introduce indexed_irred e2 h ==> (exists e' oev. step (EApp e1 e2) e' h oev) with _. begin
    assert (steps e2 e2 h []);
    let ELam e11 = e1 in
    let st : step (EApp (ELam e11) e2) (subst_beta e2 e11) h None = Beta e11 e2 h in
    ()
  end;

  introduce ~(indexed_irred e2 h) ==> (exists e' oev. step (EApp e1 e2) e' h oev) with _. begin
    assert (exists e2' oev2. step e2 e2' h oev2);
    eliminate exists e2' oev2. step e2 e2' h oev2 returns exists e' oev. step (EApp e1 e2) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (AppRight e1 st))
    end
  end

let lem_irred_eapp_implies_irred_e1 (e1 e2:closed_exp) (h:history) :
  Lemma (requires indexed_irred (EApp e1 e2) h)
        (ensures indexed_irred e1 h) =
  introduce forall (e1':closed_exp) (oev:option (event_h h)). step e1 e1' h oev ==> False with begin
    introduce _ ==> _ with st. begin
      bind_squash st (fun st -> return_squash (AppLeft #e1 e2 #e1' #h #oev st))
    end
  end

(** Such a lemma is mentioned by Amal Ahmed in her PhD thesis, section 2

    How the steps look like:
      EApp e1 e2 -->* EApp (ELam e11) e2 ->* EApp (ELam e11) e2' --> subst_beta e2' e11 -->* e'
**)
(* By induction on st.
   Case st = SRefl e1. We know e' = EApp e1 e2, so irreducible.
     We case analyze if e1 can step, if it does contradiction, so e1 irreducible.
       By sem_value_shape ELam? e1 .
     We case analyze if e2 can step, if it does contradiction, so e2 irreducible.
       (By safe e2 is_value e2; but not needed by step)
       So e = EApp (ELam _) e2 -> subst ..., contradiction.
   Case st = STrans .... We know (EApp e1 e2) -> e'' /\ e'' ->* e'
     We case analyze if e1 can step.
     Subcase e1 -> e1'. We know e'' = EApp e1' e2, so (EApp e1' e2) ->* e'.
       By IH we almost conclude, plus e1 -> e1' ->* (ELam e11) by STrans
     Subcase irred e1. From safe e1 we get is_value e1, and from sem_value_shape we get ELam? e1.
       We case analyze if e2 can step.
       Subsubcase e2 -> e2'. Similar to above, we use IH.
       Subsubcase irred e2. (From safe e2 we get is_value e2; but not needed by step.)
         So e = EApp (ELam e11) e2 -> subst_beta e2 e11 = e''. Return e11 e2. *)

let rec destruct_steps_eapp_e1
  (e1:closed_exp)
  (e2:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EApp e1 e2) e' h lt)
  (t1 t2:typ) :
  Pure (exp * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt) /\
      indexed_sem_expr_shape (TArr t1 t2) e1 h)
    (ensures fun (e11, (| lt1, lt' |)) ->
      is_closed (ELam e11) /\
      steps e1 (ELam e11) h lt1 /\
      steps (EApp e1 e2) (EApp (ELam e11) e2) h lt1 /\
      steps (EApp (ELam e11) e2) e' (h++lt1) lt' /\
      (lt == (lt1 @ lt')) /\
      (indexed_irred e1 h ==> (lt1 == [] /\ e1 == ELam e11)))
    (decreases st) =
    match st with
    | SRefl (EApp e1 e2') h -> begin
      lem_irred_eapp_implies_irred_e1 e1 e2 h;
      assert (steps e1 e1 h []);
      let ELam e11 = e1 in
      (e11, (| [], lt |))
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_eapp step_eapp_steps -> begin
      let (EApp e1 e2) = e in
      match step_eapp with
      | AppLeft #e1 e2 #e1' #h #oev1 step_e1 -> begin
        let (EApp e1' e2) = f2 in
        lem_step_implies_steps e1 e1' h oev1;
        lem_step_implies_steps (EApp e1 e2) (EApp e1' e2) h oev1;
        let lt1 : local_trace h = as_lt oev1 in
        let s2 : steps (EApp e1' e2) e' (h++lt1) lt23 = step_eapp_steps in
        trans_history h lt1 lt23;
        lem_step_preserve_indexed_sem_expr_shape e1 e1' h oev1 (TArr t1 t2);
        let (e11, (| lt1', lt' |)) = destruct_steps_eapp_e1 e1' e2 e' (h++lt1) lt23 s2 t1 t2 in
        trans_history h lt1 lt1';
        lem_steps_transitive e1 e1' (ELam e11) h lt1 lt1';
        lem_steps_transitive (EApp e1 e2) (EApp e1' e2) (EApp (ELam e11) e2) h lt1 lt1';
        (e11, (| (lt1 @ lt1'), lt' |))
        end
      | _ -> begin
        let ELam e11 = e1 in
        (e11, (| [], lt |))
        end
      end

let rec destruct_steps_eapp_e2
  (e11:exp{is_closed (ELam e11)})
  (e2:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EApp (ELam e11) e2) e' h lt) :
  Pure (value * (lt2:local_trace h & local_trace (h++lt2)))
    (requires indexed_irred e' (h++lt) /\
      indexed_safe e2 h)
    (ensures fun (e2', (| lt2, lt' |)) ->
      steps e2 e2' h lt2 /\
      //steps (EApp (ELam e11) e2) (EApp (ELam e11) e2') h lt2 /\
      steps (EApp (ELam e11) e2) (subst_beta e2' e11) h lt2 /\
      steps (subst_beta e2' e11) e' (h++lt2) lt' /\
      (lt == (lt2 @ lt')) /\
      (indexed_irred e2 h ==> (lt2 == [] /\ e2 == e2')))
    (decreases st) =
    match st with
    | SRefl (EApp (ELam e11) e2) h -> begin
      can_step_eapp_when_reduced (ELam e11) e2 h;
      assert (steps e2 e2 h []);
      (e2, (| [], lt |))
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_eapp step_eapp_steps -> begin
      let (EApp (ELam e11) e2) = e in
      match step_eapp with
      | AppRight (ELam e11) #e2 #e2' #h #oev2 step_e2 -> begin
        let (EApp (ELam e11) e2') = f2 in
        lem_step_implies_steps e2 e2' h oev2;
        lem_step_implies_steps (EApp (ELam e11) e2) (EApp (ELam e11) e2') h oev2;
        let lt2 : local_trace h = as_lt oev2 in
        let s2 : steps (EApp (ELam e11) e2') e' (h++lt2) lt23 = step_eapp_steps in
        trans_history h lt2 lt23;
        lem_step_preserve_indexed_safe e2 e2' h oev2;
        let (e2'', (| lt2', lt' |)) = destruct_steps_eapp_e2 e11 e2' e' (h++lt2) lt23 s2 in
        trans_history h lt2 lt2';
        lem_steps_transitive e2 e2' e2'' h lt2 lt2';
        lem_steps_transitive (EApp (ELam e11) e2) (EApp (ELam e11) e2') (subst_beta e2'' e11) h lt2 lt2';
        (e2'', (| (lt2 @ lt2'), lt' |))
        end
      | AppLeft _ _ -> begin
        lem_value_is_irred (ELam e11);
        (e2, (| [], lt |))
        end
      | Beta e11 e2' h -> begin
        lem_step_implies_steps (EApp (ELam e11) e2') (subst_beta e2' e11) h None;
        (e2, (| [], lt |))
        end
      end

let can_step_eif_when_safe (e1 e2 e3:closed_exp) (h:history) : Lemma
  (requires indexed_sem_expr_shape TBool e1 h)
  (ensures (exists e' oev. step (EIf e1 e2 e3) e' h oev))
  =
  introduce indexed_irred e1 h /\ e1 == ETrue ==> (exists e' oev. step (EIf e1 e2 e3) e' h oev) with _. begin
    assert (steps e1 e1 h []);
    let st : step (EIf ETrue e2 e3) e2 h None = IfTrue e2 e3 h in
    ()
  end;

  introduce indexed_irred e1 h /\ e1 == EFalse ==> (exists e' oev. step (EIf e1 e2 e3) e' h oev) with _. begin
    assert (steps e1 e1 h []);
    let st : step (EIf EFalse e2 e3) e3 h None = IfFalse e2 e3 h in
    ()
  end;

  introduce indexed_irred e1 h /\ ~(e1 == EFalse \/ e1 == ETrue) ==> (exists e' oev. step (EIf e1 e2 e3) e' h oev) with _. begin
    assert (steps e1 e1 h []);
    false_elim ()
  end;

  introduce ~(indexed_irred e1 h) ==> (exists e' oev. step (EIf e1 e2 e3) e' h oev) with _. begin
    assert (exists e1' oev1. step e1 e1' h oev1);
    eliminate exists e1' oev1. step e1 e1' h oev1 returns exists e' oev. step (EIf e1 e2 e3) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (IfCond e2 e3 st))
    end
  end

#push-options "--split_queries always"
let rec destruct_steps_eif
  (e1:closed_exp)
  (e2:closed_exp)
  (e3:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EIf e1 e2 e3) e' h lt) :
  Pure (closed_exp * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt) /\
      indexed_sem_expr_shape TBool e1 h)
    (ensures fun (e1', (| lt1, lt2 |)) ->
      indexed_irred e1' (h++lt1) /\
      is_value e1' /\
      steps e1 e1' h lt1 /\
      steps (EIf e1 e2 e3) (EIf e1' e2 e3) h lt1 /\
      steps (EIf e1' e2 e3) e' (h++lt1) lt2 /\
      (ETrue? e1' ==> (steps e2 e' (h++lt1) lt2)) /\
      (EFalse? e1' ==> (steps e3 e' (h++lt1) lt2)) /\
      (lt == lt1 @ lt2) /\
      (indexed_irred e1 h ==> (lt1 == [] /\ e1 == e1')))
    (decreases st)
  = match st with
    | SRefl (EIf e1 e2 e3) h -> begin
      can_step_eif_when_safe e1 e2 e3 h;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_eif step_eif_steps -> begin
      let (EIf e1 e2 e3) = e in
      match step_eif with
      | IfCond #e1 e2 e3 #e1' #h #oev1 step_e1 -> begin
        let (EIf e1' e2 e3) = f2 in
        lem_step_implies_steps e1 e1' h oev1;
        lem_step_implies_steps (EIf e1 e2 e3) (EIf e1' e2 e3) h oev1;
        let lt1 : local_trace h = as_lt oev1 in
        lem_step_preserve_indexed_sem_expr_shape e1 e1' h oev1 TBool;
        let s2 : steps (EIf e1' e2 e3) e' (h++lt1) lt23 = step_eif_steps in
        trans_history h lt1 lt23;
        let (e1'', (| lt1', lt2 |)) = destruct_steps_eif e1' e2 e3 e' (h++lt1) lt23 s2 in
        trans_history h lt1 lt1';
        lem_steps_transitive e1 e1' e1'' h lt1 lt1';
        lem_steps_transitive (EIf e1 e2 e3) (EIf e1' e2 e3) (EIf e1'' e2 e3) h lt1 lt1';
        (e1'', (| (lt1 @ lt1'), lt2 |))
        end
      | IfTrue e2 e3 h -> begin
        lem_step_implies_steps (EIf e1 e2 e3) e2 h None;
        lem_value_is_irred e1;
        (e1, (| [], lt |))
        end
      | IfFalse e2 e3 h -> begin
        lem_step_implies_steps (EIf e1 e2 e3) e3 h None;
        lem_value_is_irred e1;
        (e1, (| [], lt |))
        end
      end
#pop-options

  (**
    How the steps look like:
      EIf e1 e2 e3 -->* EIf e1' e2 e3 -->* e'
  **)

let lem_irred_epair_implies_irred_e1 (e1 e2:closed_exp) (h:history) :
  Lemma (requires indexed_irred (EPair e1 e2) h)
        (ensures indexed_irred e1 h) =
  introduce forall (e1':closed_exp) (oev:option (event_h h)). step e1 e1' h oev ==> False with begin
    introduce _ ==> _ with st. begin
      bind_squash st (fun st -> return_squash (PairLeft #e1 e2 #e1' #h #oev st))
    end
  end

let lem_irred_epair_implies_irred_e2 (e1':closed_exp{is_value e1'}) (e2:closed_exp) (h:history) :
  Lemma (requires indexed_irred (EPair e1' e2) h)
        (ensures indexed_irred e2 h) =
  introduce forall (e2':closed_exp) (oev:option (event_h h)). step e2 e2' h oev ==> False with begin
    introduce _ ==> _ with st. begin
      bind_squash st (fun st -> return_squash (PairRight e1' #e2 #e2' #h #oev st))
    end
  end

#push-options "--split_queries always"
let rec destruct_steps_epair_e1
  (e1:closed_exp)
  (e2:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EPair e1 e2) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt) /\
      indexed_safe e1 h)
    (ensures fun (e1', (| lt1, lt' |)) ->
      steps e1 e1' h lt1 /\
      steps (EPair e1 e2) (EPair e1' e2) h lt1 /\
      steps (EPair e1' e2) e' (h++lt1) lt' /\
      (lt == (lt1 @ lt')) /\
      (indexed_irred e1 h ==> (lt1 == [] /\ e1 == e1')))
    (decreases st) =
  match st with
  | SRefl (EPair e1 e2) h -> begin
    lem_irred_epair_implies_irred_e1 e1 e2 h;
    assert (steps e1 e1 h []);
    (e1, (| [], lt |))
    end
  | STrans #e #f2 #e' #h #_ #lt23 step_epair step_epair_steps -> begin
    let (EPair e1 e2) = e in
    match step_epair with
    | PairLeft #e1 e2 #e1' #h #oev1 step_e1 -> begin
      let (EPair e1' e2) = f2 in
      lem_step_implies_steps e1 e1' h oev1;
      lem_step_implies_steps (EPair e1 e2) (EPair e1' e2) h oev1;
      let lt1 : local_trace h = as_lt oev1 in
      let s2 : steps (EPair e1' e2) e' (h++lt1) lt23 = step_epair_steps in
      trans_history h lt1 lt23;
      lem_step_preserve_indexed_safe e1 e1' h oev1;
      let (e1'', (| lt1', lt' |)) = destruct_steps_epair_e1 e1' e2 e' (h++lt1) lt23 s2 in
      trans_history h lt1 lt1';
      lem_steps_transitive e1 e1' e1'' h lt1 lt1';
      lem_steps_transitive (EPair e1 e2) (EPair e1' e2) (EPair e1'' e2) h lt1 lt1';
      (e1'', (| (lt1 @ lt1'), lt' |))
      end
    | _ -> (e1, (| [], lt |))
    end
#pop-options

let rec destruct_steps_epair_e2
  (e1':closed_exp{is_value e1'})
  (e2:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EPair e1' e2) e' h lt) :
  Pure (value * (lt2:local_trace h & local_trace (h++lt2)))
    (requires indexed_irred e' (h++lt) /\
      indexed_safe e2 h)
    (ensures fun (e2', (| lt2, lt' |)) ->
      steps e2 e2' h lt2 /\
      steps (EPair e1' e2) (EPair e1' e2') h lt2 /\
      steps (EPair e1' e2') e' (h++lt2) lt' /\
      (lt == (lt2 @ lt')) /\
      (indexed_irred e2 h ==> (lt2 == [] /\ e2 == e2')))
    (decreases st) =
  match st with
  | SRefl (EPair e1' e2) h -> begin
    lem_irred_epair_implies_irred_e2 e1' e2 h;
    assert (steps e2 e2 h []);
    (e2, (| [], lt |))
    end
  | STrans #e #f2 #e' #h #_ #lt23 step_epair step_epair_steps -> begin
    let (EPair e1 e2) = e in
    match step_epair with
    | PairRight e1 #e2 #e2' #h #oev2 step_e2 -> begin
      let (EPair e1' e2') = f2 in
      lem_step_implies_steps e2 e2' h oev2;
      lem_step_implies_steps (EPair e1' e2) (EPair e1' e2') h oev2;
      let lt2 : local_trace h = as_lt oev2 in
      let s2 : steps (EPair e1' e2') e' (h++lt2) lt23 = step_epair_steps in
      trans_history h lt2 lt23;
      lem_step_preserve_indexed_safe e2 e2' h oev2;
      let (e2'', (| lt2', lt' |)) = destruct_steps_epair_e2 e1' e2' e' (h++lt2) lt23 s2 in
      trans_history h lt2 lt2';
      lem_steps_transitive e2 e2' e2'' h lt2 lt2';
      lem_steps_transitive (EPair e1' e2) (EPair e1' e2') (EPair e1' e2'') h lt2 lt2';
      (e2'', (| (lt2 @ lt2'), lt' |))
      end
    | PairLeft _ _ -> begin
      lem_value_is_irred e1';
      (e2, (| [], lt |))
      end
    end

  (**
    How the steps look like:
      EPair e1 e2 -->* EPair e1' e2' == e'
  **)

let lem_destruct_steps_epair
  (e1' e2':closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h) :
  Lemma (requires (steps (EPair e1' e2') e' h lt /\ indexed_irred e1' h /\ indexed_irred e2' h))
        (ensures ((EPair e1' e2') == e') /\ lt == []) =
  introduce steps (EPair e1' e2') e' h lt ==> ((EPair e1' e2') == e') /\ lt == [] with _. begin
    FStar.Squash.bind_squash #(steps (EPair e1' e2') e' h lt) () (fun sts ->
    match sts with
    | SRefl (EPair _ _) h -> ()
    | STrans #e #f2 #e' #h #_ #lt23 step_epair step_epair_steps ->
      match step_epair with
      | PairLeft _ _ -> false_elim ()
      | PairRight _ _ -> false_elim ()
    )
  end

let lem_irred_estringeq_implies_irred_e1 (e1 e2:closed_exp) (h:history) :
  Lemma (requires indexed_irred (EStringEq e1 e2) h)
        (ensures indexed_irred e1 h) =
  introduce forall (e1':closed_exp) (oev:option (event_h h)). step e1 e1' h oev ==> False with begin
    introduce _ ==> _ with st. begin
      bind_squash st (fun st -> return_squash (StringEqLeft #e1 e2 #e1' #h #oev st))
    end
  end

let lem_irred_estringeq_implies_irred_e2 (e1':closed_exp{EString? e1'}) (e2:closed_exp) (h:history) :
  Lemma (requires indexed_irred (EStringEq e1' e2) h)
        (ensures indexed_irred e2 h) =
  introduce forall (e2':closed_exp) (oev:option (event_h h)). step e2 e2' h oev ==> False with begin
    introduce _ ==> _ with st. begin
      bind_squash st (fun st -> return_squash (StringEqRight e1' #e2 #e2' #h #oev st))
    end
  end

#push-options "--split_queries always"
let rec destruct_steps_estringeq_e1
  (e1:closed_exp)
  (e2:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EStringEq e1 e2) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt) /\
      indexed_safe e1 h)
    (ensures fun (e1', (| lt1, lt' |)) ->
      steps e1 e1' h lt1 /\
      steps (EStringEq e1 e2) (EStringEq e1' e2) h lt1 /\
      steps (EStringEq e1' e2) e' (h++lt1) lt' /\
      (lt == (lt1 @ lt')) /\
      (indexed_irred e1 h ==> (lt1 == [] /\ e1 == e1')))
    (decreases st) =
  match st with
  | SRefl (EStringEq e1 e2) h -> begin
    lem_irred_estringeq_implies_irred_e1 e1 e2 h;
    assert (steps e1 e1 h []);
    (e1, (| [], lt |))
    end
  | STrans #e #f2 #e' #h #_ #lt23 step_estringeq step_estringeq_steps -> begin
    let (EStringEq e1 e2) = e in
    match step_estringeq with
    | StringEqLeft #e1 e2 #e1' #h #oev1 step_e1 -> begin
      let (EStringEq e1' e2) = f2 in
      lem_step_implies_steps e1 e1' h oev1;
      lem_step_implies_steps (EStringEq e1 e2) (EStringEq e1' e2) h oev1;
      let lt1 : local_trace h = as_lt oev1 in
      let s2 : steps (EStringEq e1' e2) e' (h++lt1) lt23 = step_estringeq_steps in
      trans_history h lt1 lt23;
      lem_step_preserve_indexed_safe e1 e1' h oev1;
      let (e1'', (| lt1', lt' |)) = destruct_steps_estringeq_e1 e1' e2 e' (h++lt1) lt23 s2 in
      trans_history h lt1 lt1';
      lem_steps_transitive e1 e1' e1'' h lt1 lt1';
      lem_steps_transitive (EStringEq e1 e2) (EStringEq e1' e2) (EStringEq e1'' e2) h lt1 lt1';
      (e1'', (| (lt1 @ lt1'), lt' |))
      end
    | _ -> (e1, (| [], lt |))
    end

let rec destruct_steps_estringeq_e2
  (e1':closed_exp{EString? e1'})
  (e2:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EStringEq e1' e2) e' h lt) :
  Pure (value * (lt2:local_trace h & local_trace (h++lt2)))
    (requires indexed_irred e' (h++lt) /\
      indexed_safe e2 h)
    (ensures fun (e2', (| lt2, lt' |)) ->
      steps e2 e2' h lt2 /\
      steps (EStringEq e1' e2) (EStringEq e1' e2') h lt2 /\
      steps (EStringEq e1' e2') e' (h++lt2) lt' /\
      (lt == (lt2 @ lt')) /\
      (indexed_irred e2 h ==> (lt2 == [] /\ e2 == e2')))
    (decreases st) =
  match st with
  | SRefl (EStringEq e1' e2) h -> begin
    lem_irred_estringeq_implies_irred_e2 e1' e2 h;
    assert (steps e2 e2 h []);
    (e2, (| [], lt |))
    end
  | STrans #e #f2 #e' #h #_ #lt23 step_estringeq step_estringeq_steps -> begin
    let (EStringEq e1 e2) = e in
    match step_estringeq with
    | StringEqRight e1 #e2 #e2' #h #oev2 step_e2 -> begin
      let (EStringEq e1' e2') = f2 in
      lem_step_implies_steps e2 e2' h oev2;
      lem_step_implies_steps (EStringEq e1' e2) (EStringEq e1' e2') h oev2;
      let lt2 : local_trace h = as_lt oev2 in
      let s2 : steps (EStringEq e1' e2') e' (h++lt2) lt23 = step_estringeq_steps in
      trans_history h lt2 lt23;
      lem_step_preserve_indexed_safe e2 e2' h oev2;
      let (e2'', (| lt2', lt' |)) = destruct_steps_estringeq_e2 e1' e2' e' (h++lt2) lt23 s2 in
      trans_history h lt2 lt2';
      lem_steps_transitive e2 e2' e2'' h lt2 lt2';
      lem_steps_transitive (EStringEq e1' e2) (EStringEq e1' e2') (EStringEq e1' e2'') h lt2 lt2';
      (e2'', (| (lt2 @ lt2'), lt' |))
      end
    | StringEqLeft _ _ -> begin
      lem_value_is_irred e1';
      (e2, (| [], lt |))
      end
    | StringEqReturn _ _ _ -> begin
      (e2, (| [], lt |))
      end
    end
#pop-options

let can_step_efst_when_reduced (e12:closed_exp) (h:history) (t1 t2:typ) : Lemma
  (requires indexed_sem_expr_shape (TPair t1 t2) e12 h)
  (ensures (exists e' oev. step (EFst e12) e' h oev))
  =
  introduce indexed_irred e12 h ==> (exists e' oev. step (EFst e12) e' h oev) with _. begin
    assert (steps e12 e12 h []);
    let (EPair e1 e2) = e12 in
    let st : step (EFst (EPair e1 e2)) e1 h None = FstPairReturn h in
    ()
  end;

  introduce ~(indexed_irred e12 h) ==> (exists e' oev. step (EFst e12) e' h oev) with _. begin
    assert (exists e12' oev12. step e12 e12' h oev12);
    eliminate exists e12' oev12. step e12 e12' h oev12 returns exists e' oev. step (EFst e12) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (FstPair st))
    end
  end

let rec destruct_steps_epair_fst
  (e12:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EFst e12) e' h lt)
  (t1 t2:typ) :
  Pure (value * (lt12:local_trace h & local_trace (h++lt12)))
    (requires indexed_irred e' (h++lt) /\
      indexed_sem_expr_shape (TPair t1 t2) e12 h)
    (ensures fun (e12', (| lt12, lt_f |)) ->
      indexed_irred e12' (h++lt12) /\
      steps e12 e12' h lt12 /\
      is_closed (EFst e12') /\
      steps (EFst e12') e' (h++lt12) lt_f /\
      lt == (lt12 @ lt_f) /\
      (indexed_irred e12 h ==> (lt12 == [] /\ e12 == e12')))
    (decreases st)
  = match st with
    | SRefl (EFst e12) h -> begin
      can_step_efst_when_reduced e12 h t1 t2;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_efst step_efst_steps -> begin
      let (EFst e12) = e in
      match step_efst with
      | FstPair #e12 #e12' #h #oev12 step_e12 -> begin
        let (EFst e12') = f2 in
        lem_step_implies_steps e12 e12' h oev12;
        lem_step_implies_steps (EFst e12) (EFst e12') h oev12;
        let lt12 : local_trace h = as_lt oev12 in
        lem_step_preserve_indexed_sem_expr_shape e12 e12' h oev12 (TPair t1 t2);
        let s2 : steps (EFst e12') e' (h++lt12) lt23 = step_efst_steps in
        trans_history h lt12 lt23;
        let (e12'', (| lt12', lt_f |)) = destruct_steps_epair_fst e12' e' (h++lt12) lt23 s2 t1 t2 in
        trans_history h lt12 lt12';
        lem_steps_transitive e12 e12' e12'' h lt12 lt12';
        (e12'', (| (lt12 @ lt12'), lt_f |))
      end
      | FstPairReturn #e1 #e2 h -> begin
        lem_step_implies_steps (EFst (EPair e1 e2)) e1 h None;
        lem_value_is_irred e12;
        (e12, (| [], lt |))
        end
      | _ -> false_elim ()
      end

  (**
    How the steps look like:
      EFst e12 -->* EFst e12' -> e'
  **)

let lem_destruct_steps_epair_fst_core
  (e1:closed_exp{is_value e1})
  (e2:closed_exp{is_value e2})
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (sts:steps (EFst (EPair e1 e2)) e' h lt)
  : Lemma (requires indexed_irred e' (h++lt))
          (ensures (e1 == e') /\ lt == []) =
  lem_value_is_irred e1;
  lem_value_is_irred e2;
  match sts with
  | SRefl _ _ ->
    assert (indexed_irred (EFst (EPair e1 e2)) (h++[]));
    FStar.List.Tot.Properties.append_l_nil h;
    let st : step (EFst (EPair e1 e2)) e1 h None = FstPairReturn h in
    false_elim ()
  | STrans #_ #f2 #_ #_ #_ #lt23 step_efst step_rest ->
    match step_efst with
    | FstPair hst ->
      (match hst with
       | PairLeft _ _ -> false_elim ()
       | PairRight _ _ -> false_elim ())
    | FstPairReturn _ ->
      lem_irred_implies_srefl_steps step_rest

let lem_destruct_steps_epair_fst
  (e1 e2:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h) :
  Lemma (requires (steps (EFst (EPair e1 e2)) e' h lt /\ is_value e1 /\ is_value e2 /\ indexed_irred e' (h++lt)))
        (ensures (e1 == e') /\ lt == []) =
  FStar.Squash.bind_squash #(steps (EFst (EPair e1 e2)) e' h lt) #((e1 == e') /\ lt == []) () (fun sts ->
    lem_destruct_steps_epair_fst_core e1 e2 e' h lt sts
  )

let can_step_esnd_when_reduced (e12:closed_exp) (h:history) (t1 t2:typ) : Lemma
  (requires indexed_sem_expr_shape (TPair t1 t2) e12 h)
  (ensures (exists e' oev. step (ESnd e12) e' h oev))
  =
  introduce indexed_irred e12 h ==> (exists e' oev. step (ESnd e12) e' h oev) with _. begin
    assert (steps e12 e12 h []);
    let (EPair e1 e2) = e12 in
    let st : step (ESnd (EPair e1 e2)) e2 h None = SndPairReturn h in
    ()
  end;

  introduce ~(indexed_irred e12 h) ==> (exists e' oev. step (ESnd e12) e' h oev) with _. begin
    assert (exists e12' oev12. step e12 e12' h oev12);
    eliminate exists e12' oev12. step e12 e12' h oev12 returns exists e' oev. step (ESnd e12) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (SndPair st))
    end
  end

let rec destruct_steps_epair_snd
  (e12:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (ESnd e12) e' h lt)
  (t1 t2:typ) :
  Pure (value * (lt12:local_trace h & local_trace (h++lt12)))
    (requires indexed_irred e' (h++lt) /\
      indexed_sem_expr_shape (TPair t1 t2) e12 h)
    (ensures fun (e12', (| lt12, lt_f |)) ->
      indexed_irred e12' (h++lt12) /\
      steps e12 e12' h lt12 /\
      is_closed (ESnd e12') /\
      steps (ESnd e12') e' (h++lt12) lt_f /\
      lt == (lt12 @ lt_f) /\
      (indexed_irred e12 h ==> (lt12 == [] /\ e12 == e12')))
    (decreases st)
  = match st with
    | SRefl (ESnd e12) h -> begin
      can_step_esnd_when_reduced e12 h t1 t2;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_esnd step_esnd_steps -> begin
      let (ESnd e12) = e in
      match step_esnd with
      | SndPair #e12 #e12' #h #oev12 step_e12 -> begin
        let (ESnd e12') = f2 in
        lem_step_implies_steps e12 e12' h oev12;
        lem_step_implies_steps (ESnd e12) (ESnd e12') h oev12;
        let lt12 : local_trace h = as_lt oev12 in
        lem_step_preserve_indexed_sem_expr_shape e12 e12' h oev12 (TPair t1 t2);
        let s2 : steps (ESnd e12') e' (h++lt12) lt23 = step_esnd_steps in
        trans_history h lt12 lt23;
        let (e12'', (| lt12', lt_f |)) = destruct_steps_epair_snd e12' e' (h++lt12) lt23 s2 t1 t2 in
        trans_history h lt12 lt12';
        lem_steps_transitive e12 e12' e12'' h lt12 lt12';
        (e12'', (| (lt12 @ lt12'), lt_f |))
        end
      | SndPairReturn #e1 #e2 h -> begin
        lem_step_implies_steps (ESnd (EPair e1 e2)) e2 h None;
        lem_value_is_irred e12;
        (e12, (| [], lt |))
        end
      | _ -> false_elim ()
      end

  (**
    How the steps look like:
      ESnd e12 -->* ESnd e12' -> e'
  **)

let lem_destruct_steps_epair_snd_core
  (e1:closed_exp{is_value e1})
  (e2:closed_exp{is_value e2})
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (sts:steps (ESnd (EPair e1 e2)) e' h lt)
  : Lemma (requires indexed_irred e' (h++lt))
          (ensures (e2 == e') /\ lt == []) =
  lem_value_is_irred e1;
  lem_value_is_irred e2;
  match sts with
  | SRefl _ _ ->
    (* SRefl refines e' = ESnd (EPair e1 e2) and lt = [].
       indexed_irred (ESnd (EPair e1 e2)) (h++[]) contradicts SndPairReturn. *)
    assert (indexed_irred (ESnd (EPair e1 e2)) (h++[]));
    FStar.List.Tot.Properties.append_l_nil h;
    let st : step (ESnd (EPair e1 e2)) e2 h None = SndPairReturn h in
    false_elim ()
  | STrans #_ #f2 #_ #_ #_ #lt23 step_esnd step_rest ->
    match step_esnd with
    | SndPair hst ->
      (match hst with
       | PairLeft _ _ -> false_elim ()
       | PairRight _ _ -> false_elim ())
    | SndPairReturn _ ->
      lem_irred_implies_srefl_steps step_rest

let lem_destruct_steps_epair_snd
  (e1 e2:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h) :
  Lemma (requires (steps (ESnd (EPair e1 e2)) e' h lt /\ is_value e1 /\ is_value e2 /\ indexed_irred e' (h++lt)))
        (ensures (e2 == e') /\ lt == []) =
  FStar.Squash.bind_squash #(steps (ESnd (EPair e1 e2)) e' h lt) #((e2 == e') /\ lt == []) () (fun sts ->
    lem_destruct_steps_epair_snd_core e1 e2 e' h lt sts
  )

let srefl_einl_implies_value (e12:closed_exp) (h:history) : Lemma
  (requires indexed_safe e12 h /\ indexed_irred (EInl e12) h)
  (ensures is_value (EInl e12))
  =
  introduce indexed_irred e12 h ==> is_value (EInl e12) with _. begin
    assert (steps e12 e12 h []);
    ()
  end;

  introduce ~(indexed_irred e12 h) ==> is_value (EInl e12) with _. begin
    assert (exists e12' oev12. step e12 e12' h oev12);
    eliminate exists e12' oev12. step e12 e12' h oev12 returns exists e' oev. step (EInl e12) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (SInl st))
    end;
    false_elim ()
  end

let rec destruct_steps_einl
  (e12:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EInl e12) e' h lt) :
  Pure (value * (lt12:local_trace h & local_trace (h++lt12)))
    (requires indexed_irred e' (h++lt) /\
      indexed_safe e12 h)
    (ensures fun (e12', (| lt12, lt_f |)) ->
      indexed_irred e12' (h++lt12) /\
      steps e12 e12' h lt12 /\
      steps (EInl e12) (EInl e12') h lt12 /\
      is_closed (EInl e12') /\
      steps (EInl e12') e' (h++lt12) lt_f /\
      lt == (lt12 @ lt_f) /\
      (indexed_irred e12 h ==> (lt12 == [] /\ e12 == e12')))
    (decreases st)
  = match st with
    | SRefl (EInl e12) h -> begin
      srefl_einl_implies_value e12 h;
      lem_value_is_irred e12;
      (e12, (| [], [] |))
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_einl step_einl_steps -> begin
      let (EInl e12) = e in
      let SInl #e12 #e12' #h #oev12 step_e12 = step_einl in
      let (EInl e12') = f2 in
      lem_step_implies_steps e12 e12' h oev12;
      lem_step_implies_steps (EInl e12) (EInl e12') h oev12;
      let lt12 : local_trace h = as_lt oev12 in
      lem_step_preserve_indexed_safe e12 e12' h oev12;
      let s2 : steps (EInl e12') e' (h++lt12) lt23 = step_einl_steps in
      trans_history h lt12 lt23;
      let (e12'', (| lt12', lt_f |)) = destruct_steps_einl e12' e' (h++lt12) lt23 s2 in
      trans_history h lt12 lt12';
      lem_steps_transitive e12 e12' e12'' h lt12 lt12';
      lem_steps_transitive (EInl e12) (EInl e12') (EInl e12'') h lt12 lt12';
      (e12'', (| (lt12 @ lt12'), lt_f |))
      end

let lem_destruct_steps_einl
  (e12:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h) :
  Lemma (requires steps (EInl e12) e' h lt /\
                  indexed_irred e12 h /\
                  indexed_irred (EInl e12) h)
        (ensures (EInl e12 == e') /\ lt == []) =
  introduce steps (EInl e12) e' h lt ==> ((EInl e12 == e') /\ lt == []) with _. begin
    FStar.Squash.bind_squash #(steps (EInl e12) e' h lt) () (fun sts ->
    match sts with
    | SRefl (EInl e12) h -> ()
    | STrans #e #f2 #e' #h #_ #lt23 step_einl step_einl_steps -> false_elim ()
    )
  end

let srefl_einr_implies_value (e12:closed_exp) (h:history) : Lemma
  (requires indexed_safe e12 h /\ indexed_irred (EInr e12) h)
  (ensures is_value (EInr e12))
  =
  introduce indexed_irred e12 h ==> is_value (EInr e12) with _. begin
    assert (steps e12 e12 h []);
    ()
  end;

  introduce ~(indexed_irred e12 h) ==> is_value (EInr e12) with _. begin
    assert (exists e12' oev12. step e12 e12' h oev12);
    eliminate exists e12' oev12. step e12 e12' h oev12 returns exists e' oev. step (EInr e12) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (SInr st))
    end;
    false_elim ()
  end

let rec destruct_steps_einr
  (e12:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EInr e12) e' h lt) :
  Pure (value * (lt12:local_trace h & local_trace (h++lt12)))
    (requires indexed_irred e' (h++lt) /\
      indexed_safe e12 h)
    (ensures fun (e12', (| lt12, lt_f |)) ->
      indexed_irred e12' (h++lt12) /\
      steps e12 e12' h lt12 /\
      steps (EInr e12) (EInr e12') h lt12 /\
      is_closed (EInr e12') /\
      steps (EInr e12') e' (h++lt12) lt_f /\
      lt == (lt12 @ lt_f) /\
      (indexed_irred e12 h ==> (lt12 == [] /\ e12 == e12')))
    (decreases st)
  = match st with
    | SRefl (EInr e12) h -> begin
      srefl_einr_implies_value e12 h;
      lem_value_is_irred e12;
      (e12, (| [], [] |))
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_einr step_einr_steps -> begin
      let (EInr e12) = e in
      let SInr #e12 #e12' #h #oev12 step_e12 = step_einr in
      let (EInr e12') = f2 in
      lem_step_implies_steps e12 e12' h oev12;
      lem_step_implies_steps (EInr e12) (EInr e12') h oev12;
      let lt12 : local_trace h = as_lt oev12 in
      lem_step_preserve_indexed_safe e12 e12' h oev12;
      let s2 : steps (EInr e12') e' (h++lt12) lt23 = step_einr_steps in
      trans_history h lt12 lt23;
      let (e12'', (| lt12', lt_f |)) = destruct_steps_einr e12' e' (h++lt12) lt23 s2 in
      trans_history h lt12 lt12';
      lem_steps_transitive e12 e12' e12'' h lt12 lt12';
      lem_steps_transitive (EInr e12) (EInr e12') (EInr e12'') h lt12 lt12';
      (e12'', (| (lt12 @ lt12'), lt_f |))
      end

let lem_destruct_steps_einr
  (e12:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h) :
  Lemma (requires steps (EInr e12) e' h lt /\
                  indexed_irred e12 h /\
                  indexed_irred (EInr e12) h)
        (ensures (EInr e12 == e') /\ lt == []) =
  introduce steps (EInr e12) e' h lt ==> ((EInr e12 == e') /\ lt == []) with _. begin
    FStar.Squash.bind_squash #(steps (EInr e12) e' h lt) () (fun sts ->
    match sts with
    | SRefl (EInr e12) h -> ()
    | STrans #e #f2 #e' #h #_ #lt23 step_einr step_einr_steps -> false_elim ()
    )
  end

let can_step_ecase_when_safe (e_case:closed_exp) (e_lc:exp{is_closed (ELam e_lc)}) (e_rc:exp{is_closed (ELam e_rc)}) (h:history) (t1 t2:typ) : Lemma
  (requires indexed_sem_expr_shape (TSum t1 t2) e_case h)
  (ensures (exists e' oev. step (ECase e_case e_lc e_rc) e' h oev))
  =
  introduce indexed_irred e_case h ==> (exists e' oev. step (ECase e_case e_lc e_rc) e' h oev) with _. begin
    match e_case with
    | EInl e_c' -> begin
      assert (steps e_case e_case h []);
      let st : step (ECase (EInl e_c') e_lc e_rc) (subst_beta e_c' e_lc) h None = SInlReturn e_c' e_lc e_rc h in
      ()
      end
    | EInr e_c' -> begin
      assert (steps e_case e_case h []);
      let st : step (ECase (EInr e_c') e_lc e_rc) (subst_beta e_c' e_rc) h None = SInrReturn e_c' e_lc e_rc h in
      ()
      end
    | _ -> begin
      assert (steps e_case e_case h []);
      false_elim ()
      end
  end;

  introduce ~(indexed_irred e_case h) ==> (exists e' oev. step (ECase e_case e_lc e_rc) e' h oev) with _. begin
    assert (exists e_case' oev1. step e_case e_case' h oev1);
    eliminate exists e_case' oev1. step e_case e_case' h oev1 returns exists e' oev. step (ECase e_case e_lc e_rc) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (SCase e_lc e_rc st))
    end
  end

#push-options "--z3rlimit 32"
let rec destruct_steps_ecase
  (e_case:closed_exp)
  (e_lc:exp{is_closed (ELam e_lc)})
  (e_rc:exp{is_closed (ELam e_rc)})
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (ECase e_case e_lc e_rc) e' h lt)
  (t1 t2:typ) :
  Pure (closed_exp * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt) /\
      indexed_sem_expr_shape (TSum t1 t2) e_case h)
    (ensures fun (e_case', (| lt1, lt2 |)) ->
      indexed_irred e_case' (h++lt1) /\
      steps e_case e_case' h lt1 /\
      steps (ECase e_case' e_lc e_rc) e' (h++lt1) lt2 /\
      (EInl? e_case' ==>
        (e_case' == EInl (get_einl_v e_case')) /\
        (steps (ECase e_case e_lc e_rc) (subst_beta (get_einl_v e_case') e_lc) h lt1) /\
        (steps (subst_beta (get_einl_v e_case') e_lc) e' (h++lt1) lt2)) /\
      (EInr? e_case' ==>
        (e_case' == EInr (get_einr_v e_case')) /\
        (steps (ECase e_case e_lc e_rc) (subst_beta (get_einr_v e_case') e_rc) h lt1) /\
        (steps (subst_beta (get_einr_v e_case') e_rc) e' (h++lt1) lt2)) /\
      (lt == lt1 @ lt2) /\
      (indexed_irred e_case h ==> (lt1 == [] /\ e_case == e_case')))
    (decreases st)
  = match st with
    | SRefl (ECase e_case e_lc e_rc) h -> begin
      can_step_ecase_when_safe e_case e_lc e_rc h t1 t2;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_ecase step_ecase_steps -> begin
      let (ECase e_case e_lc e_rc) = e in
      match step_ecase with
      | SCase #e_case e_lc e_rc #e_case' #h #oev1 step_e1 -> begin
        let (ECase e_case' e_lc e_rc) = f2 in
        lem_step_implies_steps e_case e_case' h oev1;
        lem_step_implies_steps (ECase e_case e_lc e_rc) (ECase e_case' e_lc e_rc) h oev1;
        let lt1 : local_trace h = as_lt oev1 in
        lem_step_preserve_indexed_sem_expr_shape e_case e_case' h oev1 (TSum t1 t2);
        let s2 : steps (ECase e_case' e_lc e_rc) e' (h++lt1) lt23 = step_ecase_steps in
        trans_history h lt1 lt23;
        let (e_case'', (| lt1', lt2 |)) = destruct_steps_ecase e_case' e_lc e_rc e' (h++lt1) lt23 s2 t1 t2 in
        trans_history h lt1 lt1';
        lem_steps_transitive e_case e_case' e_case'' h lt1 lt1';
        match e_case'' with
        | EInl v -> begin
          lem_steps_transitive (ECase e_case e_lc e_rc) (ECase e_case' e_lc e_rc) (subst_beta v e_lc) h lt1 lt1';
          (e_case'', (| (lt1 @ lt1'), lt2 |))
          end
        | EInr v -> begin
          lem_steps_transitive (ECase e_case e_lc e_rc) (ECase e_case' e_lc e_rc) (subst_beta v e_rc) h lt1 lt1';
          (e_case'', (| (lt1 @ lt1'), lt2 |))
          end
        | _ -> false_elim ()
        end
      | SInlReturn e_c' e_lc e_rc h -> begin
        lem_step_implies_steps (ECase (EInl e_c') e_lc e_rc) (subst_beta e_c' e_lc) h None;
        lem_value_is_irred (EInl e_c');
        (EInl e_c', (| [], lt |))
        end
      | SInrReturn e_c' e_lc e_rc h -> begin
        lem_step_implies_steps (ECase (EInr e_c') e_lc e_rc) (subst_beta e_c' e_rc) h None;
        lem_value_is_irred (EInr e_c');
        (EInr e_c', (| [], lt |))
        end
      end
#pop-options

let lem_irred_sem_shape_gives_value_shape (t:typ) (e:closed_exp) (h:history) :
  Lemma (requires indexed_irred e h /\ indexed_sem_expr_shape t e h)
        (ensures sem_value_shape t e) =
  assert (steps e e h []);
  assert (indexed_irred e (h++[]))


let ecall_arg_typ (op:io_ops) : typ =
  match op with
  | OOpen -> TString
  | ORead -> TFileDescr
  | OWrite -> TPair TFileDescr TString
  | OClose -> TFileDescr

let can_step_ecall_val (op:io_ops{op <> OWrite}) (arg:closed_exp{sem_value_shape (ecall_arg_typ op) arg}) (h:history) :
  Lemma (exists e' oev. step (ECall op arg) e' h oev)
  =
  match op with
  | ORead ->
    let _ : step (ECall ORead arg) (EInl (EString "")) h (Some (EvRead (get_fd arg) (Inl ""))) = SCallReturn h ORead (get_fd arg) (Inl "") in
    let _ : step (ECall ORead arg) (EInr EUnit) h (Some (EvRead (get_fd arg) (Inr ()))) = SCallReturn h ORead (get_fd arg) (Inr ()) in
    ()
  | OOpen ->
    let _ : step (ECall OOpen arg) (EInl (get_efd (fresh_fd h))) h (Some (EvOpen (get_string arg) (Inl (fresh_fd h)))) = SCallReturn h OOpen (get_string arg) (Inl (fresh_fd h)) in
    let _ : step (ECall OOpen arg) (EInr EUnit) h (Some (EvOpen (get_string arg) (Inr ()))) = SCallReturn h OOpen (get_string arg) (Inr ()) in
    ()
  | OClose ->
    let _ : step (ECall OClose arg) (EInl EUnit) h (Some (EvClose (get_fd arg) (Inl ()))) = SCallReturn h OClose (get_fd arg) (Inl ()) in
    let _ : step (ECall OClose arg) (EInr EUnit) h (Some (EvClose (get_fd arg) (Inr ()))) = SCallReturn h OClose (get_fd arg) (Inr ()) in
    ()

let can_step_ecall (op:io_ops{op <> OWrite}) (arg:closed_exp) (h:history) :
  Lemma
  (requires indexed_sem_expr_shape (ecall_arg_typ op) arg h)
  (ensures (exists e' oev. step (ECall op arg) e' h oev))
  =
  introduce indexed_irred arg h ==> (exists e' oev. step (ECall op arg) e' h oev) with _. begin
    assert (steps arg arg h []);
    lem_irred_sem_shape_gives_value_shape (ecall_arg_typ op) arg h;
    can_step_ecall_val op arg h
  end;

  introduce ~(indexed_irred arg h) ==> (exists e' oev. step (ECall op arg) e' h oev) with _. begin
    assert (exists arg' oev'. step arg arg' h oev');
    eliminate exists arg' oev'. step arg arg' h oev' returns exists e' oev. step (ECall op arg) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (SCall #_ #_ #_ #_ #op st))
    end
  end

let rec destruct_steps_ecall_arg
  (op:io_ops{op <> OWrite})
  (arg:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (ECall op arg) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
  (requires indexed_irred e' (h++lt) /\
    indexed_sem_expr_shape (ecall_arg_typ op) arg h)
  (ensures fun (val_arg, (| lt1, lt' |)) ->
    sem_value_shape (ecall_arg_typ op) val_arg /\
    steps arg val_arg h lt1 /\
    steps (ECall op arg) (ECall op val_arg) h lt1 /\
    steps (ECall op val_arg) e' (h++lt1) lt' /\
    (lt == (lt1 @ lt')))
  (decreases st) =
  match st with
  | SRefl _ h -> begin
    can_step_ecall op arg h;
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
      lem_step_preserve_indexed_sem_expr_shape arg arg' h oev (ecall_arg_typ op);
      let (val_arg, (| lt1', lt' |)) = destruct_steps_ecall_arg op arg' e' (h++lt1) lt23 s2 in
      trans_history h lt1 lt1';
      lem_steps_transitive arg arg' val_arg h lt1 lt1';
      lem_steps_transitive (ECall op arg) (ECall op arg') (ECall op val_arg) h lt1 lt1';
      (val_arg, (| (lt1 @ lt1'), lt' |))
      end
    | _ -> (arg, (| [], lt |))
    end

#push-options "--z3rlimit 32"
let destruct_steps_ecall
  (op:io_ops{op <> OWrite})
  (val_arg:closed_exp{sem_value_shape (ecall_arg_typ op) val_arg})
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (ECall op val_arg) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt))
    (ensures fun (e_r, (| lt1, lt2 |)) ->
       steps (ECall op val_arg) e_r h lt1 /\
       (exists (args:io_args op) (res:io_res op args).
         io_pre h op args /\ io_post h op args res /\
         val_arg == as_e_io_args op args /\
         e_r == as_e_io_res op args res /\
         lt1 == [op_to_ev op args res]) /\
       steps e_r e' (h++lt1) lt2 /\
       (lt == (lt1 @ lt2)))
    (decreases st) =
    match st with
    | SRefl _ h -> begin
      can_step_ecall_val op val_arg h;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_ecall step_ecall_steps -> begin
      match step_ecall with
      | SCallReturn h op args res ->
        lem_step_implies_steps (ECall op (as_e_io_args op args)) (as_e_io_res op args res) h (Some (op_to_ev op args res));
        let lt' : local_trace h = [op_to_ev op args res] in
        trans_history h lt' lt23;
        (f2, (| lt', lt23 |))
      end
#pop-options


let can_step_ewrite_when_fd_arg_value (fd:value{EFileDescr? fd}) (arg:value{EString? arg}) (h:history) :
  Lemma (ensures (exists e' oev. step (ECall OWrite (EPair fd arg)) e' h oev))
  =
  let _ : step (ECall OWrite (EPair fd arg)) (EInl EUnit) h (Some (EvWrite (get_fd fd, get_string arg) (Inl ()))) = SCallReturn h OWrite (get_fd fd, get_string arg) (Inl ()) in
  ()

let lem_irred_ewrite_implies_irred_fd (fd arg:closed_exp) (h:history) :
  Lemma (requires indexed_irred (ECall OWrite (EPair fd arg)) h)
        (ensures indexed_irred fd h) =
  introduce forall fd' oev. step fd fd' h oev ==> False with begin
    introduce _ ==> _ with _. begin
      bind_squash #(step fd fd' h oev) () (fun st ->
      let _ : step (ECall OWrite (EPair fd arg)) (ECall OWrite (EPair fd' arg)) h oev = SCall (PairLeft arg st) in ())
    end
  end

let lem_irred_ewrite_implies_irred_arg (fd:closed_exp{EFileDescr? fd})  (arg:closed_exp) (h:history) :
  Lemma (requires indexed_irred (ECall OWrite (EPair fd arg)) h)
        (ensures indexed_irred arg h) =
  introduce forall arg' oev. step arg arg' h oev ==> False with begin
    introduce _ ==> _ with _. begin
      bind_squash #(step arg arg' h oev) () (fun st ->
      let _ : step (ECall OWrite (EPair fd arg)) (ECall OWrite (EPair fd arg')) h oev = SCall (PairRight fd st) in ())
    end
  end

// Helper: given a step (ECall OWrite (EPair fd arg)) -> (ECall OWrite (EPair fd' arg))
// extract the inner step on fd.
// This works because the only step rule that changes the first arg of EPair inside ECall is PairLeft via SCall.
// Helper: extract the inner step on fd from a step on (ECall OWrite (EPair fd arg)).
// Returns (fd', step fd fd' h oev) given st : step (ECall OWrite (EPair fd arg)) e2 h oev
// where e2 must be of the form ECall OWrite (EPair fd' arg).
let extract_ewrite_fd_step
  (fd:closed_exp) (arg:closed_exp)
  (h:history) (oev:option (event_h h))
  (e2:closed_exp)
  (st:step (ECall OWrite (EPair fd arg)) e2 h oev) :
  Pure (fd':closed_exp & step fd fd' h oev)
    (requires SCall? st /\ PairLeft? (SCall?.hst st))
    (ensures fun _ -> True) =
  let SCall pair_step = st in
  let PairLeft e2_v step_fd = pair_step in
  (| _, step_fd |)

// Helper: extract the inner step on arg from a step on (ECall OWrite (EPair fd arg)).
// Returns (arg', step arg arg' h oev).
let extract_ewrite_arg_step
  (fd:closed_exp{EFileDescr? fd}) (arg:closed_exp)
  (h:history) (oev:option (event_h h))
  (e2:closed_exp)
  (st:step (ECall OWrite (EPair fd arg)) e2 h oev) :
  Pure (arg':closed_exp & step arg arg' h oev)
    (requires SCall? st /\ PairRight? (SCall?.hst st))
    (ensures fun _ -> True) =
  let SCall pair_step = st in
  let PairRight e1_v step_arg = pair_step in
  (| _, step_arg |)

#push-options "--split_queries always --fuel 12 --z3rlimit 12"
let rec destruct_steps_ewrite_fd
  (fd:closed_exp)
  (arg:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (ECall OWrite (EPair fd arg)) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt) /\
      indexed_sem_expr_shape TFileDescr fd h)
    (ensures fun (fd', (| lt1, lt' |)) ->
      EFileDescr? fd' /\
      steps fd fd' h lt1 /\
      steps (ECall OWrite (EPair fd arg)) (ECall OWrite (EPair fd' arg)) h lt1 /\
      steps (ECall OWrite (EPair fd' arg)) e' (h++lt1) lt' /\
      (lt == (lt1 @ lt')))
    (decreases st) =
  match st with
  | SRefl (ECall OWrite (EPair fd arg)) h -> begin
    lem_irred_ewrite_implies_irred_fd fd arg h;
    lem_irred_sem_shape_gives_value_shape TFileDescr fd h;
    (fd, (| [], lt |))
  end
  | STrans #e #f2 #e' #h #_ #lt23 step_ewrite step_ewrite_steps -> begin
    let (ECall OWrite (EPair fd arg)) = e in
    match step_ewrite with
    | SCall #_ #_ #_ #_ #_ pair_step -> begin
      match pair_step with
      | PairLeft #fd arg2 #fd' #h #oev1 step_fd -> begin
        // step_fd : step fd fd' h oev1
        let (ECall OWrite (EPair fd' _)) = f2 in
        lem_step_implies_steps fd fd' h oev1;
        let step_pair_ecall : step (ECall OWrite (EPair fd arg)) (ECall OWrite (EPair fd' arg)) h oev1 =
          SCall (PairLeft arg2 step_fd) in
        lem_step_implies_steps (ECall OWrite (EPair fd arg)) (ECall OWrite (EPair fd' arg)) h oev1;
        let lt1 : local_trace h = as_lt oev1 in
        let s2 : steps (ECall OWrite (EPair fd' arg)) e' (h++lt1) lt23 = step_ewrite_steps in
        trans_history h lt1 lt23;
        lem_step_preserve_indexed_sem_expr_shape fd fd' h oev1 TFileDescr;
        let (fd'', (| lt1', lt' |)) = destruct_steps_ewrite_fd fd' arg e' (h++lt1) lt23 s2 in
        trans_history h lt1 lt1';
        lem_steps_transitive fd fd' fd'' h lt1 lt1';
        lem_steps_transitive (ECall OWrite (EPair fd arg)) (ECall OWrite (EPair fd' arg)) (ECall OWrite (EPair fd'' arg)) h lt1 lt1';
        (fd'', (| (lt1 @ lt1'), lt' |))
        end
      | PairRight fd_v #arg2 #arg' #h #oev1 step_arg -> begin
        // fd is already a value (fd = fd_v), only arg steps
        lem_value_is_irred fd_v;
        lem_irred_sem_shape_gives_value_shape TFileDescr fd_v h;
        (fd_v, (| [], lt |))
        end
      end
    | SCallReturn h_sr OWrite args_sr _ -> begin
      // SCallReturn on OWrite means fd = EFileDescr fd_t is already in args_sr
      // fd = EFileDescr (fst args_sr)
      assert (fd == EFileDescr (fst args_sr));
      (fd, (| [], lt |))
      end
    end
#pop-options

#push-options "--split_queries always --fuel 12 --z3rlimit 12"
let rec destruct_steps_ewrite_arg
  (fd':closed_exp{EFileDescr? fd'})
  (arg:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (ECall OWrite (EPair fd' arg)) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt) /\
      indexed_sem_expr_shape TString arg h)
    (ensures fun (arg', (| lt1, lt' |)) ->
      EString? arg' /\
      steps arg arg' h lt1 /\
      steps (ECall OWrite (EPair fd' arg)) (ECall OWrite (EPair fd' arg')) h lt1 /\
      steps (ECall OWrite (EPair fd' arg')) e' (h++lt1) lt' /\
      (lt == (lt1 @ lt')))
    (decreases st) =
  match st with
  | SRefl (ECall OWrite (EPair fd' arg)) h -> begin
    lem_irred_ewrite_implies_irred_arg fd' arg h;
    (arg, (| [], lt |))
    end
  | STrans #e #f2 #e' #h #oev #lt23 step_ewrite step_ewrite_steps -> begin
    let (ECall OWrite (EPair fd' arg)) = e in
    match step_ewrite with
    | SCall #_ #_ #_ #oev2 #_ (PairRight fd_v #arg2 #arg' #h2 #oev3 step_arg) -> begin
      // step_arg : step arg arg' h2 oev3
      let (ECall OWrite (EPair _ arg')) = f2 in
      lem_step_implies_steps arg arg' h2 oev3;
      lem_step_implies_steps (ECall OWrite (EPair fd_v arg2)) (ECall OWrite (EPair fd_v arg')) h2 oev3;
      let lt1 : local_trace h = as_lt oev in
      let s2 : steps (ECall OWrite (EPair fd' arg')) e' (h++lt1) lt23 = step_ewrite_steps in
      trans_history h lt1 lt23;
      lem_step_preserve_indexed_sem_expr_shape arg arg' h2 oev3 TString;
      let (arg'', (| lt1', lt' |)) = destruct_steps_ewrite_arg fd' arg' e' (h++lt1) lt23 s2 in
      trans_history h lt1 lt1';
      lem_steps_transitive arg arg' arg'' h lt1 lt1';
      lem_steps_transitive (ECall OWrite (EPair fd' arg)) (ECall OWrite (EPair fd' arg')) (ECall OWrite (EPair fd' arg'')) h lt1 lt1';
      (arg'', (| (lt1 @ lt1'), lt' |))
      end
    | SCall #_ #_ #_ #_ #_ (PairLeft _ _) -> (arg, (| [], lt |))
    | SCallReturn _ _ _ _ -> (arg, (| [], lt |))
    end
#pop-options

#push-options "--z3rlimit 32"
let destruct_steps_ewrite
  (fd':closed_exp{EFileDescr? fd'})
  (arg':closed_exp{EString? arg'})
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (ECall OWrite (EPair fd' arg')) e' h lt) :
  Pure (closed_exp * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt))
    (ensures fun (e_r, (| lt1, lt2 |)) ->
      steps (ECall OWrite (EPair fd' arg')) e_r h lt1 /\
      (e_r == EInl EUnit \/ e_r == EInr EUnit) /\
      (EString? arg' ==>
        (EInl? e_r ==> steps e_r e' (h++lt1) lt2 /\ lt == (lt1 @ lt2) /\ lt1 == [EvWrite (get_fd fd', get_string arg') (Inl ())]) /\
        (EInr? e_r ==> steps e_r e' (h++lt1) lt2 /\ lt == (lt1 @ lt2) /\ lt1 == [EvWrite (get_fd fd', get_string arg') (Inr ())])) /\
      (lt == (lt1 @ lt2) \/ lt == (lt1 @ lt2)))
    (decreases st) =
    match st with
    | SRefl (ECall OWrite (EPair fd' arg')) h -> begin
      can_step_ewrite_when_fd_arg_value fd' arg' h;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_ewrite step_ewrite_steps -> begin
      let (ECall OWrite (EPair fd' arg')) = e in
      match step_ewrite with
      | SCallReturn h OWrite (fd_t, arg_t) (Inl ()) -> begin
        let EInl EUnit = f2 in
        lem_step_implies_steps (ECall OWrite (EPair (get_efd fd_t) (EString arg_t))) (EInl EUnit) h (Some (EvWrite (fd_t, arg_t) (Inl ())));
        let lt' : local_trace h = [EvWrite (fd_t, arg_t) (Inl ())] in
        let s2 : steps (EInl EUnit) e' (h++lt') lt23 = step_ewrite_steps in
        trans_history h lt' lt23;
        lem_value_preserves_value EUnit (h++lt') TUnit;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einl EUnit e' (h++lt') lt23 s2 in
        (f2, (| lt', (lt12 @ lt_f) |))
        end
      | SCallReturn h OWrite (fd_t, arg_t) (Inr ()) -> begin
        let EInr EUnit = f2 in
        lem_step_implies_steps (ECall OWrite (EPair (get_efd fd_t) (EString arg_t))) (EInr EUnit) h (Some (EvWrite (fd_t, arg_t) (Inr ())));
        let lt' : local_trace h = [EvWrite (fd_t, arg_t) (Inr ())] in
        let s2 : steps (EInr EUnit) e' (h++lt') lt23 = step_ewrite_steps in
        trans_history h lt' lt23;
        lem_value_preserves_value EUnit (h++lt') TUnit;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einr EUnit e' (h++lt') lt23 s2 in
        (f2, (| lt', (lt12 @ lt_f) |))
        end
      | SCall #_ #_ #_ #_ #_ (PairRight _ _) -> false_elim ()
      | SCall #_ #_ #_ #_ #_ (PairLeft _ _) -> false_elim ()
      end
#pop-options
