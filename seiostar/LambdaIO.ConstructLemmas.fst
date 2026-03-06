module LambdaIO.ConstructLemmas

open LambdaIO

// CONSTRUCT LEMMAS
let rec construct_steps_eapp_e1
  (e1:closed_exp)
  (e11:exp{is_closed (ELam e11)})
  (e2:closed_exp)
  (h:history)
  (lt1:local_trace h)
  (st1:steps e1 (ELam e11) h lt1) :
  Lemma
    (requires indexed_irred (ELam e11) (h++lt1))
    (ensures steps (EApp e1 e2) (EApp (ELam e11) e2) h lt1)
    (decreases st1) =
  match st1 with
  | SRefl e1 h -> ()
  | STrans #e1 #e1' #_ #h #oev1 #lt23 step_e1 step_e1_steps -> begin
    let _ : step (EApp e1 e2) (EApp e1' e2) h oev1 = AppLeft e2 step_e1 in
    lem_step_implies_steps (EApp e1 e2) (EApp e1' e2) h oev1;
    let lt' : local_trace h = as_lt oev1 in
    let s2 : steps e1' (ELam e11) (h++lt') lt23 = step_e1_steps in
    trans_history h lt' lt23;
    construct_steps_eapp_e1 e1' e11 e2 (h++lt') lt23 s2;
    lem_steps_transitive (EApp e1 e2) (EApp e1' e2) (EApp (ELam e11) e2) h lt' lt23
    end

let rec construct_steps_eapp_e2
  (e11:exp{is_closed (ELam e11)})
  (e2:closed_exp)
  (e2':closed_exp{is_value e2'})
  (h:history)
  (lt2:local_trace h)
  (st2:steps e2 e2' h lt2) :
  Lemma
    (requires indexed_irred e2' (h++lt2))
    (ensures steps (EApp (ELam e11) e2) (EApp (ELam e11) e2') h lt2)
    (decreases st2) =
  match st2 with
  | SRefl e2 h -> ()
  | STrans #e2 #e2_ #e2' #h #oev2 #lt23 step_e2 step_e2_steps -> begin
    let _ : step (EApp (ELam e11) e2) (EApp (ELam e11) e2_) h oev2 = AppRight (ELam e11) step_e2 in
    lem_step_implies_steps (EApp (ELam e11) e2) (EApp (ELam e11) e2_) h oev2;
    let lt' : local_trace h = as_lt oev2 in
    let s2 : steps e2_ e2' (h++lt') lt23 = step_e2_steps in
    trans_history h lt' lt23;
    construct_steps_eapp_e2 e11 e2_ e2' (h++lt') lt23 s2;
    lem_steps_transitive (EApp (ELam e11) e2) (EApp (ELam e11) e2_) (EApp (ELam e11) e2') h lt' lt23
    end

let construct_steps_eapp
  (e1:closed_exp)
  (e11:exp{is_closed (ELam e11)})
  (e2:closed_exp)
  (e2':closed_exp{is_value e2'})
  (e':closed_exp)
  (h:history)
  (lt1:local_trace h)
  (lt2:local_trace (h++lt1))
  (lt3:local_trace ((h++lt1)++lt2))
  (sts1:steps e1 (ELam e11) h lt1)
  (sts2:steps e2 e2' (h++lt1) lt2)
  (sts3:steps (subst_beta e2' e11) e' ((h++lt1)++lt2) lt3) :
  Lemma (requires indexed_irred (ELam e11) (h++lt1) /\
                  indexed_irred e2' ((h++lt1)++lt2) /\
                  indexed_irred e' (((h++lt1)++lt2)++lt3))
        (ensures steps (EApp e1 e2) e' h (lt1@(lt2@lt3))) =
  construct_steps_eapp_e1 e1 e11 e2 h lt1 sts1;
  construct_steps_eapp_e2 e11 e2 e2' (h++lt1) lt2 sts2;
  lem_steps_transitive (EApp e1 e2) (EApp (ELam e11) e2) (EApp (ELam e11) e2') h lt1 lt2;
  let _ : step (EApp (ELam e11) e2') (subst_beta e2' e11) ((h++lt1)++lt2) None = Beta e11 e2' ((h++lt1)++lt2) in
  lem_step_implies_steps (EApp (ELam e11) e2') (subst_beta e2' e11) ((h++lt1)++lt2) None;
  lem_steps_transitive (EApp (ELam e11) e2') (subst_beta e2' e11) e' ((h++lt1)++lt2) [] lt3;
  trans_history h lt1 lt2;
  lem_steps_transitive (EApp e1 e2) (EApp (ELam e11) e2') e' h (lt1@lt2) lt3;
  associative_history lt1 lt2 lt3;
  assert (steps (EApp e1 e2) e' h (lt1@(lt2@lt3)))

let rec construct_steps_epair_e1
  (e1:closed_exp)
  (e1':closed_exp{is_value e1'})
  (e2:closed_exp)
  (h:history)
  (lt1:local_trace h)
  (st1:steps e1 e1' h lt1) :
  Lemma
    (requires indexed_irred e1' (h++lt1))
    (ensures steps (EPair e1 e2) (EPair e1' e2) h lt1)
    (decreases st1) =
  match st1 with
  | SRefl e1 h -> ()
  | STrans #e1 #e1_ #_ #h #oev1 #lt23 step_e1 step_e1_steps -> begin
    let _ : step (EPair e1 e2) (EPair e1_ e2) h oev1 = PairLeft e2 step_e1 in
    lem_step_implies_steps (EPair e1 e2) (EPair e1_ e2) h oev1;
    let lt' : local_trace h = as_lt oev1 in
    let s2 : steps e1_ e1' (h++lt') lt23 = step_e1_steps in
    trans_history h lt' lt23;
    construct_steps_epair_e1 e1_ e1' e2 (h++lt') lt23 s2;
    lem_steps_transitive (EPair e1 e2) (EPair e1_ e2) (EPair e1' e2) h lt' lt23
    end

let rec construct_steps_epair_e2
  (e1':closed_exp{is_value e1'})
  (e2:closed_exp)
  (e2':closed_exp{is_value e2'})
  (h:history)
  (lt2:local_trace h)
  (st2:steps e2 e2' h lt2) :
  Lemma
    (requires indexed_irred e2' (h++lt2))
    (ensures steps (EPair e1' e2) (EPair e1' e2') h lt2)
    (decreases st2) =
  match st2 with
  | SRefl e2 h -> ()
  | STrans #e2 #e2_ #_ #h #oev2 #lt23 step_e2 step_e2_steps -> begin
    let _ : step (EPair e1' e2) (EPair e1' e2_) h oev2 = PairRight e1' step_e2 in
    lem_step_implies_steps (EPair e1' e2) (EPair e1' e2_) h oev2;
    let lt' : local_trace h = as_lt oev2 in
    let s2 : steps e2_ e2' (h++lt') lt23 = step_e2_steps in
    trans_history h lt' lt23;
    construct_steps_epair_e2 e1' e2_ e2' (h++lt') lt23 s2;
    lem_steps_transitive (EPair e1' e2) (EPair e1' e2_) (EPair e1' e2') h lt' lt23
    end

let construct_steps_epair
  (e1:closed_exp)
  (e1':closed_exp{is_value e1'})
  (e2:closed_exp)
  (e2':closed_exp{is_value e2'})
  (h:history)
  (lt1:local_trace h)
  (lt2:local_trace (h++lt1))
  (sts1:steps e1 e1' h lt1)
  (sts2:steps e2 e2' (h++lt1) lt2) :
  Lemma (requires indexed_irred e1' (h++lt1) /\
                  indexed_irred e2' ((h++lt1)++lt2))
        (ensures steps (EPair e1 e2) (EPair e1' e2') h (lt1@lt2)) =
  construct_steps_epair_e1 e1 e1' e2 h lt1 sts1;
  construct_steps_epair_e2 e1' e2 e2' (h++lt1) lt2 sts2;
  trans_history h lt1 lt2;
  lem_steps_transitive (EPair e1 e2) (EPair e1' e2) (EPair e1' e2') h lt1 lt2

let rec construct_steps_estringeq_e1
  (e1:closed_exp)
  (e1':closed_exp{EString? e1'})
  (e2:closed_exp)
  (h:history)
  (lt1:local_trace h)
  (st1:steps e1 e1' h lt1) :
  Lemma
    (requires indexed_irred e1' (h++lt1))
    (ensures steps (EStringEq e1 e2) (EStringEq e1' e2) h lt1)
    (decreases st1) =
  match st1 with
  | SRefl e1 h -> ()
  | STrans #e1 #e1_ #_ #h #oev1 #lt23 step_e1 step_e1_steps -> begin
    let _ : step (EStringEq e1 e2) (EStringEq e1_ e2) h oev1 = StringEqLeft e2 step_e1 in
    lem_step_implies_steps (EStringEq e1 e2) (EStringEq e1_ e2) h oev1;
    let lt' : local_trace h = as_lt oev1 in
    let s2 : steps e1_ e1' (h++lt') lt23 = step_e1_steps in
    trans_history h lt' lt23;
    construct_steps_estringeq_e1 e1_ e1' e2 (h++lt') lt23 s2;
    lem_steps_transitive (EStringEq e1 e2) (EStringEq e1_ e2) (EStringEq e1' e2) h lt' lt23
    end

let rec construct_steps_estringeq_e2
  (e1':closed_exp{EString? e1'})
  (e2:closed_exp)
  (e2':closed_exp{EString? e2'})
  (h:history)
  (lt2:local_trace h)
  (st2:steps e2 e2' h lt2) :
  Lemma
    (requires indexed_irred e2' (h++lt2))
    (ensures steps (EStringEq e1' e2) (EStringEq e1' e2') h lt2)
    (decreases st2) =
  match st2 with
  | SRefl e2 h -> ()
  | STrans #e2 #e2_ #_ #h #oev2 #lt23 step_e2 step_e2_steps -> begin
    let _ : step (EStringEq e1' e2) (EStringEq e1' e2_) h oev2 = StringEqRight e1' step_e2 in
    lem_step_implies_steps (EStringEq e1' e2) (EStringEq e1' e2_) h oev2;
    let lt' : local_trace h = as_lt oev2 in
    let s2 : steps e2_ e2' (h++lt') lt23 = step_e2_steps in
    trans_history h lt' lt23;
    construct_steps_estringeq_e2 e1' e2_ e2' (h++lt') lt23 s2;
    lem_steps_transitive (EStringEq e1' e2) (EStringEq e1' e2_) (EStringEq e1' e2') h lt' lt23
    end

let construct_steps_estringeq
  (e1:closed_exp)
  (e1':closed_exp{EString? e1'})
  (e2:closed_exp)
  (e2':closed_exp{EString? e2'})
  (h:history)
  (lt1:local_trace h)
  (lt2:local_trace (h++lt1))
  (sts1:steps e1 e1' h lt1)
  (sts2:steps e2 e2' (h++lt1) lt2) :
  Lemma (requires indexed_irred e1' (h++lt1) /\
                  indexed_irred e2' ((h++lt1)++lt2))
        (ensures steps (EStringEq e1 e2) (EStringEq e1' e2') h (lt1@lt2)) =
  construct_steps_estringeq_e1 e1 e1' e2 h lt1 sts1;
  construct_steps_estringeq_e2 e1' e2 e2' (h++lt1) lt2 sts2;
  trans_history h lt1 lt2;
  lem_steps_transitive (EStringEq e1 e2) (EStringEq e1' e2) (EStringEq e1' e2') h lt1 lt2

let rec construct_steps_efst
  (e12:closed_exp)
  (e12':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps e12 e12' h lt) :
  Lemma
    (requires indexed_irred e12' (h++lt))
    (ensures steps (EFst e12) (EFst e12') h lt)
    (decreases st) =
  match st with
  | SRefl _ _ -> ()
  | STrans #_ #e12_ #_ #_ #oev #lt23 step12 rest -> begin
    let _ : step (EFst e12) (EFst e12_) h oev = FstPair step12 in
    lem_step_implies_steps (EFst e12) (EFst e12_) h oev;
    let lt' : local_trace h = as_lt oev in
    trans_history h lt' lt23;
    construct_steps_efst e12_ e12' (h++lt') lt23 rest;
    lem_steps_transitive (EFst e12) (EFst e12_) (EFst e12') h lt' lt23
    end

let rec construct_steps_esnd
  (e12:closed_exp)
  (e12':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps e12 e12' h lt) :
  Lemma
    (requires indexed_irred e12' (h++lt))
    (ensures steps (ESnd e12) (ESnd e12') h lt)
    (decreases st) =
  match st with
  | SRefl _ _ -> ()
  | STrans #_ #e12_ #_ #_ #oev #lt23 step12 rest -> begin
    let _ : step (ESnd e12) (ESnd e12_) h oev = SndPair step12 in
    lem_step_implies_steps (ESnd e12) (ESnd e12_) h oev;
    let lt' : local_trace h = as_lt oev in
    trans_history h lt' lt23;
    construct_steps_esnd e12_ e12' (h++lt') lt23 rest;
    lem_steps_transitive (ESnd e12) (ESnd e12_) (ESnd e12') h lt' lt23
    end

let rec construct_steps_einl
  (e:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps e e' h lt) :
  Lemma
    (requires indexed_irred e' (h++lt))
    (ensures steps (EInl e) (EInl e') h lt)
    (decreases st) =
  match st with
  | SRefl _ _ -> ()
  | STrans #_ #e_ #_ #_ #oev #lt23 step_e rest -> begin
    let _ : step (EInl e) (EInl e_) h oev = SInl step_e in
    lem_step_implies_steps (EInl e) (EInl e_) h oev;
    let lt' : local_trace h = as_lt oev in
    trans_history h lt' lt23;
    construct_steps_einl e_ e' (h++lt') lt23 rest;
    lem_steps_transitive (EInl e) (EInl e_) (EInl e') h lt' lt23
    end

let rec construct_steps_einr
  (e:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps e e' h lt) :
  Lemma
    (requires indexed_irred e' (h++lt))
    (ensures steps (EInr e) (EInr e') h lt)
    (decreases st) =
  match st with
  | SRefl _ _ -> ()
  | STrans #_ #e_ #_ #_ #oev #lt23 step_e rest -> begin
    let _ : step (EInr e) (EInr e_) h oev = SInr step_e in
    lem_step_implies_steps (EInr e) (EInr e_) h oev;
    let lt' : local_trace h = as_lt oev in
    trans_history h lt' lt23;
    construct_steps_einr e_ e' (h++lt') lt23 rest;
    lem_steps_transitive (EInr e) (EInr e_) (EInr e') h lt' lt23
    end

let rec construct_steps_eopen
  (e:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps e e' h lt) :
  Lemma
    (requires indexed_irred e' (h++lt))
    (ensures steps (EOpen e) (EOpen e') h lt)
    (decreases st) =
  match st with
  | SRefl _ _ -> ()
  | STrans #_ #e_ #_ #_ #oev #lt23 step_e rest -> begin
    let _ : step (EOpen e) (EOpen e_) h oev = SOpen step_e in
    lem_step_implies_steps (EOpen e) (EOpen e_) h oev;
    let lt' : local_trace h = as_lt oev in
    trans_history h lt' lt23;
    construct_steps_eopen e_ e' (h++lt') lt23 rest;
    lem_steps_transitive (EOpen e) (EOpen e_) (EOpen e') h lt' lt23
    end

let rec construct_steps_eread
  (e:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps e e' h lt) :
  Lemma
    (requires indexed_irred e' (h++lt))
    (ensures steps (ERead e) (ERead e') h lt)
    (decreases st) =
  match st with
  | SRefl _ _ -> ()
  | STrans #_ #e_ #_ #_ #oev #lt23 step_e rest -> begin
    let _ : step (ERead e) (ERead e_) h oev = SRead step_e in
    lem_step_implies_steps (ERead e) (ERead e_) h oev;
    let lt' : local_trace h = as_lt oev in
    trans_history h lt' lt23;
    construct_steps_eread e_ e' (h++lt') lt23 rest;
    lem_steps_transitive (ERead e) (ERead e_) (ERead e') h lt' lt23
    end

let rec construct_steps_eclose
  (e:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps e e' h lt) :
  Lemma
    (requires indexed_irred e' (h++lt))
    (ensures steps (EClose e) (EClose e') h lt)
    (decreases st) =
  match st with
  | SRefl _ _ -> ()
  | STrans #_ #e_ #_ #_ #oev #lt23 step_e rest -> begin
    let _ : step (EClose e) (EClose e_) h oev = SClose step_e in
    lem_step_implies_steps (EClose e) (EClose e_) h oev;
    let lt' : local_trace h = as_lt oev in
    trans_history h lt' lt23;
    construct_steps_eclose e_ e' (h++lt') lt23 rest;
    lem_steps_transitive (EClose e) (EClose e_) (EClose e') h lt' lt23
    end

let rec construct_steps_ewrite_fd
  (fd:closed_exp)
  (fd':closed_exp)
  (msg:closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps fd fd' h lt) :
  Lemma
    (requires indexed_irred fd' (h++lt))
    (ensures steps (EWrite fd msg) (EWrite fd' msg) h lt)
    (decreases st) =
  match st with
  | SRefl _ _ -> ()
  | STrans #_ #fd_ #_ #_ #oev #lt23 step_fd rest -> begin
    let _ : step (EWrite fd msg) (EWrite fd_ msg) h oev = SWriteFd msg step_fd in
    lem_step_implies_steps (EWrite fd msg) (EWrite fd_ msg) h oev;
    let lt' : local_trace h = as_lt oev in
    trans_history h lt' lt23;
    construct_steps_ewrite_fd fd_ fd' msg (h++lt') lt23 rest;
    lem_steps_transitive (EWrite fd msg) (EWrite fd_ msg) (EWrite fd' msg) h lt' lt23
    end

let rec construct_steps_ewrite_arg
  (fd:closed_exp{EFileDescr? fd})
  (msg:closed_exp)
  (msg':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps msg msg' h lt) :
  Lemma
    (requires indexed_irred msg' (h++lt))
    (ensures steps (EWrite fd msg) (EWrite fd msg') h lt)
    (decreases st) =
  match st with
  | SRefl _ _ -> ()
  | STrans #_ #msg_ #_ #_ #oev #lt23 step_msg rest -> begin
    let _ : step (EWrite fd msg) (EWrite fd msg_) h oev = SWriteArg fd step_msg in
    lem_step_implies_steps (EWrite fd msg) (EWrite fd msg_) h oev;
    let lt' : local_trace h = as_lt oev in
    trans_history h lt' lt23;
    construct_steps_ewrite_arg fd msg_ msg' (h++lt') lt23 rest;
    lem_steps_transitive (EWrite fd msg) (EWrite fd msg_) (EWrite fd msg') h lt' lt23
    end

let rec construct_steps_ecase_cond
  (e1:closed_exp)
  (e1':closed_exp)
  (e2:exp{is_closed (ELam e2)})
  (e3:exp{is_closed (ELam e3)})
  (h:history)
  (lt1:local_trace h)
  (sts1:steps e1 e1' h lt1) :
  Lemma
    (requires indexed_irred e1' (h++lt1))
    (ensures steps (ECase e1 e2 e3) (ECase e1' e2 e3) h lt1)
    (decreases sts1) =
  match sts1 with
  | SRefl _ _ -> ()
  | STrans #_ #e1_ #_ #_ #oev1 #lt23 step_e1 step_e1_steps -> begin
    let _ : step (ECase e1 e2 e3) (ECase e1_ e2 e3) h oev1 = SCase e2 e3 step_e1 in
    lem_step_implies_steps (ECase e1 e2 e3) (ECase e1_ e2 e3) h oev1;
    let lt' : local_trace h = as_lt oev1 in
    trans_history h lt' lt23;
    construct_steps_ecase_cond e1_ e1' e2 e3 (h++lt') lt23 step_e1_steps;
    lem_steps_transitive (ECase e1 e2 e3) (ECase e1_ e2 e3) (ECase e1' e2 e3) h lt' lt23
    end

let construct_steps_ecase_inl
  (e1:closed_exp)
  (v:closed_exp{is_value v})
  (e2:exp{is_closed (ELam e2)})
  (e3:exp{is_closed (ELam e3)})
  (e':closed_exp)
  (h:history)
  (lt1:local_trace h)
  (lt2:local_trace (h++lt1))
  (sts1:steps e1 (EInl v) h lt1)
  (sts2:steps (subst_beta v e2) e' (h++lt1) lt2) :
  Lemma
    (requires indexed_irred (EInl v) (h++lt1) /\
              indexed_irred e' ((h++lt1)++lt2))
    (ensures steps (ECase e1 e2 e3) e' h (lt1@lt2)) =
  construct_steps_ecase_cond e1 (EInl v) e2 e3 h lt1 sts1;
  let _ : step (ECase (EInl v) e2 e3) (subst_beta v e2) (h++lt1) None = SInlReturn v e2 e3 (h++lt1) in
  lem_step_implies_steps (ECase (EInl v) e2 e3) (subst_beta v e2) (h++lt1) None;
  trans_history h lt1 lt2;
  lem_steps_transitive (ECase (EInl v) e2 e3) (subst_beta v e2) e' (h++lt1) [] lt2;
  lem_steps_transitive (ECase e1 e2 e3) (ECase (EInl v) e2 e3) e' h lt1 lt2

let construct_steps_ecase_inr
  (e1:closed_exp)
  (v:closed_exp{is_value v})
  (e2:exp{is_closed (ELam e2)})
  (e3:exp{is_closed (ELam e3)})
  (e':closed_exp)
  (h:history)
  (lt1:local_trace h)
  (lt2:local_trace (h++lt1))
  (sts1:steps e1 (EInr v) h lt1)
  (sts2:steps (subst_beta v e3) e' (h++lt1) lt2) :
  Lemma
    (requires indexed_irred (EInr v) (h++lt1) /\
              indexed_irred e' ((h++lt1)++lt2))
    (ensures steps (ECase e1 e2 e3) e' h (lt1@lt2)) =
  construct_steps_ecase_cond e1 (EInr v) e2 e3 h lt1 sts1;
  let _ : step (ECase (EInr v) e2 e3) (subst_beta v e3) (h++lt1) None = SInrReturn v e2 e3 (h++lt1) in
  lem_step_implies_steps (ECase (EInr v) e2 e3) (subst_beta v e3) (h++lt1) None;
  trans_history h lt1 lt2;
  lem_steps_transitive (ECase (EInr v) e2 e3) (subst_beta v e3) e' (h++lt1) [] lt2;
  lem_steps_transitive (ECase e1 e2 e3) (ECase (EInr v) e2 e3) e' h lt1 lt2


let rec construct_steps_eif_e1
  (e1:closed_exp)
  (e1':closed_exp{ETrue? e1' \/ EFalse? e1'})
  (e2:closed_exp)
  (e3:closed_exp)
  (h:history)
  (lt1:local_trace h)
  (sts1:steps e1 e1' h lt1) :
  Lemma
    (requires indexed_irred e1' (h++lt1))
    (ensures steps (EIf e1 e2 e3) (EIf e1' e2 e3) h lt1)
    (decreases sts1) =
  match sts1 with
  | SRefl e1 h -> ()
  | STrans #e1 #e1_ #_ #h #oev1 #lt23 step_e1 step_e1_steps -> begin
    let _ : step (EIf e1 e2 e3) (EIf e1_ e2 e3) h oev1 = IfCond e2 e3 step_e1 in
    lem_step_implies_steps (EIf e1 e2 e3) (EIf e1_ e2 e3) h oev1;
    let lt' : local_trace h = as_lt oev1 in
    let s2 : steps e1_ e1' (h++lt') lt23 = step_e1_steps in
    trans_history h lt' lt23;
    construct_steps_eif_e1 e1_ e1' e2 e3 (h++lt') lt23 s2;
    lem_steps_transitive (EIf e1 e2 e3) (EIf e1_ e2 e3) (EIf e1' e2 e3) h lt' lt23
    end

let construct_steps_eif
  (e1:closed_exp)
  (e1':closed_exp{ETrue? e1' \/ EFalse? e1'})
  (e2:closed_exp)
  (e3:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt1:local_trace h)
  (lt2:local_trace (h++lt1))
  (sts1:steps e1 e1' h lt1)
  (sts2:steps (match e1' with | ETrue -> e2 | EFalse -> e3) e' (h++lt1) lt2) :
  Lemma
    (requires indexed_irred e1' (h++lt1) /\
              indexed_irred e' ((h++lt1)++lt2))
    (ensures steps (EIf e1 e2 e3) e' h (lt1@lt2))
    (decreases sts1) =
  construct_steps_eif_e1 e1 e1' e2 e3 h lt1 sts1;
  let e_tf = match e1' with | ETrue -> e2 | EFalse -> e3 in
  let _ : step (EIf e1' e2 e3) e_tf (h++lt1) None =
    match e1' with
    | ETrue -> IfTrue e2 e3 (h++lt1)
    | EFalse -> IfFalse e2 e3 (h++lt1) in
  lem_step_implies_steps (EIf e1' e2 e3) e_tf (h++lt1) None;
  trans_history h lt1 lt2;
  lem_steps_transitive (EIf e1' e2 e3) e_tf e' (h++lt1) [] lt2;
  lem_steps_transitive (EIf e1 e2 e3) (EIf e1' e2 e3) e'  h lt1 lt2
