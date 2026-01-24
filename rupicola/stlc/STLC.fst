(* Substitution proof from: https://fstar-lang.org/tutorial/book/part2/part2_stlc.html *)

module STLC

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

type typ =
  | TUnit  : typ
  | TBool  : typ
  | TNat   : typ
  | TArr   : typ -> typ -> typ
  | TPair  : typ -> typ -> typ
  | TSum   : typ -> typ -> typ

let var = nat
type exp =
  | EUnit  : exp
  | ETrue  : exp
  | EFalse : exp
  | EZero  : exp
  | ESucc  : exp -> exp
  | ENRec  : exp -> exp -> exp -> exp
  | EIf    : exp -> exp -> exp -> exp
  | EVar   : v:var -> exp
  | ELam   : b:exp -> exp
  | EApp   : exp -> exp -> exp
  | EPair  : fst:exp -> snd:exp -> exp
  | EFst   : exp -> exp
  | ESnd   : exp -> exp
  | EInl   : exp -> exp
  | EInr   : exp -> exp
  | ECase  : exp -> exp -> exp -> exp

(* Parallel substitution operation `subst` *)
let sub (renaming:bool) =
    f:(var -> exp){ renaming <==> (forall x. EVar? (f x)) }

let bool_order (b:bool) = if b then 0 else 1

let sub_inc
  : sub true
  = fun y -> EVar (y+1)

let is_var (e:exp) : int = if EVar? e then 0 else 1

let rec subst (#r:bool)
              (s:sub r)
              (e:exp)
  : Tot (e':exp { r ==> (EVar? e <==> EVar? e') })
        (decreases %[bool_order (EVar? e);
                     bool_order r;
                     1;
                     e])
  = match e with
    | EVar x -> s x
    | ELam e1 -> ELam (subst (sub_elam s) e1)
    | EApp e1 e2 -> EApp (subst s e1) (subst s e2)
    | EIf e1 e2 e3 -> EIf (subst s e1) (subst s e2) (subst s e3)
    | EUnit -> EUnit
    | ETrue -> ETrue
    | EFalse -> EFalse
    | EZero -> EZero
    | ESucc e' -> ESucc (subst s e')
    | ENRec e1 e2 e3 -> ENRec (subst s e1) (subst s e2) (subst s e3)
    | EPair e1 e2 -> EPair (subst s e1) (subst s e2)
    | EFst e' -> EFst (subst s e')
    | ESnd e' -> ESnd (subst s e')
    | EInl e' -> EInl (subst s e')
    | EInr e' -> EInr (subst s e')
    | ECase e1 e2 e3 -> ECase (subst s e1) (subst (sub_elam s) e2) (subst (sub_elam s) e3)

and sub_elam (#r:bool) (s:sub r)
  : Tot (sub r)
        (decreases %[1;
                     bool_order r;
                     0;
                     EVar 0])
  = let f : var -> exp =
      fun y ->
        if y=0
        then EVar y
        else subst sub_inc (s (y - 1))
    in
    introduce not r ==> (exists x. ~ (EVar? (f x)))
    with not_r.
      eliminate exists y. ~ (EVar? (s y))
      returns (exists x. ~ (EVar? (f x)))
      with (not_evar_sy:squash (~(EVar? (s y)))).
        introduce exists x. ~(EVar? (f x))
        with (y + 1)
        and ()
    ;
    f

let sub_beta (e:exp)
  : sub (EVar? e)
  = let f =
      fun (y:var) ->
        if y = 0 then e      (* substitute *)
        else (EVar (y-1))    (* shift -1 *)
    in
    if not (EVar? e)
    then introduce exists (x:var). ~(EVar? (f x))
         with 0 and ();
    f

let rec free_vars_indx (e:exp) (n:nat) : list var = // n is the number of binders
  match e with
  | EUnit -> []
  | ETrue -> []
  | EFalse -> []
  | EZero -> []
  | ESucc e' -> free_vars_indx e' n
  | ENRec e1 e2 e3 -> free_vars_indx e1 n @ free_vars_indx e2 n @ free_vars_indx e3 n
  | ELam e' -> free_vars_indx e' (n+1)
  | EApp e1 e2 -> free_vars_indx e1 n @ free_vars_indx e2 n
  | EIf e1 e2 e3 -> free_vars_indx e1 n @ free_vars_indx e2 n @ free_vars_indx e3 n
  | EVar i -> if i < n then [] else [i-n]
  | EPair e1 e2 -> free_vars_indx e1 n @ free_vars_indx e2 n
  | EFst e' -> free_vars_indx e' n
  | ESnd e' -> free_vars_indx e' n
  | EInl e' -> free_vars_indx e' n
  | EInr e' -> free_vars_indx e' n
  | ECase e1 e2 e3 -> free_vars_indx e1 n @ free_vars_indx e2 (n+1) @ free_vars_indx e3 (n+1)

let free_vars e = free_vars_indx e 0

let is_closed (e:exp) : bool =
  free_vars e = []

let rec is_value (e:exp) : Type0 =
  match e with
  | EUnit -> True
  | ETrue -> True
  | EFalse -> True
  | EZero -> True
  | ESucc e' -> is_value e'
  | ELam _ -> is_closed e
  | EPair e1 e2 -> is_value e1 /\ is_value e2
  | EInl e'
  | EInr e' -> is_value e'
  | _ -> False

let rec lem_value_is_closed (e:exp) : Lemma
  (requires is_value e)
  (ensures is_closed e)
  [SMTPat (is_closed e)] =
  match e with
  | EPair e1 e2 -> lem_value_is_closed e1; lem_value_is_closed e2
  | EInl e'
  | EInr e'
  | ESucc e' -> lem_value_is_closed e'
  | _ -> ()

type value = e:exp{is_value e}
type closed_exp = e:exp{is_closed e}

#push-options "--split_queries always"
let rec lem_shifting_preserves_closed (s:sub true) (e:exp) (n:nat) :
  Lemma
    (requires (free_vars_indx e n == [] /\
               (forall (x:var). EVar?.v (s x) <= x+1)))
    (ensures (free_vars_indx (subst s e) (n+1) == []))
    (decreases e) =
  match e with
  | ELam e' -> begin
    assert (free_vars_indx e' (n+1) == []);
    let s' : sub true = sub_elam s in
    assert (forall (x:var). EVar?.v (s' x) <= x+1);
    lem_shifting_preserves_closed s' e' (n+1);
    assert (free_vars_indx (subst s' e') (n+2) == []);
    assert (free_vars_indx (subst s' e') (n+2) ==
            free_vars_indx (subst s (ELam e')) (n+1))
  end
  | EFst e
  | ESnd e
  | EInl e
  | EInr e
  | ESucc e ->
    lem_shifting_preserves_closed s e n
  | EApp e1 e2
  | EPair e1 e2 ->
    lem_shifting_preserves_closed s e1 n;
    lem_shifting_preserves_closed s e2 n
  | EIf e1 e2 e3 ->
    lem_shifting_preserves_closed s e1 n;
    lem_shifting_preserves_closed s e2 n;
    lem_shifting_preserves_closed s e3 n
  | ENRec e1 e2 e3 ->
    lem_shifting_preserves_closed s e1 n;
    lem_shifting_preserves_closed s e2 n;
    lem_shifting_preserves_closed s e3 n
  | ECase e1 e2 e3 ->
    lem_shifting_preserves_closed s e1 n;
    lem_shifting_preserves_closed s e2 (n+1);
    admit ();
    lem_shifting_preserves_closed s e3 (n+1)
  | _ -> ()

let rec lem_subst_freevars_closes_exp
  #b
  (s:sub b)
  (e:exp)
  (n:nat) // number of binders
        // the substitutions for the free variables are in s from pos n to infinity
        // recursively, n increases, and s is shifted
  :
  Lemma
    (requires (
      (forall (x:var). x < n ==> EVar? (s x) /\ EVar?.v (s x) < n) /\
      (forall fv. fv `memP` free_vars_indx e n ==>
        free_vars_indx (s (n+fv)) n == [])))
    (ensures (free_vars_indx (subst s e) n == []))
    (decreases e) =
  match e with
  | ELam e' ->
    let s' = sub_elam s in
    let n' = n+1 in
    assert (free_vars_indx e n == free_vars_indx e' n');
    introduce forall x. free_vars_indx (s x) n == [] ==> free_vars_indx (s' (x+1)) n' == [] with begin
      introduce _ ==> _ with _. begin
        assert (free_vars_indx (s x) n == []);
        lem_shifting_preserves_closed (sub_inc) (s x) n;
        assert (free_vars_indx (subst sub_inc (s x)) n' == [])
      end
    end;
    lem_subst_freevars_closes_exp s' e' n'
  | EApp e1 e2
  | EPair e1 e2 ->
    assume (forall x. x `memP` free_vars_indx e1 n ==> x `memP` free_vars_indx e n);(** should be provable **)
    lem_subst_freevars_closes_exp s e1 n;
    assume (forall x. x `memP` free_vars_indx e2 n ==> x `memP` free_vars_indx e n);(** should be provable **)
    lem_subst_freevars_closes_exp s e2 n
  | EIf e1 e2 e3 ->
    assume (forall x. x `memP` free_vars_indx e1 n ==> x `memP` free_vars_indx e n);(** should be provable **)
    lem_subst_freevars_closes_exp s e1 n;
    assume (forall x. x `memP` free_vars_indx e2 n ==> x `memP` free_vars_indx e n);(** should be provable **)
    lem_subst_freevars_closes_exp s e2 n;
    assume (forall x. x `memP` free_vars_indx e3 n ==> x `memP` free_vars_indx e n);(** should be provable **)
    lem_subst_freevars_closes_exp s e3 n
  | EFst e'
  | ESnd e'
  | EInl e'
  | EInr e'
  | ESucc e' ->
    assume (forall x. x `memP` free_vars_indx e' n ==> x `memP` free_vars_indx e n);(** should be provable **)
    lem_subst_freevars_closes_exp s e' n
  | ENRec e1 e2 e3 ->
    assume (forall x. x `memP` free_vars_indx e1 n ==> x `memP` free_vars_indx e n);(** should be provable **)
    lem_subst_freevars_closes_exp s e1 n;
    assume (forall x. x `memP` free_vars_indx e2 n ==> x `memP` free_vars_indx e n);(** should be provable **)
    lem_subst_freevars_closes_exp s e2 n;
    assume (forall x. x `memP` free_vars_indx e3 n ==> x `memP` free_vars_indx e n);(** should be provable **)
    lem_subst_freevars_closes_exp s e3 n
  | ECase e1 e2 e3 -> admit ()
  | _ -> ()
#pop-options

let subst_beta (v e:exp) :
  Pure closed_exp
    (requires (is_closed (ELam e)) /\ is_closed v)
    (ensures (fun _ -> True)) =
  assume (free_vars_indx e 0 == [0]); (** should be provable **)
  lem_subst_freevars_closes_exp (sub_beta v) e 0;
  subst (sub_beta v) e

let lem_esucc_value_closed (e:value{is_closed e}) :
  Lemma (is_closed (ESucc e))
  [SMTPat (is_closed (ESucc e))] =
  ()

let lem_einr_value_closed (e:value{is_closed e}) :
  Lemma (is_closed (EInr e))
  [SMTPat (is_closed (EInr e))] =
  ()

let lem_einl_value_closed (e:value{is_closed e}) :
  Lemma (is_closed (EInl e))
  [SMTPat (is_closed (EInl e))] =
  ()

let lem_eapp_closed (e1:closed_exp) (e2:closed_exp) :
  Lemma (is_closed (EApp e1 e2))
  [SMTPat (is_closed (EApp e1 e2))] =
  ()

let lem_epair_closed (e1:closed_exp) (e2:closed_exp) :
  Lemma (is_closed (EPair e1 e2))
  [SMTPat (is_closed (EPair e1 e2))] =
  ()

let lem_ecase_closed (e1:closed_exp) (e2:exp{is_closed (ELam e2)}) (e3:exp{is_closed (ELam e3)}) :
  Lemma (is_closed (ECase e1 e2 e3))
  [SMTPat (is_closed (ECase e1 e2 e3))] =
  ()

(* Small-step operational semantics; strong / full-beta reduction is
   right to left  *)

noeq
type step : closed_exp -> closed_exp -> Type =
  | AppRight :
    e1:closed_exp ->
    #e2:closed_exp ->
    #e2':closed_exp ->
    hst:step e2 e2' ->
    step (EApp e1 e2) (EApp e1 e2')
  | AppLeft :
    #e1:closed_exp ->
    e2:closed_exp{is_value e2} -> (** e2 being a value makes the semantics to be call by value. TODO: funny one cannot use [value] directly **)
    #e1':closed_exp ->
    hst:step e1 e1' ->
    step (EApp e1 e2) (EApp e1' e2)
  | Beta :
    e11:exp{is_closed (ELam e11)} ->
    e2:value ->
    step (EApp (ELam e11) e2) (subst_beta e2 e11)
  | SSucc :
    #e:closed_exp ->
    #e':closed_exp ->
    hst:step e e' ->
    step (ESucc e) (ESucc e')
  | SNRecV :
    #e1:closed_exp ->
    #e1':closed_exp ->
    e2:closed_exp ->
    e3:closed_exp ->
    hst:step e1 e1' ->
    step (ENRec e1 e2 e3) (ENRec e1' e2 e3)
  | SNRec0 :
    e2:closed_exp ->
    e3:closed_exp ->
    step (ENRec EZero e2 e3) e2
  | SNRecIter :
    v:closed_exp{is_value v} ->
    e2:closed_exp ->
    e3:closed_exp ->
    step (ENRec (ESucc v) e2 e3) (ENRec v (EApp e3 e2) e3)
  | IfCond :
    #e1:closed_exp ->
    e2:closed_exp ->
    e3:closed_exp ->
    #e1':closed_exp ->
    hst:step e1 e1' ->
    step (EIf e1 e2 e3) (EIf e1' e2 e3)
  | IfTrue :
    e2:closed_exp ->
    e3:closed_exp ->
    step (EIf ETrue e2 e3) e2
  | IfFalse :
    e2:closed_exp ->
    e3:closed_exp ->
    step (EIf EFalse e2 e3) e3
  | SCase :
    #e1:closed_exp ->
    e2:exp{is_closed (ELam e2)} ->
    e3:exp{is_closed (ELam e3)} ->
    #e1':closed_exp ->
    hst:step e1 e1' ->
    step (ECase e1 e2 e3) (ECase e1' e2 e3)
  | SInl :
    e1:value ->
    e2:exp{is_closed (ELam e2)} ->
    e3:exp{is_closed (ELam e3)} ->
    step (ECase (EInl e1) e2 e3) (subst_beta e1 e2)
  | SInr :
    e1:value ->
    e2:exp{is_closed (ELam e2)} ->
    e3:exp{is_closed (ELam e3)} ->
    step (ECase (EInr e1) e2 e3) (subst_beta e1 e3)
  | PairLeft :
    #e1:closed_exp ->
    e2:closed_exp ->
    #e1':closed_exp ->
    hst:step e1 e1' ->
    step (EPair e1 e2) (EPair e1' e2)
  | PairRight :
    e1:closed_exp{is_value e1} ->
    #e2:closed_exp ->
    #e2':closed_exp ->
    hst:step e2 e2' ->
    step (EPair e1 e2) (EPair e1 e2')
  | FstPair :
    #e':closed_exp ->
    #e'':closed_exp ->
    hst:step e' e'' ->
    step (EFst e') (EFst e'')
  | FstPairReturn :
    #e1:closed_exp{is_value e1} ->
    #e2:closed_exp{is_value e2} ->
    step (EFst (EPair e1 e2)) e1
  | SndPair :
    #e':closed_exp ->
    #e'':closed_exp ->
    hst:step e' e'' ->
    step (ESnd e') (ESnd e'')
  | SndPairReturn :
    #e1:closed_exp{is_value e1} ->
    #e2:closed_exp{is_value e2} ->
    step (ESnd (EPair e1 e2)) e2

let can_step (e:closed_exp) : Type0 =
  exists (e':closed_exp). step e e'

let irred (e:closed_exp) : Type0 =
  forall (e':closed_exp). ~(step e e') // optionally \/ is_value e - Amal's definition

let rec lem_value_is_irred (e:closed_exp) : Lemma
  (requires is_value e)
  (ensures irred e)
  [SMTPat (irred e)] =
  match e with
  | EPair e1 e2 ->
    lem_value_is_irred e1;
    lem_value_is_irred e2;
    introduce forall (e':closed_exp). step e e' ==> False with begin
      introduce step e e' ==> False with h. begin
        FStar.Squash.bind_squash #(step e e') h (fun st ->
          match st with
          | PairLeft e2 hst -> ()
          | PairRight e1 hst -> ()
          | _ -> false_elim ())
      end
    end
  | ESucc e' ->
    lem_value_is_irred e';
    introduce forall (e_next:closed_exp). step e e_next ==> False with begin
      introduce step e e_next ==> False with h. begin
        FStar.Squash.bind_squash #(step e e_next) h (fun st ->
          match st with
          | SSucc hst -> ()
          | _ -> false_elim ())
      end
    end
  | _ -> assert (forall e'. ~(step e e')) by (explode ())

(** reflexive transitive closure of step *)
noeq
type steps : closed_exp -> closed_exp -> Type =
| SRefl  : e:closed_exp ->
           steps e e
| STrans : #e1:closed_exp ->
           #e2:closed_exp ->
           #e3:closed_exp ->
           step e1 e2 ->
           steps e2 e3 ->
           steps e1 e3

let rec lem_steps_transitive_constructive
  (#e1 #e2 #e3:closed_exp)
  (st12:steps e1 e2)
  (st23:steps e2 e3)
  : Tot (steps e1 e3) (decreases st12)
  = match st12 with
    | SRefl _ -> st23
    | STrans e1_can_step st12' ->
      STrans e1_can_step (lem_steps_transitive_constructive st12' st23)

open FStar.Squash

let lem_step_implies_steps (e e':closed_exp) :
  Lemma
    (requires step e e')
    (ensures steps e e') =
  introduce forall e e'. step e e' ==> steps e e' with begin
    introduce step e e' ==> steps e e' with h. begin
      FStar.Squash.bind_squash #(step e e') () (fun st ->
        return_squash (STrans st (SRefl e')))
    end
  end

let lem_steps_transitive (e1 e2 e3:closed_exp) :
  Lemma
    (requires (steps e1 e2 /\ steps e2 e3))
    (ensures (steps e1 e3)) =
  bind_squash #(steps e1 e2) () (fun st12 ->
    bind_squash #(steps e2 e3) () (fun st23 ->
      return_squash (
        lem_steps_transitive_constructive st12 st23)))

let lem_steps_irred_e_irred_e'_implies_e_e' (e:closed_exp{irred e}) (e':closed_exp{irred e'}) : Lemma
  (requires steps e e')
  (ensures e == e') = admit ()

let lem_steps_refl (e:closed_exp) : Lemma (steps e e) [SMTPat (steps e e)] =
  FStar.Squash.return_squash (SRefl e)

let safe (e:closed_exp) : Type0 =
  forall e'. steps e e' ==> is_value e' \/ can_step e'

let lem_steps_preserve_safe (e e':closed_exp) :
  Lemma
    (requires (safe e) /\ (steps e e'))
    (ensures (safe e')) =
  introduce forall e_f. steps e' e_f ==> is_value e_f \/ can_step e_f with
    begin
    introduce steps e' e_f ==> is_value e_f \/ can_step e_f with h.
      begin
      bind_squash #(steps e' e_f) () (fun st_f ->
      match st_f with
        | SRefl e' -> ()
        | STrans e'_can_step st_f' -> lem_steps_transitive e e' e_f)
      end
    end

(* We need syntactic types for this, or at least the top-level shape of types *)
let sem_value_shape (t:typ) (e:closed_exp) : Tot Type0 =
  match t with
  | TUnit -> e == EUnit
  | TBool -> e == ETrue \/ e == EFalse
  | TNat -> EZero? e \/ ESucc? e
  | TArr t1 t2 -> ELam? e
  | TPair t1 t2 -> EPair? e
  | TSum t1 t2 -> EInl? e \/ EInr? e

let sem_expr_shape (t:typ) (e:closed_exp) : Tot Type0 =
  forall (e':closed_exp). steps e e' ==> irred e' ==> sem_value_shape t e'

let lem_steps_preserve_sem_expr_shape (e e':closed_exp) (t:typ) :
  Lemma
    (requires (sem_expr_shape t e) /\ (steps e e'))
    (ensures (sem_expr_shape t e')) =
  introduce forall e_f. steps e' e_f /\ irred e_f ==> sem_value_shape t e_f with
    begin
    introduce _  ==> sem_value_shape t e_f with h.
      begin
        bind_squash #(steps e' e_f) () (fun st_f ->
        match st_f with
        | SRefl e' -> ()
        | STrans e'_can_step st_f' -> lem_steps_transitive e e' e_f)
      end
    end

let can_step_eapp_when_safe (e1 e2:closed_exp) (t1 t2:typ) : Lemma
  (requires
    safe e1 /\
    safe e2 /\
    sem_expr_shape (TArr t1 t2) e1)
  (ensures (exists e'. step (EApp e1 e2) e'))
  =
  (**
     We case analyze if e1 can step or if e2 can step,
       and for each case, we build a step accordingly **)
  introduce irred e1 /\ irred e2 ==>  (exists e'. step (EApp e1 e2) e') with _. begin
    let ELam e11 = e1 in (* By sem_expr_shape ELam? e1 **)
    let st : step (EApp (ELam e11) e2) (subst_beta e2 e11) =
      Beta e11 e2 in
    ()
  end;

  introduce ~(irred e1) /\ irred e2 ==>  (exists e'. step (EApp e1 e2) e') with _. begin
    assert (exists e1'. step e1 e1');
    eliminate exists e1'. step e1 e1' returns exists e'. step (EApp e1 e2) e' with st. begin
      bind_squash st (fun st -> return_squash (AppLeft e2 st))
    end
  end;

  introduce ~(irred e2) ==>  (exists e'. step (EApp e1 e2) e') with _. begin
    assert (exists e2'. step e2 e2');
    eliminate exists e2'. step e2 e2' returns exists e'. step (EApp e1 e2) e' with st. begin
      bind_squash st (fun st -> return_squash (AppRight e1 st))
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

let rec destruct_steps_eapp
  (e1:closed_exp)
  (e2:closed_exp)
  (e':closed_exp)
  (st:steps (EApp e1 e2) e')
  (t1:typ)
  (t2:typ) :
  Pure (exp * value)
    (requires irred e' /\ (** CH: needed, otherwise I can take zero steps; could be replaced by value e' *)
      safe e1 /\
      sem_expr_shape (TArr t1 t2) e1 /\
      safe e2)
    (ensures fun (e11, e2') ->
      is_closed (ELam e11) /\
      steps e1 (ELam e11) /\
      steps e2 e2' /\
      steps (EApp e1 e2) (subst_beta e2' e11) /\
      steps (subst_beta e2' e11) e')
    (decreases st)
  = match st with
    | SRefl (EApp e1 e2) -> begin
      (** I am contradicting `irred (EApp e1 e2)` by proving that
       `exists e'. step (EApp e1 e2)` **)
      can_step_eapp_when_safe e1 e2 t1 t2;
      false_elim ()
    end
    | STrans #f1 #f2 #f3 step_eapp step_eapp_steps -> begin
      let (EApp e1 e2) = f1 in
      let e' = f3 in
      match step_eapp with
      | AppLeft #e1 e2 #e1' step_e1 -> begin
        let (EApp e1' e2) = f2 in
        lem_step_implies_steps e1 e1';
        lem_step_implies_steps (EApp e1 e2) (EApp e1' e2);
        lem_steps_preserve_safe e1 e1';
        lem_steps_preserve_sem_expr_shape e1 e1' (TArr t1 t2);
        let s2 : steps (EApp e1' e2) e' = step_eapp_steps in
        let (e11'', e2'') = destruct_steps_eapp e1' e2 e' s2 t1 t2 in
        lem_steps_transitive e1 e1' (ELam e11'');
        lem_steps_transitive (EApp e1 e2) (EApp e1' e2) (subst_beta e2'' e11'');
        (e11'', e2'')
        end
      | AppRight e1 #e2 #e2' step_e2 -> begin
        let (EApp e1 e2') = f2 in
        lem_step_implies_steps e2 e2';
        lem_step_implies_steps (EApp e1 e2) (EApp e1 e2');
        lem_steps_preserve_safe e2 e2';
        let s2 : steps (EApp e1 e2') e' = step_eapp_steps in
        let (e11'', e2'') = destruct_steps_eapp e1 e2' e' s2 t1 t2 in
        lem_steps_transitive e2 e2' e2'';
        lem_steps_transitive (EApp e1 e2) (EApp e1 e2') (subst_beta e2'' e11'');
        (e11'', e2'')
        end
      | Beta e11 e2 -> begin
        lem_step_implies_steps (EApp e1 e2) (subst_beta e2 e11);
        (e11, e2)
        end
      | _ -> false_elim ()
      end

let can_step_eif_when_safe (e1 e2 e3:closed_exp) : Lemma
  (requires
    safe e1 /\
    sem_expr_shape TBool e1)
  (ensures (exists e'. step (EIf e1 e2 e3) e'))
  =
  introduce irred e1 /\ e1 == ETrue ==> (exists e'. step (EIf e1 e2 e3) e') with _.
  begin
    let st : step (EIf ETrue e2 e3) e2 = IfTrue e2 e3 in
    ()
  end;
  introduce irred e1 /\ e1 == EFalse ==> (exists e'. step (EIf e1 e2 e3) e') with _.
  begin
    let st : step (EIf EFalse e2 e3) e3 = IfFalse e2 e3 in
    ()
  end;
  introduce ~(irred e1) ==> (exists e'. step (EIf e1 e2 e3) e') with _.
  begin
    assert (exists e1'. step e1 e1');
    eliminate exists e1'. step e1 e1' returns exists e'. step (EIf e1 e2 e3) e' with st. begin
      bind_squash st (fun st -> return_squash (IfCond e2 e3 st))
    end
  end

let rec destruct_steps_eif
  (e1:closed_exp)
  (e2:closed_exp)
  (e3:closed_exp)
  (e':closed_exp)
  (st:steps (EIf e1 e2 e3) e') :
  Pure closed_exp
    (requires irred e' /\
      safe e1 /\
      sem_expr_shape TBool e1) (** CA: not sure if necessary **)
    (ensures fun e1' ->
      irred e1' /\
      steps e1 e1' /\
      steps (EIf e1 e2 e3) (EIf e1' e2 e3) /\
      (ETrue? e1' ==> steps e2 e') /\
      (EFalse? e1' ==> steps e3 e'))
    (decreases st)
  = match st with
    | SRefl (EIf e1 e2 e3) -> begin
      can_step_eif_when_safe e1 e2 e3;
      false_elim ()
      end
    | STrans #f1 #f2 #f3 step_eif step_eif_steps -> begin
      let (EIf e1 e2 e3) = f1 in
      let e' = f3 in
      match step_eif with
      | IfCond #e1 e2 e3 #e1' step_e1 -> begin
        let (EIf e1' e2 e3) = f2 in
        lem_step_implies_steps e1 e1';
        lem_step_implies_steps (EIf e1 e2 e3) (EIf e1' e2 e3);
        lem_steps_preserve_safe e1 e1';
        lem_steps_preserve_sem_expr_shape e1 e1' TBool;
        let s2 : steps (EIf e1' e2 e3) e' = step_eif_steps in
        let e1'' = destruct_steps_eif e1' e2 e3 e' s2 in
        lem_steps_transitive e1 e1' e1'';
        lem_steps_transitive (EIf e1 e2 e3) (EIf e1' e2 e3) (EIf e1'' e2 e3);
        e1''
        end
      | IfTrue e2 e3 -> begin
        lem_step_implies_steps (EIf e1 e2 e3) e2;
        e1
        end
      | IfFalse e2 e3 -> begin
        lem_step_implies_steps (EIf e1 e2 e3) e3;
        e1
        end
      | _ -> false_elim ()
      end

  (**
    How the steps look like:
      EIf e1 e2 e3 -->* EIf e1' e2 e3 -->* e'
  **)

let srefl_epair_implies_value (e1 e2:closed_exp) : Lemma
  (requires safe e1 /\ safe e2 /\ irred (EPair e1 e2))
  (ensures is_value (EPair e1 e2))
  =
  introduce irred e1 /\ irred e2 ==> is_value (EPair e1 e2) with _.
  begin () end;
  introduce ~(irred e1) ==> is_value (EPair e1 e2) with _.
  begin
    assert (exists e1'. step e1 e1');
    eliminate exists e1'. step e1 e1' returns exists e'. step (EPair e1 e2) e' with st.
    begin
      bind_squash st (fun st -> return_squash (PairLeft e2 st))
    end;
    false_elim ()
  end;
  introduce irred e1 /\ ~(irred e2) ==> is_value (EPair e1 e2) with _.
  begin
    assert (exists e2'. step e2 e2');
    eliminate exists e2'. step e2 e2' returns exists e'. step (EPair e1 e2) e' with st.
    begin
      bind_squash st (fun st -> return_squash (PairRight e1 st))
    end;
    false_elim ()
  end

let rec destruct_steps_epair
  (e1:closed_exp)
  (e2:closed_exp)
  (e':closed_exp)
  (st:steps (EPair e1 e2) e') :
  Pure (value * value)
    (requires
      irred e' /\ ///\
      safe e1 /\
      safe e2) (** CA: not sure if necessary **)
    (ensures fun (e1', e2')->
      steps e1 e1' /\
      steps e2 e2' /\
      steps (EPair e1 e2) (EPair e1' e2') /\
      steps (EPair e1' e2') e')
    (decreases st)
  = match st with
    | SRefl (EPair e1 e2) -> begin
      srefl_epair_implies_value e1 e2;
      (e1, e2)
      end
    | STrans #f1 #f2 #f3 step_epair step_epair_steps -> begin
      let (EPair e1 e2) = f1 in
      let e' = f3 in
      match step_epair with
      | PairLeft #e1 e2 #e1' step_e1 -> begin
        let (EPair e1' e2) = f2 in
        lem_step_implies_steps e1 e1';
        lem_step_implies_steps (EPair e1 e2) (EPair e1' e2);
        lem_steps_preserve_safe e1 e1';
        let s2 : steps (EPair e1' e2) e' = step_epair_steps in
        let (e1'', e2'') = destruct_steps_epair e1' e2 e' s2 in
        lem_steps_transitive e1 e1' e1'';
        lem_steps_transitive (EPair e1 e2) (EPair e1' e2) (EPair e1'' e2'');
        (e1'', e2'')
        end
      | PairRight e1 #e2 #e2' step_e2 -> begin
        let (EPair e1 e2') = f2 in
        lem_step_implies_steps e2 e2';
        lem_step_implies_steps (EPair e1 e2) (EPair e1 e2');
        lem_steps_preserve_safe e2 e2';
        let s2 : steps (EPair e1 e2') e' = step_epair_steps in
        let (e1'', e2'') = destruct_steps_epair e1 e2' e' s2 in
        lem_steps_transitive e2 e2' e2'';
        lem_steps_transitive (EPair e1 e2) (EPair e1 e2') (EPair e1'' e2'');
        (e1'', e2'')
        end
      | _ -> (e1, e2)
      end

  (**
    How the steps look like:
      EPair e1 e2 -->* EPair e1' e2' == e'
  **)


let lem_destruct_steps_epair
  (e1' e2':closed_exp)
  (e':closed_exp) :
  Lemma (requires (steps (EPair e1' e2') e' /\ irred e1' /\ irred e2'))
        (ensures ((EPair e1' e2') == e')) = admit ()

let can_step_efst_when_safe (e12:closed_exp) (t1 t2:typ) : Lemma
  (requires
    safe e12 /\
    sem_expr_shape (TPair t1 t2) e12)
  (ensures (exists e'. step (EFst e12) e'))
  =
  introduce irred e12 ==> (exists e'. step (EFst e12) e') with _.
  begin
    let (EPair e1 e2) = e12 in
    let st : step (EFst (EPair e1 e2)) e1 = FstPairReturn in
    ()
  end;
  introduce ~(irred e12) ==> (exists e'. step (EFst e12) e') with _.
  begin
    assert (exists e12'. step e12 e12');
    eliminate exists e12'. step e12 e12' returns exists e'. step (EFst e12) e' with st.
    begin
      bind_squash st (fun st -> return_squash (FstPair st))
    end
  end

let rec destruct_steps_epair_fst
  (e12:closed_exp)
  (e':closed_exp)
  (st:steps (EFst e12) e')
  (t1:typ)
  (t2:typ) :
  Pure value
    (requires irred e' /\
      safe e12 /\
      sem_expr_shape (TPair t1 t2) e12) (** CA: not sure if necessary **)
    (ensures fun e12' ->
      irred e12' /\
      steps e12 e12' /\
      is_closed (EFst e12') /\
      steps (EFst e12') e')
    (decreases st)
  =
  match st with
  | SRefl (EFst e12) -> begin
    can_step_efst_when_safe e12 t1 t2;
    false_elim ()
    end
  | STrans #f1 #f2 #f3 step_efst step_efst_steps -> begin
    let (EFst e12) = f1 in
    let e' = f3 in
    match step_efst with
    | FstPair #e12 #e12' step_e12 -> begin
      let (EFst e12') = f2 in
      lem_step_implies_steps e12 e12';
      lem_step_implies_steps (EFst e12) (EFst e12');
      lem_steps_preserve_safe e12 e12';
      lem_steps_preserve_sem_expr_shape e12 e12' (TPair t1 t2);
      let s2 : steps (EFst e12') e' = step_efst_steps in
      let e12'' = destruct_steps_epair_fst e12' e' s2 t1 t2 in
      lem_steps_transitive e12 e12' e12'';
      e12''
      end
    | FstPairReturn #e1 #e2 -> begin
      lem_step_implies_steps (EFst (EPair e1 e2)) e1;
      e12
      end
    | _ -> false_elim ()
    end

  (**
    How the steps look like:
      EFst e12 -->* EFst e12' -> e'
  **)

let lem_destruct_steps_epair_fst
  (e1 e2:closed_exp)
  (e':closed_exp) :
  Lemma (requires (steps (EFst (EPair e1 e2)) e' /\ irred e1 /\ irred e2))
        (ensures (e1 == e')) = admit ()

let can_step_esnd_when_safe (e12:closed_exp) (t1 t2:typ) : Lemma
  (requires
    safe e12 /\
    sem_expr_shape (TPair t1 t2) e12)
  (ensures (exists e'. step (ESnd e12) e'))
  =
  introduce irred e12 ==> (exists e'. step (ESnd e12) e') with _.
  begin
    let (EPair e1 e2) = e12 in
    let st : step (ESnd (EPair e1 e2)) e2 = SndPairReturn in
    ()
  end;
  introduce ~(irred e12) ==> (exists e'. step (ESnd e12) e') with _.
  begin
    assert (exists e12'. step e12 e12');
    eliminate exists e12'. step e12 e12' returns exists e'. step (ESnd e12) e' with st.
    begin
      bind_squash st (fun st -> return_squash (SndPair st))
    end
  end

let rec destruct_steps_epair_snd
  (e12:closed_exp)
  (e':closed_exp)
  (st:steps (ESnd e12) e')
  (t1:typ)
  (t2:typ) :
  Pure value
    (requires irred e' /\
      safe e12 /\
      sem_expr_shape (TPair t1 t2) e12) (** CA: not sure if necessary **)
    (ensures fun e12' ->
      irred e12' /\
      steps e12 e12' /\
      is_closed (ESnd e12') /\
      steps (ESnd e12') e')
    (decreases st)
  =
  match st with
  | SRefl (ESnd e12) -> begin
    can_step_esnd_when_safe e12 t1 t2;
    false_elim ()
    end
  | STrans #f1 #f2 #f3 step_esnd step_esnd_steps -> begin
    let (ESnd e12) = f1 in
    let e' = f3 in
    match step_esnd with
    | SndPair #e12 #e12' step_e12 -> begin
      let (ESnd e12') = f2 in
      lem_step_implies_steps e12 e12';
      lem_step_implies_steps (ESnd e12) (ESnd e12');
      lem_steps_preserve_safe e12 e12';
      lem_steps_preserve_sem_expr_shape e12 e12' (TPair t1 t2);
      let s2 : steps (ESnd e12') e' = step_esnd_steps in
      let e12'' = destruct_steps_epair_snd e12' e' s2 t1 t2 in
      lem_steps_transitive e12 e12' e12'';
      e12''
      end
    | SndPairReturn #e1 #e2 -> begin
      lem_step_implies_steps (ESnd (EPair e1 e2)) e2;
      e12
      end
    | _ -> false_elim ()
    end

  (**
    How the steps look like:
      ESnd e12 -->* ESnd e12' -> e'
  **)

let lem_destruct_steps_epair_snd
  (e1 e2:closed_exp)
  (e':closed_exp) :
  Lemma (requires (steps (ESnd (EPair e1 e2)) e' /\ irred e1 /\ irred e2))
        (ensures (e2 == e')) = admit ()
