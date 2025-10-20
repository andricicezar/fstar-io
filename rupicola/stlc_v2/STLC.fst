(* Substitution proof from: https://fstar-lang.org/tutorial/book/part2/part2_stlc.html *)

module STLC

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

type typ =
  | TUnit  : typ 
  | TBool  : typ 
  | TArr   : typ -> typ -> typ
  | TPair  : typ -> typ -> typ

let var = nat
type exp =
  | EUnit  : exp
  | ETrue  : exp
  | EFalse : exp
  | EIf    : exp -> exp -> exp -> exp
  | EVar   : v:var -> exp
  | ELam   : b:exp -> exp
  | EApp   : exp -> exp -> exp
  | EPair  : fst:exp -> snd:exp -> exp
  | EFst   : exp -> exp
  | ESnd   : exp -> exp

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
    | EPair e1 e2 -> EPair (subst s e1) (subst s e2)
    | EFst e' -> EFst (subst s e')
    | ESnd e' -> ESnd (subst s e')

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

let rec free_vars_indx (e:exp) (n:nat) : (list var * nat) = // n is the number of binders
  match e with
  | EUnit -> ([], n)
  | ETrue -> ([], n)
  | EFalse -> ([], n)
  | ELam e' -> free_vars_indx e' (n+1)
  | EApp e1 e2 -> (fst (free_vars_indx e1 n) @ fst (free_vars_indx e2 n), snd (free_vars_indx e1 n) + snd (free_vars_indx e2 n))
  | EIf e1 e2 e3 -> (fst (free_vars_indx e1 n) @ fst (free_vars_indx e2 n) @ fst (free_vars_indx e3 n), snd (free_vars_indx e1 n) + snd (free_vars_indx e2 n) + snd (free_vars_indx e3 n))
  | EVar i -> if i < n then ([], n) else ([i-n], n)
  | EPair e1 e2 -> (fst (free_vars_indx e1 n) @ fst (free_vars_indx e2 n), snd (free_vars_indx e1 n) + snd (free_vars_indx e2 n))
  | EFst e' -> free_vars_indx e' n
  | ESnd e' -> free_vars_indx e' n

let free_vars e = free_vars_indx e 0

let is_closed (e:exp) : bool =
  let (ls, _) = free_vars e in
  ls = []

let _ = assert (free_vars (ELam(ELam(EVar 0))) == ([], 2)) 

let rec is_value (e:exp) : Type0 =
  match e with
  | EUnit -> True
  | ETrue -> True
  | EFalse -> True
  | ELam _ -> is_closed e
  | EPair e1 e2 -> is_value e1 /\ is_value e2
  | _ -> False

let rec lem_value_is_closed (e:exp) : Lemma
  (requires is_value e)
  (ensures is_closed e)
  [SMTPat (is_closed e)] =
  match e with
  | EPair e1 e2 -> lem_value_is_closed e1; lem_value_is_closed e2
  | _ -> ()

type value = e:exp{is_value e}
type closed_exp = e:exp{is_closed e}

(*let rec lem_shifting_preserves_closed (s:sub true) (e:exp) (n:nat) :
  Lemma
    (requires (free_vars_indx e n == [] /\
               (forall (x:var). EVar?.v (s x) <= x+1)))
    (ensures (fst (free_vars_indx (subst s e) (n+1)) == []))
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
  | EApp e1 e2 ->
    lem_shifting_preserves_closed s e1 n;
    lem_shifting_preserves_closed s e2 n
  | EIf e1 e2 e3 ->
    lem_shifting_preserves_closed s e1 n;
    lem_shifting_preserves_closed s e2 n;
    lem_shifting_preserves_closed s e3 n
  | EPair e1 e2 ->
    lem_shifting_preserves_closed s e1 n;
    lem_shifting_preserves_closed s e2 n
  | EFst e ->
    lem_shifting_preserves_closed s e n
  | ESnd e ->
    lem_shifting_preserves_closed s e n
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
  | EApp e1 e2 ->
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
  | EPair e1 e2 ->
    assume (forall x. x `memP` free_vars_indx e1 n ==> x `memP` free_vars_indx e n);(** should be provable **)
    lem_subst_freevars_closes_exp s e1 n;
    assume (forall x. x `memP` free_vars_indx e2 n ==> x `memP` free_vars_indx e n);(** should be provable **)
    lem_subst_freevars_closes_exp s e2 n
  | EFst e' ->
    assume (forall x. x `memP` free_vars_indx e' n ==> x `memP` free_vars_indx e n);(** should be provable **)
    lem_subst_freevars_closes_exp s e' n
  | ESnd e' ->
    assume (forall x. x `memP` free_vars_indx e' n ==> x `memP` free_vars_indx e n);(** should be provable **)
    lem_subst_freevars_closes_exp s e' n
  | _ -> ()

(* Small-step operational semantics; strong / full-beta reduction is
   non-deterministic, so necessarily as inductive relation *)

let subst_beta (v e:exp) :
  Pure closed_exp
    (requires (is_closed (ELam e) /\ is_closed v))
    (ensures (fun _ -> True)) =
  assume (free_vars_indx e 0 == [0]); (** should be provable **)
  lem_subst_freevars_closes_exp (sub_beta v) e 0;
  subst (sub_beta v) e

val step : closed_exp -> option closed_exp
let rec step e =
  match e with
  | EApp e1 e2 -> begin
      match step e1 with (** PO-app1 **)
      | Some e1' -> Some (EApp e1' e2)
      | None     -> begin
          match step e2 with (** PO-app2 **)
          | Some e2' -> Some (EApp e1 e2')
          | None     -> begin
            match e1 with (** PO-app3 **)
            | ELam e' -> begin
              Some (subst_beta e2 e')
            end
            | _ -> None
          end
      end
  end
  | EIf e1 e2 e3 -> begin
    match step e1 with
    | Some e1' -> Some (EIf e1' e2 e3)
    | None -> begin
      match e1 with
      | ETrue -> Some e2
      | EFalse -> Some e3
      | _ -> None
    end
  end
  | EPair e1 e2 -> begin
    match step e1 with
    | Some e1' -> Some (EPair e1' e2)
    | None -> begin
      match step e2 with
      | Some e2' -> Some (EPair e1 e2')
      | None -> None
    end
  end
  | EFst e' -> begin
    match step e' with
    | Some e'' -> Some (EFst e'')
    | None -> begin
      match e' with
      | EPair e1 _ -> Some e1
      | _ -> None
    end
  end
  | ESnd e' -> begin
    match step e' with
    | Some e'' -> Some (ESnd e'')
    | None -> begin
      match e' with
      | EPair _ e2 -> Some e2
      | _ -> None
    end
  end
  | _ -> None

let can_step (e:closed_exp) : Type0 =
  Some? (step e)

let irred (e:closed_exp) : Type0 =
  None? (step e)

let rec lem_value_is_irred (e:closed_exp) : Lemma
  (requires is_value e)
  (ensures irred e)
  [SMTPat (irred e)] =
  match e with
  | EPair e1 e2 -> lem_value_is_irred e1; lem_value_is_irred e2
  | _ -> ()

(** reflexive transitive closure of step *)
type steps : closed_exp -> closed_exp -> Type =
| SRefl  : e:closed_exp ->
           steps e e
| STrans : #e0:closed_exp ->
           #e2:closed_exp ->
           squash (Some? (step e0)) ->
           steps (Some?.v (step e0)) e2 ->
           steps e0 e2

let lem_steps_refl (e:closed_exp) : Lemma (steps e e) [SMTPat (steps e e)] =
  FStar.Squash.return_squash (SRefl e)

let safe (e:closed_exp) : Type0 =
  forall e'. steps e e' ==> is_value e' \/ can_step e'

(** Such a lemma is mentioned by Amal Ahmed in her PhD thesis, section 2 **)
let rec destruct_steps_eapp
  (e1:closed_exp)
  (e2:closed_exp)
  (e':closed_exp)
  (st:steps (EApp e1 e2) e') :
  Pure (exp * value)
    (requires irred e') (** CA: not sure if necessary **)
    (ensures fun (e11, e2') ->
      is_closed (ELam e11) /\
      steps e1 (ELam e11) /\
      steps e2 e2' /\
      steps (EApp e1 e2) (subst_beta e2' e11) /\
      steps (subst_beta e2' e11) e')
    (decreases st)
  =
  (**
    How the steps look like:
      EApp e1 e2 -->* EApp (ELam t1 e11) e2' --> subst_beta t1 e2' e11 -->* e'

    The function should destruct steps until it is again in EApp.
    Based on the definition of step function, it should imply that (ELam t1 e11) and e2'
    are irreducible.
  **)
  admit ()

let rec destruct_steps_eif
  (e1:closed_exp)
  (e2:closed_exp)
  (e3:closed_exp)
  (e':closed_exp)
  (st:steps (EIf e1 e2 e3) e') :
  Pure closed_exp
    (requires irred e') (** CA: not sure if necessary **)
    (ensures fun e1' ->
      irred e1' /\
      steps e1 e1' /\
      steps (EIf e1 e2 e3) (EIf e1' e2 e3) /\
      (ETrue? e1' ==> steps e2 e') /\
      (EFalse? e1' ==> steps e3 e'))
    (decreases st)
  =
  (**
    How the steps look like:
      EIf e1 e2 e3 -->* EIf e1' e2 e3 -->* e'
  **)
  admit ()


let rec destruct_steps_epair
  (e1:closed_exp)
  (e2:closed_exp)
  (e':closed_exp)
  (st:steps (EPair e1 e2) e') :
  Pure (value * value)
    (requires irred e') (** CA: not sure if necessary **)
    (ensures fun (e1', e2')->
      steps e1 e1' /\
      steps e2 e2' /\
      steps (EPair e1 e2) (EPair e1' e2') /\
      steps (EPair e1' e2') e')
    (decreases st)
  =
  (**
    How the steps look like:
      EPair e1 e2 -->* EPair e1' e2' == e'
  **)
  admit ()

let rec destruct_steps_epair_fst
  (e12:closed_exp)
  (e':closed_exp)
  (st:steps (EFst e12) e') :
  Pure value
    (requires irred e') (** CA: not sure if necessary **)
    (ensures fun e12' ->
      steps e12 e12' /\
      steps (EFst e12') e')
    (decreases st)
  =
  (**
    How the steps look like:
      EFst e12 -->* EFst e12' -> e'
  **)
  admit ()

let lem_destruct_steps_epair_fst
  (e1 e2:closed_exp)
  (e':closed_exp) :
  Lemma (requires (steps (EFst (EPair e1 e2)) e' /\ irred e1 /\ irred e2))
        (ensures (e1 == e')) = admit ()

let rec destruct_steps_epair_snd
  (e12:closed_exp)
  (e':closed_exp)
  (st:steps (ESnd e12) e') :
  Pure value
    (requires irred e') (** CA: not sure if necessary **)
    (ensures fun e12' ->
      steps e12 e12' /\
      steps (ESnd e12') e')
    (decreases st)
  =
  (**
    How the steps look like:
      ESnd e12 -->* ESnd e12' -> e'
  **)
  admit ()

let lem_destruct_steps_epair_snd
  (e1 e2:closed_exp)
  (e':closed_exp) :
  Lemma (requires (steps (ESnd (EPair e1 e2)) e' /\ irred e1 /\ irred e2))
        (ensures (e2 == e')) = admit ()
        *)
