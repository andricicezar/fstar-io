(* Substitution proof from: https://fstar-lang.org/tutorial/book/part2/part2_stlc.html *)

module STLC

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot
open Trace

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
  | ERead  : exp
  | EWrite : exp -> exp

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
    | ERead -> ERead
    | EWrite e' -> EWrite (subst s e')

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
  | ELam e' -> free_vars_indx e' (n+1)
  | EApp e1 e2 -> free_vars_indx e1 n @ free_vars_indx e2 n
  | EIf e1 e2 e3 -> free_vars_indx e1 n @ free_vars_indx e2 n @ free_vars_indx e3 n
  | EVar i -> if i < n then [] else [i-n]
  | EPair e1 e2 -> free_vars_indx e1 n @ free_vars_indx e2 n
  | EFst e' -> free_vars_indx e' n
  | ESnd e' -> free_vars_indx e' n
  | ERead -> []
  | EWrite e' -> free_vars_indx e' n

let free_vars e = free_vars_indx e 0

let is_closed (e:exp) : bool =
  free_vars e = []

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
  | EWrite e ->
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
  | EWrite e' ->
    assume (forall x. x `memP` free_vars_indx e' n ==> x `memP` free_vars_indx e n);
    lem_subst_freevars_closes_exp s e' n
  | _ -> ()

let subst_beta (v e:exp) :
  Pure closed_exp
    (requires (is_closed (ELam e)) /\ is_closed v)
    (ensures (fun _ -> True)) =
  assume (free_vars_indx e 0 == [0]); (** should be provable **)
  lem_subst_freevars_closes_exp (sub_beta v) e 0;
  subst (sub_beta v) e

let get_ebool (b:bool) : closed_exp =
  match b with
  | true -> ETrue
  | false -> EFalse

(* Small-step operational semantics; strong / full-beta reduction is
   right to left  *)

noeq
type step : closed_exp -> closed_exp -> (h:history) -> option (event_h h) -> Type =
  | AppRight :
    e1:closed_exp ->
    #e2:closed_exp ->
    #e2':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step e2 e2' h oev ->
    step (EApp e1 e2) (EApp e1 e2') h oev
  | AppLeft :
    #e1:closed_exp ->
    e2:closed_exp{is_value e2} -> (** e2 being a value makes the semantics to be call by value. TODO: funny one cannot use [value] directly **)
    #e1':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step e1 e1' h oev ->
    step (EApp e1 e2) (EApp e1' e2) h oev
  | Beta :
    e11:exp{is_closed (ELam e11)} ->
    e2:value ->
    h:history ->
    step (EApp (ELam e11) e2) (subst_beta e2 e11) h None
  | IfCond :
    #e1:closed_exp ->
    e2:closed_exp ->
    e3:closed_exp ->
    #e1':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step e1 e1' h oev ->
    step (EIf e1 e2 e3) (EIf e1' e2 e3) h oev
  | IfTrue :
    e2:closed_exp ->
    e3:closed_exp ->
    h:history ->
    step (EIf ETrue e2 e3) e2 h None
  | IfFalse :
    e2:closed_exp ->
    e3:closed_exp ->
    h:history ->
    step (EIf EFalse e2 e3) e3 h None
  | PairLeft :
    #e1:closed_exp ->
    e2:closed_exp ->
    #e1':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step e1 e1' h oev ->
    step (EPair e1 e2) (EPair e1' e2) h oev
  | PairRight :
    e1:closed_exp{is_value e1} ->
    #e2:closed_exp ->
    #e2':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step e2 e2' h oev ->
    step (EPair e1 e2) (EPair e1 e2') h oev
  | FstPair :
    #e':closed_exp ->
    #e'':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step e' e'' h oev ->
    step (EFst e') (EFst e'') h oev
  | FstPairReturn :
    #e1:closed_exp{is_value e1} ->
    #e2:closed_exp{is_value e2} ->
    h:history ->
    step (EFst (EPair e1 e2)) e1 h None
  | SndPair :
    #e':closed_exp ->
    #e'':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step e' e'' h oev ->
    step (ESnd e') (ESnd e'') h oev
  | SndPairReturn :
    #e1:closed_exp{is_value e1} ->
    #e2:closed_exp{is_value e2} ->
    h:history ->
    step (ESnd (EPair e1 e2)) e2 h None
  | SRead :
    b:bool ->
    h:history ->
    step ERead (get_ebool b) h (Some (EvRead () (Some b)))
  | SWrite :
    b:bool ->
    h:history ->
    step (EWrite (get_ebool b)) EUnit h (Some (EvWrite b (Some ())))

let can_step (e:closed_exp) : Type0 =
  exists (e':closed_exp) (h:history) (oev:option (event_h h)). step e e' h oev

let irred (e:closed_exp) (h:history) : Type0 =
  forall (e':closed_exp) (oev:option (event_h h)). ~(step e e' h oev) 
  // optionally \/ is_value e - Amal's definition

let rec lem_value_is_irred (e:closed_exp) : Lemma
  (requires is_value e)
  (ensures (forall h. irred e h)) =
  match e with
  | EUnit ->
    assert (forall h e' oev. ~(step EUnit e' h oev)) by explode ()
  | ETrue ->
    assert (forall h e' oev. ~(step ETrue e' h oev)) by explode ()
  | EFalse ->
    assert (forall h e' oev. ~(step EFalse e' h oev)) by explode ()
  | ELam e11 ->
    assert (forall h e' oev. ~(step (ELam e11) e' h  oev)) by explode ()
  | EPair e1 e2 ->
    lem_value_is_irred e1;
    lem_value_is_irred e2;
    introduce forall (h:history) (e':closed_exp) (oev:option (event_h h)). step e e' h oev ==> False with begin
      introduce step e e' h oev ==> False with _. begin
        FStar.Squash.bind_squash #(step e e' h oev) () (fun st ->
        match st with
        | PairLeft e2 hst -> ()
        | PairRight e1 hst -> ()
        | _ -> ())
      end
    end
  | _ -> ()

(** reflexive transitive closure of step *)
noeq
type steps : closed_exp -> closed_exp -> (h:history) -> local_trace h -> Type =
| SRefl  : e:closed_exp ->
           h:history ->
           steps e e h []
| STrans : #e1:closed_exp ->
           #e2:closed_exp ->
           #e3:closed_exp ->
           #h:history ->
           #oev:option (event_h h) -> 
           #lt:local_trace (if Some? oev then (Some?.v oev)::h else h) ->
           step e1 e2 h oev ->
           steps e2 e3 (if Some? oev then (Some?.v oev)::h else h) lt ->
           steps e1 e3 h (if Some? oev then [Some?.v oev] @ lt else lt)

let rec lem_steps_transitive_constructive
  (#e1 #e2 #e3:closed_exp) 
  (#h:history)
  (#lt1:local_trace h) (#lt2:local_trace (h++lt1))
  (st12:steps e1 e2 h lt1)
  (st23:steps e2 e3 (h++lt1) lt2)
  : Tot (steps e1 e3 h (lt1 @ lt2)) (decreases st12)
  = match st12 with
    | SRefl _ _ -> st23
    | STrans e1_can_step st12' ->
      STrans e1_can_step (lem_steps_transitive_constructive st12' st23)

open FStar.Squash

let get_event_trace (#h:history) (oev:option (event_h h)) : local_trace h = 
  if Some? oev then [Some?.v oev] else []

let lem_step_implies_steps (e e':closed_exp) (h:history) (oev:option (event_h h)) :
  Lemma
    (requires step e e' h oev)
    (ensures steps e e' h (get_event_trace oev)) =
  introduce forall e e'. step e e' h oev ==> steps e e' h (get_event_trace oev) with begin
    introduce step e e' h oev ==> steps e e' h (get_event_trace oev) with _. begin
      bind_squash #(step e e' h oev) () (fun st -> return_squash (STrans st (SRefl e' (h++(get_event_trace oev)))))
    end
  end

let lem_steps_transitive 
  (e1 e2 e3:closed_exp)
  (h:history)
  (lt12:local_trace h) 
  (lt23:local_trace (h++lt12)) :
  Lemma
    (requires (steps e1 e2 h lt12 /\ steps e2 e3 (h++lt12) lt23))
    (ensures (steps e1 e3 h (lt12 @ lt23))) =
  bind_squash #(steps e1 e2 h lt12) () (fun st12 ->
    bind_squash #(steps e2 e3 (h++lt12) lt23) () (fun st23 ->
      return_squash (
        lem_steps_transitive_constructive st12 st23)))

(*let lem_steps_irred_e_irred_e'_implies_e_e' (#h:history) (e:closed_exp{irred e h}) (e':closed_exp{irred e' h}) (lt:local_trace h) : Lemma
  (requires steps e e' h lt)
  (ensures e == e') = admit ()*)

let lem_steps_refl (e:closed_exp) (h:history) : Lemma (steps e e h []) [SMTPat (steps e e h [])] =
  FStar.Squash.return_squash (SRefl e h)

let safe (e:closed_exp) (h:history) : Type0 =
  forall (e':closed_exp) (lt:local_trace h). steps e e' h lt ==> is_value e' \/ can_step e' 

let lem_steps_preserve_safe (e e':closed_exp) (h:history) (lt:local_trace h) :
  Lemma
    (requires (forall h'. (safe e h /\ exists (lt:local_trace h'). steps e e' h' lt)))
    (ensures (forall h'. safe e' h')) =
  eliminate forall h'. (safe e h' /\ exists lt. steps e e' h' lt) with h;
  
  introduce is_value e' ==> (forall h'. safe e' h') with _. begin
    introduce forall h_ e_ lt_. steps e' e_ h_ lt_ ==> is_value e_ \/ can_step e_ with begin
      introduce steps e' e_ h_ lt_ ==> is_value e_ \/ can_step e_  with _. begin
        bind_squash #(steps e' e_ h_ lt_) () (fun st ->
        match st with
        | SRefl e' h_ -> begin
          lem_value_is_irred e'
          end
        | STrans can_step st' -> 
          lem_value_is_irred e';
          false_elim ())
      end
    end
  end;

  introduce can_step e' ==> (forall h'. safe e' h') with _. begin
    introduce forall h_ e_ lt_. steps e' e_ h_ lt_ ==> is_value e_ \/ can_step e_ with begin
      introduce steps e' e_ h_ lt_ ==> is_value e_ \/ can_step e_ with _. begin
        bind_squash #(steps e' e_ h_ lt_) () (fun st ->
        match st with
        | SRefl e' h_ -> begin
          assert (can_step e')
          end
        | STrans step st' -> begin
          //assert (safe e' (h++lt));
          admit ()
          end)
      end
    end
  end
  
(* We need syntactic types for this, or at least the top-level shape of types *)
let sem_value_shape (t:typ) (e:closed_exp) : Tot Type0 =
  match t with
  | TUnit -> e == EUnit
  | TBool -> e == ETrue \/ e == EFalse
  | TArr t1 t2 -> ELam? e
  | TPair t1 t2 -> EPair? e

let sem_expr_shape (t:typ) (e:closed_exp) (h:history) : Tot Type0 =
  forall (e':closed_exp) (lt:local_trace h). steps e e' h lt ==> irred e' (h++lt) ==> sem_value_shape t e'

let lem_steps_preserve_sem_expr_shape (e e':closed_exp) (h:history) (lt:local_trace h) (t:typ) :
  Lemma
    (requires (sem_expr_shape t e h) /\ (steps e e' h lt))
    (ensures (sem_expr_shape t e' (h++lt))) =
  introduce forall e'' lt'. steps e' e'' (h++lt) lt' /\ irred e'' ((h++lt)++lt') ==> sem_value_shape t e'' with begin
    introduce _  ==> sem_value_shape t e'' with _. begin
      bind_squash #(steps e' e'' (h++lt) lt') () (fun st ->
      match st with
      | SRefl _ _ -> ()
      | STrans _ _ -> lem_steps_transitive e e' e'' h lt lt')
    end
  end

let can_step_eapp_when_safe (e1 e2:closed_exp) (t1 t2:typ) (h:history) : Lemma
  (requires
    safe e1 h /\
    safe e2 h /\
    sem_expr_shape (TArr t1 t2) e1  h)
  (ensures (exists e' oev. step (EApp e1 e2) e' h oev))
  =
  (**
     We case analyze if e1 can step or if e2 can step,
       and for each case, we build a step accordingly **)

  introduce irred e1 h /\ irred e2 h ==> (exists e' oev. step (EApp e1 e2) e' h oev) with _. begin
    assert (steps e1 e1 h []);
    assert (steps e2 e2 h []);
    let ELam e11 = e1 in
    let st : step (EApp (ELam e11) e2) (subst_beta e2 e11) h None = Beta e11 e2 h in
    ()
  end;

  introduce ~(irred e1 h) /\ irred e2 h ==> (exists e' oev. step (EApp e1 e2) e' h oev) with _. begin
    assert (steps e2 e2 h []);
    assert (exists e1' oev1. step e1 e1' h oev1);
    eliminate exists e1' oev1. step e1 e1' h oev1 returns exists e' oev. step (EApp e1 e2) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (AppLeft e2 st))
    end
  end;

  introduce ~(irred e2 h) ==>  (exists e' oev. step (EApp e1 e2) e' h oev) with _. begin
    assert (exists e2' oev2. step e2 e2' h oev2);
    eliminate exists e2' oev2. step e2 e2' h oev2 returns exists e' oev. step (EApp e1 e2) e' h oev with st. begin
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
  (h:history)
  (lt:local_trace h)
  (st:steps (EApp e1 e2) e' h lt)
  (t1:typ)
  (t2:typ) :
  Pure (exp * value * (lt2:local_trace h & (lt1:local_trace (h++lt2) & local_trace (((h++lt2)++lt1)))))
    (requires irred e' (h++lt) /\ (** CH: needed, otherwise I can take zero steps; could be replaced by value e' *)
      (forall h'. safe e1 h') /\
      sem_expr_shape (TArr t1 t2) e1 h /\
      (forall h'. safe e2 h')) // this is weird
    (ensures fun (e11, e2', (| lt2, (| lt1, lt3 |) |)) ->
      steps e2 e2' h lt2 /\
      is_closed (ELam e11) /\
      steps e1 (ELam e11) (h++lt2) lt1 /\
      steps (EApp e1 e2) (subst_beta e2' e11) h (lt2 @ lt1) /\
      steps (subst_beta e2' e11) e' ((h++lt2)++lt1) lt3 /\
      lt == ((lt2 @ lt1) @ lt3) /\
      (irred e2 h ==> (lt2 == [] /\ e2 == e2')) /\
      (irred e1 (h++lt2) ==> (lt1 == [] /\ e1 == ELam e11)))
    (decreases st)
  = match st with
    | SRefl (EApp e1 e2) h -> begin
      can_step_eapp_when_safe e1 e2 t1 t2 h;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_eapp step_eapp_steps -> begin
      let (EApp e1 e2) = e in
      match step_eapp with
      | AppLeft #e1 e2 #e1' #h #oev1 step_e1 -> begin
        let (EApp e1' e2) = f2 in
        lem_step_implies_steps e1 e1' h oev1;
        lem_step_implies_steps (EApp e1 e2) (EApp e1' e2) h oev1;
        let lt1 : local_trace h = get_event_trace oev1 in
        lem_steps_preserve_safe e1 e1' h lt1;
        lem_steps_preserve_sem_expr_shape e1 e1' h lt1 (TArr t1 t2);
        let s2 : steps (EApp e1' e2) e' (h++lt1) lt23 = step_eapp_steps in
        eliminate forall h'. safe e2 h' with (h++lt1);
        eliminate forall h'. safe e1' h' with (h++lt1);
        let (e11, e2', (| _, (| lt1', lt3 |) |)) = destruct_steps_eapp e1' e2 e' (h++lt1) lt23 s2 t1 t2 in
        lem_value_is_irred e2;
        lem_steps_transitive e1 e1' (ELam e11) h lt1 lt1';
        lem_steps_transitive (EApp e1 e2) (EApp e1' e2) (subst_beta e2' e11) h lt1 lt1';
        (e11, e2', (| [] , (| (lt1 @ lt1'), lt3 |) |))
        end
      | AppRight e1 #e2 #e2' #h #oev2 step_e2 -> begin
        let (EApp e1 e2') = f2 in
        lem_step_implies_steps e2 e2' h oev2;
        lem_step_implies_steps (EApp e1 e2) (EApp e1 e2') h oev2;
        let lt2 : local_trace h = get_event_trace oev2 in
        lem_steps_preserve_safe e2 e2' h lt2;
        let s2 : steps (EApp e1 e2') e' (h++lt2) lt23 = step_eapp_steps in
        assume (sem_expr_shape (TArr t1 t2) e1 (h++lt2));
        let (e11, e2'', (| lt2', (| lt1, lt3 |) |)) = destruct_steps_eapp e1 e2' e' (h++lt2) lt23 s2 t1 t2 in
        lem_steps_transitive e2 e2' e2'' h lt2 lt2';
        lem_steps_transitive (EApp e1 e2) (EApp e1 e2') (subst_beta e2'' e11) h lt2 (lt2' @ lt1);
        (e11, e2'', (| (lt2 @ lt2'), (| lt1, lt3 |) |))
        end
      | Beta e11 e2 h -> begin
        lem_step_implies_steps (EApp e1 e2) (subst_beta e2 e11) h None;
        (e11, e2, (| [], (| [], lt |) |))
        end
      end

let can_step_eif_when_safe (e1 e2 e3:closed_exp) (h:history) : Lemma
  (requires
    safe e1 h /\
    sem_expr_shape TBool e1 h)
  (ensures (exists e' oev. step (EIf e1 e2 e3) e' h oev))
  = 
  introduce irred e1 h /\ e1 == ETrue ==> (exists e' oev. step (EIf e1 e2 e3) e' h oev) with _. begin
    assert (steps e1 e1 h []);
    let st : step (EIf ETrue e2 e3) e2 h None = IfTrue e2 e3 h in
    ()
  end;
  
  introduce irred e1 h /\ e1 == EFalse ==> (exists e' oev. step (EIf e1 e2 e3) e' h oev) with _. begin
    assert (steps e1 e1 h []);
    let st : step (EIf EFalse e2 e3) e3 h None = IfFalse e2 e3 h in
    ()
  end;
  
  introduce irred e1 h /\ ~(e1 == EFalse \/ e1 == ETrue) ==> (exists e' oev. step (EIf e1 e2 e3) e' h oev) with _. begin
    assert (steps e1 e1 h []);
    false_elim ()
  end;
  
  introduce ~(irred e1 h) ==> (exists e' oev. step (EIf e1 e2 e3) e' h oev) with _. begin
    assert (exists e1' oev1. step e1 e1' h oev1);
    eliminate exists e1' oev1. step e1 e1' h oev1 returns exists e' oev. step (EIf e1 e2 e3) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (IfCond e2 e3 st))
    end
  end

let rec destruct_steps_eif
  (e1:closed_exp)
  (e2:closed_exp)
  (e3:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EIf e1 e2 e3) e' h lt) :
  Pure (closed_exp * (lt1:local_trace h & (local_trace (h++lt1) * local_trace (h++lt1))))
    (requires irred e' (h++lt) /\
      (forall h'. safe e1 h') /\
      sem_expr_shape TBool e1 h)
    (ensures fun (e1', (| lt1, (lt2, lt3) |)) ->
      irred e1' (h++lt1) /\
      steps e1 e1' h lt1 /\
      steps (EIf e1 e2 e3) (EIf e1' e2 e3) h lt1 /\
      (ETrue? e1' ==> steps e2 e' (h++lt1) lt2) /\
      (EFalse? e1' ==> steps e3 e' (h++lt1) lt3) /\
      ((lt == lt1 @ lt2) \/ (lt == lt1 @ lt3)) /\
      (irred e1 h ==> (lt1 == [] /\ e1 == e1')))
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
        let lt1 : local_trace h = get_event_trace oev1 in
        lem_steps_preserve_safe e1 e1' h lt1;
        lem_steps_preserve_sem_expr_shape e1 e1' h lt1 TBool;
        eliminate forall h'. safe e1' h' with (h++lt1);
        let s2 : steps (EIf e1' e2 e3) e' (h++lt1) lt23 = step_eif_steps in
        let (e1'', (| lt1', (lt2, lt3) |)) = destruct_steps_eif e1' e2 e3 e' (h++lt1) lt23 s2 in
        lem_steps_transitive e1 e1' e1'' h lt1 lt1';
        lem_steps_transitive (EIf e1 e2 e3) (EIf e1' e2 e3) (EIf e1'' e2 e3) h lt1 lt1';
        (e1'', (| (lt1 @ lt1'), (lt2, lt3) |))
        end
      | IfTrue e2 e3 h -> begin
        lem_step_implies_steps (EIf e1 e2 e3) e2 h None;
        lem_value_is_irred e1;
        (e1, (| [], (lt, []) |))
        end
      | IfFalse e2 e3 h -> begin
        lem_step_implies_steps (EIf e1 e2 e3) e3 h None;
        lem_value_is_irred e1;
        (e1, (| [], ([], lt) |))
        end
      end

  (**
    How the steps look like:
      EIf e1 e2 e3 -->* EIf e1' e2 e3 -->* e'
  **)

let srefl_epair_implies_value (e1 e2:closed_exp) (h:history) : Lemma
  (requires safe e1 h /\ safe e2 h /\ irred (EPair e1 e2) h)
  (ensures is_value (EPair e1 e2))
  =
  introduce irred e1 h /\ irred e2 h ==> is_value (EPair e1 e2) with _.
  begin 
    assert (steps e1 e1 h []);
    assert (steps e2 e2 h []);
    ()
  end;

  introduce ~(irred e1 h) ==> is_value (EPair e1 e2) with _.
  begin
    assert (exists e1' oev1. step e1 e1' h oev1);
    eliminate exists e1' oev1. step e1 e1' h oev1 returns exists e' oev. step (EPair e1 e2) e' h oev with st.
    begin
      bind_squash st (fun st -> return_squash (PairLeft e2 st))
    end;
    false_elim ()
  end;
  
  introduce irred e1 h /\ ~(irred e2 h) ==> is_value (EPair e1 e2) with _.
  begin
    assert (steps e1 e1 h []);
    assert (exists e2' oev2. step e2 e2' h oev2);
    eliminate exists e2' oev2. step e2 e2' h oev2 returns exists e' oev. step (EPair e1 e2) e' h oev with st.
    begin
      bind_squash st (fun st -> return_squash (PairRight e1 st))
    end;
    false_elim ()
  end

let rec destruct_steps_epair
  (e1:closed_exp)
  (e2:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EPair e1 e2) e' h lt) :
  Pure (value * value * (lt1:local_trace h & (lt2:local_trace (h++lt1) & local_trace (((h++lt1)++lt2)))))
    (requires irred e' (h++lt) /\ ///\
      (forall h'. safe e1 h') /\
      (forall h'. safe e2 h'))
    (ensures fun (e1', e2', (| lt1, (| lt2, lt3 |) |)) ->
      steps e1 e1' h lt1 /\
      steps e2 e2' (h++lt1) lt2 /\
      steps (EPair e1 e2) (EPair e1' e2') h (lt1 @ lt2) /\
      steps (EPair e1' e2') e' ((h++lt1)++lt2) lt3  /\
      lt == ((lt1 @ lt2) @ lt3) /\
      (irred e1 h ==> (lt1 == [] /\ e1 == e1')) /\
      (irred e2 (h++lt1) ==> (lt2 == [] /\ e2 == e2')))
    (decreases st)
  = match st with
    | SRefl (EPair e1 e2) h -> begin
      srefl_epair_implies_value e1 e2 h;
      (e1, e2, (| [], (| [], [] |) |))
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_epair step_epair_steps -> begin
      let (EPair e1 e2) = e in
      match step_epair with
      | PairLeft #e1 e2 #e1' #h #oev1 step_e1 -> begin
        let (EPair e1' e2) = f2 in
        lem_step_implies_steps e1 e1' h oev1;
        lem_step_implies_steps (EPair e1 e2) (EPair e1' e2) h oev1;
        let lt1 : local_trace h = get_event_trace oev1 in
        lem_steps_preserve_safe e1 e1' h lt1;
        let s2 : steps (EPair e1' e2) e' (h++lt1) lt23 = step_epair_steps in
        eliminate forall h'. safe e1' h' with (h++lt1);
        eliminate forall h'. safe e2 h' with (h++lt1);
        let (e1'', e2', (| lt1', (| lt2, lt3 |) |)) = destruct_steps_epair e1' e2 e' (h++lt1) lt23 s2 in
        lem_steps_transitive e1 e1' e1'' h lt1 lt1';
        lem_steps_transitive (EPair e1 e2) (EPair e1' e2) (EPair e1'' e2') h lt1 (lt1' @ lt2);
        (e1'', e2', (| (lt1 @ lt1'), (| lt2, lt3 |) |))
        end
      | PairRight e1 #e2 #e2' #h #oev2 step_e2 -> begin
        let (EPair e1 e2') = f2 in
        lem_step_implies_steps e2 e2' h oev2;
        lem_step_implies_steps (EPair e1 e2) (EPair e1 e2') h oev2;
        let lt2 : local_trace h = get_event_trace oev2 in
        lem_steps_preserve_safe e2 e2' h lt2;
        let s2 : steps (EPair e1 e2') e' (h++lt2) lt23 = step_epair_steps in
        eliminate forall h'. safe e2' h' with (h++lt2);
        eliminate forall h'. safe e1 h' with (h++lt2);
        let (e1', e2'', (| lt1, (| lt2', lt3 |) |)) = destruct_steps_epair e1 e2' e' (h++lt2) lt23 s2 in
        lem_value_is_irred e1;
        lem_steps_transitive e2 e2' e2'' h lt2 lt2';
        lem_steps_transitive (EPair e1 e2) (EPair e1 e2') (EPair e1' e2'') h lt2 lt2';
        (e1', e2'', (| lt1, (| (lt2 @ lt2'), lt3 |) |)) 
        end
      | _ -> 
        (e1, e2, (| [], (| [], [] |) |))
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
  Lemma (requires (steps (EPair e1' e2') e' h lt /\ irred e1' h /\ irred e2' h))
        (ensures ((EPair e1' e2') == e')) = admit ()

let can_step_efst_when_safe (e12:closed_exp) (t1 t2:typ) (h:history) : Lemma
  (requires
    safe e12 h /\
    sem_expr_shape (TPair t1 t2) e12 h)
  (ensures (exists e' oev. step (EFst e12) e' h oev))
  =
  introduce irred e12 h ==> (exists e' oev. step (EFst e12) e' h oev) with _. begin
    assert (steps e12 e12 h []);
    let (EPair e1 e2) = e12 in
    let st : step (EFst (EPair e1 e2)) e1 h None = FstPairReturn h in
    ()
  end;
  
  introduce ~(irred e12 h) ==> (exists e' oev. step (EFst e12) e' h oev) with _. begin
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
  (t1:typ)
  (t2:typ) :
  Pure (value * (lt12:local_trace h & local_trace (h++lt12)))
    (requires irred e' (h++lt) /\
      (forall h'. safe e12 h') /\
      sem_expr_shape (TPair t1 t2) e12 h) (** CA: not sure if necessary **)
    (ensures fun (e12', (| lt12, lt_f |)) ->
      irred e12' (h++lt12) /\
      steps e12 e12' h lt12 /\
      is_closed (EFst e12') /\
      steps (EFst e12') e' (h++lt12) lt_f /\
      lt == (lt12 @ lt_f) /\
      (irred e12 h ==> (lt12 == [] /\ e12 == e12')))
    (decreases st)
  = match st with
    | SRefl (EFst e12) h -> begin
      can_step_efst_when_safe e12 t1 t2 h;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_efst step_efst_steps -> begin
      let (EFst e12) = e in
      match step_efst with
      | FstPair #e12 #e12' #h #oev12 step_e12 -> begin
        let (EFst e12') = f2 in
        lem_step_implies_steps e12 e12' h oev12;
        lem_step_implies_steps (EFst e12) (EFst e12') h oev12;
        let lt12 : local_trace h = get_event_trace oev12 in
        lem_steps_preserve_safe e12 e12' h lt12;
        lem_steps_preserve_sem_expr_shape e12 e12' h lt12 (TPair t1 t2);
        let s2 : steps (EFst e12') e' (h++lt12) lt23 = step_efst_steps in
        let (e12'', (| lt12', lt_f |)) = destruct_steps_epair_fst e12' e' (h++lt12) lt23 s2 t1 t2 in
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

let lem_destruct_steps_epair_fst
  (e1 e2:closed_exp)
  (e':closed_exp) 
  (h:history) 
  (lt:local_trace h) :
  Lemma (requires (steps (EFst (EPair e1 e2)) e' h lt /\ irred e1 h /\ irred e2 h))
        (ensures (e1 == e')) = admit ()

let can_step_esnd_when_safe (e12:closed_exp) (t1 t2:typ) (h:history) : Lemma
  (requires
    safe e12 h /\
    sem_expr_shape (TPair t1 t2) e12 h)
  (ensures (exists e' oev. step (ESnd e12) e' h oev))
  =
  introduce irred e12 h ==> (exists e' oev. step (ESnd e12) e' h oev) with _. begin
    assert (steps e12 e12 h []);
    let (EPair e1 e2) = e12 in
    let st : step (ESnd (EPair e1 e2)) e2 h None = SndPairReturn h in
    ()
  end;
  
  introduce ~(irred e12 h) ==> (exists e' oev. step (ESnd e12) e' h oev) with _. begin
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
  (t1:typ)
  (t2:typ) :
  Pure (value * (lt12:local_trace h & local_trace (h++lt12)))
    (requires irred e' (h++lt) /\
      (forall h'. safe e12 h') /\
      sem_expr_shape (TPair t1 t2) e12 h) (** CA: not sure if necessary **)
    (ensures fun (e12', (| lt12, lt_f |)) ->
      irred e12' (h++lt12) /\
      steps e12 e12' h lt12 /\
      is_closed (ESnd e12') /\
      steps (ESnd e12') e' (h++lt12) lt_f /\
      lt == (lt12 @ lt_f) /\
      (irred e12 h ==> (lt12 == [] /\ e12 == e12')))
    (decreases st)
  = match st with
    | SRefl (ESnd e12) h -> begin
      can_step_esnd_when_safe e12 t1 t2 h;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_esnd step_esnd_steps -> begin
      let (ESnd e12) = e in
      match step_esnd with
      | SndPair #e12 #e12' #h #oev12 step_e12 -> begin
        let (ESnd e12') = f2 in
        lem_step_implies_steps e12 e12' h oev12;
        lem_step_implies_steps (ESnd e12) (ESnd e12') h oev12;
        let lt12 : local_trace h = get_event_trace oev12 in
        lem_steps_preserve_safe e12 e12' h lt12;
        lem_steps_preserve_sem_expr_shape e12 e12' h lt12 (TPair t1 t2);
        let s2 : steps (ESnd e12') e' (h++lt12) lt23 = step_esnd_steps in
        let (e12'', (| lt12', lt_f |)) = destruct_steps_epair_snd e12' e' (h++lt12) lt23 s2 t1 t2 in
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

let lem_destruct_steps_epair_snd
  (e1 e2:closed_exp)
  (e':closed_exp) 
  (h:history) 
  (lt:local_trace h) :
  Lemma (requires (steps (ESnd (EPair e1 e2)) e' h lt /\ irred e1 h /\ irred e2 h))
        (ensures (e2 == e')) = admit ()
