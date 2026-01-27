(* Substitution proof from: https://fstar-lang.org/tutorial/book/part2/part2_stlc.html *)

module STLC

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot
open Trace

type typ =
  | TUnit  : typ
  | TBool  : typ
  | TFileDescr : typ
  | TArr   : typ -> typ -> typ
  | TPair  : typ -> typ -> typ
  | TSum   : typ -> typ -> typ

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
  | EInl   : exp -> exp
  | EInr   : exp -> exp
  | ECase  : exp -> exp -> exp -> exp
  | ERead  : exp -> exp
  | EWrite : exp -> exp -> exp
  | EFileDescr : fd:file_descr -> exp
  | EOpen  : exp -> exp
  | EClose : exp -> exp

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
    | EInl e' -> EInl (subst s e')
    | EInr e' -> EInr (subst s e')
    | ECase e1 e2 e3 -> ECase (subst s e1) (subst (sub_elam s) e2) (subst (sub_elam s) e3)
    | ERead e' -> ERead (subst s e')
    | EWrite e1 e2  -> EWrite (subst s e1) (subst s e2)
    | EFileDescr i -> EFileDescr i
    | EOpen e' -> EOpen (subst s e')
    | EClose e' -> EClose (subst s e')

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
  | EInl e' -> free_vars_indx e' n
  | EInr e' -> free_vars_indx e' n
  | ECase e1 e2 e3 -> free_vars_indx e1 n @ free_vars_indx e2 (n+1) @ free_vars_indx e3 (n+1)
  | ERead e' -> free_vars_indx e' n
  | EWrite e1 e2 -> free_vars_indx e1 n @ free_vars_indx e2 n
  | EFileDescr i -> []
  | EOpen e' -> free_vars_indx e' n
  | EClose e' -> free_vars_indx e' n

let free_vars e = free_vars_indx e 0

let is_closed (e:exp) : bool =
  free_vars e = []

let rec is_value (e:exp) : Type0 =
  match e with
  | EUnit -> True
  | ETrue -> True
  | EFalse -> True
  | EFileDescr _ -> True
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
  | EInr e' -> lem_value_is_closed e'
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
  | EOpen e
  | EClose e
  | ERead e ->
    lem_shifting_preserves_closed s e n
  | EWrite e1 e2
  | EApp e1 e2
  | EPair e1 e2 ->
    lem_shifting_preserves_closed s e1 n;
    lem_shifting_preserves_closed s e2 n
  | EIf e1 e2 e3 ->
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
  | EWrite e1 e2
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
  | EClose e'
  | EOpen e'
  | ERead e' ->
    assume (forall x. x `memP` free_vars_indx e' n ==> x `memP` free_vars_indx e n);(** should be provable **)
    lem_subst_freevars_closes_exp s e' n
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

let get_bool (e:value{ETrue? e \/ EFalse? e}) : bool =
  match e with
  | ETrue -> true
  | EFalse -> false

let get_ebool (b:bool) : closed_exp =
  match b with
  | true -> ETrue
  | false -> EFalse

let get_efd (fd:file_descr) : closed_exp =
  EFileDescr fd

let get_resexn_unit (x:resexn unit) : closed_exp =
  match x with
  | Inl () -> EInl EUnit
  | Inr () -> EInr EUnit

let get_resexn_bool (x:resexn bool) : closed_exp =
  match x with
  | Inl b -> EInl (get_ebool b)
  | Inr () -> EInr EUnit

let get_resexn_fd (x:resexn file_descr) : closed_exp =
  match x with
  | Inl fd -> EInl (get_efd fd)
  | Inr () -> EInr EUnit

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
    e2:closed_exp{is_value e2} ->
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
  | SCase :
    #e1:closed_exp ->
    e2:exp{is_closed (ELam e2)} ->
    e3:exp{is_closed (ELam e3)} ->
    #e1':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step e1 e1' h oev ->
    step (ECase e1 e2 e3) (ECase e1' e2 e3) h oev
  | SInl :
    #e':closed_exp ->
    #e'':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step e' e'' h oev ->
    step (EInl e') (EInl e'') h oev
  | SInlReturn :
    e1:closed_exp{is_value e1} ->
    e2:exp{is_closed (ELam e2)} ->
    e3:exp{is_closed (ELam e3)} ->
    h:history ->
    step (ECase (EInl e1) e2 e3) (subst_beta e1 e2) h None
  | SInr :
    #e':closed_exp ->
    #e'':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step e' e'' h oev ->
    step (EInr e') (EInr e'') h oev
  | SInrReturn :
    e1:closed_exp{is_value e1} ->
    e2:exp{is_closed (ELam e2)} ->
    e3:exp{is_closed (ELam e3)} ->
    h:history ->
    step (ECase (EInr e1) e2 e3) (subst_beta e1 e3) h None
  | SRead :
    #fd:closed_exp ->
    #fd':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step fd fd' h oev ->
    step (ERead fd) (ERead fd') h oev
  | SReadReturn :
    h:history ->
    fd:file_descr ->
    r:resexn bool ->
    step (ERead (get_efd fd)) (get_resexn_bool r) h (Some (EvRead fd r))
  | SWriteArg :
    #arg:closed_exp ->
    #arg':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    fd:closed_exp ->
    hst:step arg arg' h oev ->
    step (EWrite fd arg) (EWrite fd arg') h oev
  | SWriteFd :
    #fd:closed_exp ->
    #fd':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    arg:closed_exp ->
    hst:step fd fd' h oev ->
    step (EWrite fd arg) (EWrite fd' arg) h oev
  | SWriteReturn :
    h:history ->
    fd:file_descr ->
    arg:value{ETrue? arg \/ EFalse? arg} ->
    r:resexn unit ->
    step (EWrite (get_efd fd) arg) (get_resexn_unit r) h (Some (EvWrite (fd, get_bool arg) r))
  | SOpen :
    #str:closed_exp ->
    #str':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step str str' h oev ->
    step (EOpen str) (EOpen str') h oev
  | SOpenReturnSuccess :
    str:value{ETrue? str \/ EFalse? str} ->
    h:history ->
    step (EOpen str) (get_resexn_fd (Inl (fresh_fd h))) h (Some (EvOpen (get_bool str) (Inl (fresh_fd h))))
  | SOpenReturnFail :
    str:value{ETrue? str \/ EFalse? str} ->
    h:history ->
    step (EOpen str) (EInr EUnit) h (Some (EvOpen (get_bool str) (Inr ())))
  | SClose :
    #fd:closed_exp ->
    #fd':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step fd fd' h oev ->
    step (EClose fd) (EClose fd') h oev
  | SCloseReturn :
    h:history ->
    fd:file_descr ->
    r:resexn unit ->
    step (EClose (get_efd fd)) (get_resexn_unit r) h (Some (EvClose fd r))

let can_step (e:closed_exp) : Type0 =
  exists (e':closed_exp) (h:history) (oev:option (event_h h)). step e e' h oev

let indexed_can_step (e:closed_exp) (h:history) : Type0 =
  exists (e':closed_exp) (oev:option (event_h h)). step e e' h oev

let irred (e:closed_exp) : Type0 =
  forall (e':closed_exp) (h:history) (oev:option (event_h h)). ~(step e e' h oev)

let indexed_irred (e:closed_exp) (h:history) : Type0 =
  forall (e':closed_exp) (oev:option (event_h h)). ~(step e e' h oev)

let rec lem_value_is_irred (e:closed_exp) : Lemma
  (requires is_value e)
  (ensures (irred e)) =
  match e with
  | EPair e1 e2 ->
    lem_value_is_irred e1;
    lem_value_is_irred e2;
    introduce forall (e':closed_exp) (h:history) (oev:option (event_h h)). step e e' h oev ==> False with begin
      introduce step e e' h oev ==> False with _. begin
        FStar.Squash.bind_squash #(step e e' h oev) () (fun st ->
        match st with
        | PairLeft e2 hst -> ()
        | PairRight e1 hst -> ()
        | _ -> ())
      end
    end
  | EInl e12 ->
    lem_value_is_irred e12;
    introduce forall (e':closed_exp) (h:history) (oev:option (event_h h)). step e e' h oev ==> False with begin
      introduce step e e' h oev ==> False with _. begin
        FStar.Squash.bind_squash #(step e e' h oev) () (fun st ->
        match st with
        | SInl hst -> ()
        | _ -> ())
      end
    end
  | EInr e12 ->
    lem_value_is_irred e12;
    introduce forall (e':closed_exp) (h:history) (oev:option (event_h h)). step e e' h oev ==> False with begin
      introduce step e e' h oev ==> False with _. begin
        FStar.Squash.bind_squash #(step e e' h oev) () (fun st ->
        match st with
        | SInr hst -> ()
        | _ -> ())
      end
    end
  | _ -> assert (forall h e' oev. ~(step e e' h oev)) by (explode ())

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
           #lt:local_trace (h++(as_lt oev)) ->
           step e1 e2 h oev ->
           steps e2 e3 (h++(as_lt oev)) lt ->
           steps e1 e3 h (as_lt oev @ lt)

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

let lem_step_implies_steps (e e':closed_exp) (h:history) (oev:option (event_h h)) :
  Lemma
    (requires step e e' h oev)
    (ensures steps e e' h (as_lt oev)) =
  introduce forall e e'. step e e' h oev ==> steps e e' h (as_lt oev) with begin
    introduce step e e' h oev ==> steps e e' h (as_lt oev) with _. begin
      bind_squash #(step e e' h oev) () (fun st -> return_squash (STrans st (SRefl e' (h++(as_lt oev)))))
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

let lem_steps_refl (e:closed_exp) (h:history) : Lemma (steps e e h []) [SMTPat (steps e e h [])] =
  FStar.Squash.return_squash (SRefl e h)

let safe (e:closed_exp) : Type0 =
  forall (e':closed_exp) (h:history) (lt:local_trace h). steps e e' h lt ==> (is_value e' \/ indexed_can_step e' (h++lt))

let indexed_safe (e:closed_exp) (h:history) : Type0 =
  forall (e':closed_exp) (lt:local_trace h). steps e e' h lt ==> (is_value e' \/ indexed_can_step e' (h++lt))

let lem_step_preserve_indexed_safe (e e':closed_exp) (h:history) (oev:option (event_h h)) :
  Lemma (requires indexed_safe e h /\ step e e' h oev)
        (ensures indexed_safe e' (h++(as_lt oev))) =
  introduce forall e'' lt'. steps e' e'' (h++(as_lt oev)) lt' ==> (is_value e'' \/ indexed_can_step e'' ((h++(as_lt oev))++lt')) with begin
    introduce _ ==> _ with _. begin
      lem_step_implies_steps e e' h oev;
      lem_steps_transitive e e' e'' h (as_lt oev) lt';
      eliminate forall e' lt. steps e e' h lt ==> (is_value e' \/ indexed_can_step e' (h++lt)) with e'' ((as_lt oev) @ lt');
      ()
    end
  end

let lem_value_is_safe (e:closed_exp) :
  Lemma (requires is_value e)
        (ensures safe e) = admit ()

let get_read_arg (ev:event{EvRead? ev}) : io_args ORead =
  match ev with
  | EvRead arg res -> arg

let get_read_res (args:io_args ORead) (ev:event{EvRead? ev}) : io_res ORead args =
  match ev with
  | EvRead arg res -> res

let get_open_arg (ev:event{EvOpen? ev}) : io_args OOpen =
  match ev with
  | EvOpen arg res -> arg

let get_open_res (args:io_args OOpen) (ev:event{EvOpen? ev}) : io_res OOpen args =
  match ev with
  | EvOpen arg res -> res

let get_einl_v (x:closed_exp{EInl? x}) =
  match x with
  | EInl v -> v

let get_einr_v (x:closed_exp{EInr? x}) =
  match x with
  | EInr v -> v

//assume val get_new_file_descr (ev:event{EvOpen? ev}) (h':history) : (ev':event{test_event h' ev'})

(*let corresponding_event #h #h' (oev:option (event_h h)) (oev':option (event_h h')) =
  (None? oev <==> None? oev') /\
  ((Some? oev /\ (test_event h' (Some?.v oev))) ==>
    (oev == oev')) /\ // if the read/write/open/close was an error, it would be an error in any history
  ((Some? oev /\ (EvRead? (Some?.v oev)) /\ (~(test_event h' (Some?.v oev)))) ==>
    ((EInl? (get_read_res (get_read_arg (Some?.v oev)) (Some?.v oev))) /\ (oev' == Some (EvRead (get_read_arg (Some?.v oev)) (Inr ()))))) /\
  // this will look the same for EvWrite
  ((Some? oev /\ (EvOpen? (Some?.v oev)) /\ (~(test_event h' (Some?.v oev)))) ==>
    ((EInl? (get_open_res (get_open_arg (Some?.v oev)) (Some?.v oev))) /\ (oev' == Some (get_new_file_descr (Some?.v oev) h'))))*)
  //((Some? oev /\ (EvClose? (Some?.v oev)) /\

// h = [] [1]
// h' = [] (1 - 1) + 1 = [1]

// h = [3, 2, 1] [2, 3, OpenFile 4, 4]
// h' = [4, 3, 2, 1] [2, 3, OpenFile 5, 5]

// (fd - (last_fd h)) + (last_fd h')

// h = [1 2 3] [4]
// h' = [] [1]

// TODO: add file descr to read and write (and check that they are in the bounds of the semantics, so 1 and last fd of the history)

let new_event' #h #h' (oev:option (event_h h)) : option (event_h h') =
  match oev with
  | None -> None
  | Some (EvOpen str (Inl fd)) -> Some (EvOpen str (Inl (fresh_fd h')))
    // I think fresh_fd should return the max_fd (since file descriptors are forgeable and we can't guarantee that they'll increase monotonically
  | Some (EvRead fd (Inl b)) -> if (valid_fd h' fd) then Some (EvRead fd (Inl b)) else Some (EvRead fd (Inr ()))
    // and here, valid_fd should check that fd appears in h' (not just whether it is in the range)
  | Some (EvWrite (fd, arg) (Inl ())) -> if (valid_fd h' fd) then Some (EvWrite (fd, arg) (Inl ())) else Some (EvWrite (fd, arg) (Inr ()))
  | Some (EvClose fd (Inl ())) -> if (valid_fd h' fd) then Some (EvClose fd (Inl ())) else Some (EvClose fd (Inr ()))
  | _ -> oev // evopen inr (), evread inr ()

(*let new_event #h #h' (oev:option (event_h h)) : option (event_h h') =
  match oev with
  | None -> None
  | Some (EvOpen str (Inl fd)) -> Some (EvOpen str (Inl (fresh_fd h')))
  | Some (EvRead fd r) -> Some (EvRead (recast_fd h h' fd) r)
  | Some (EvWrite (fd, arg) r) -> Some (EvWrite ((recast_fd h h' fd), arg) r)
  | Some (EvClose fd arg) -> Some (EvClose (recast_fd h h' fd) arg)
  | _ -> oev*)

// should be able to try to read from closed file descriptors -> error

// example correct traces:
// [EvOpen "0" -> Inl true, EvWrite true -> Inl (), EvRead () -> Inl true, EvClose true -> Inl ()]

// rules as I understand them when we change histories:
// 1. EvRead fails if an EvOpen does NOT precede it AND if something has NOT been written to the file
// 2. EvWrite fails if an EvOpen does NOT precede it
// 3. EvOpen never fails but returns different file descriptor
// 4. EvClose fails if an EvOpen with the same file descriptor does NOT precede it

(* We need syntactic types for this, or at least the top-level shape of types *)
let sem_value_shape (t:typ) (e:closed_exp) : Tot Type0 =
  match t with
  | TUnit -> e == EUnit
  | TBool -> e == ETrue \/ e == EFalse
  | TArr t1 t2 -> ELam? e
  | TPair t1 t2 -> EPair? e
  | TSum t1 t2 -> EInl? e \/ EInr? e

let sem_expr_shape (t:typ) (e:closed_exp) : Tot Type0 =
  forall (e':closed_exp) (h:history) (lt:local_trace h). steps e e' h lt ==> irred e' ==> sem_value_shape t e'

let indexed_sem_expr_shape (t:typ) (e:closed_exp) (h:history) : Tot Type0 =
  forall (e':closed_exp) (lt:local_trace h). steps e e' h lt ==> indexed_irred e' (h++lt) ==> sem_value_shape t e'

let lem_step_preserve_indexed_sem_expr_shape (e e':closed_exp) (h:history) (oev:option (event_h h)) (t:typ) :
  Lemma
    (requires indexed_sem_expr_shape t e h /\ step e e' h oev)
    (ensures indexed_sem_expr_shape t e' (h++(as_lt oev))) =
  introduce forall e'' lt'. steps e' e'' (h++(as_lt oev)) lt' /\ indexed_irred e'' ((h++(as_lt oev))++lt') ==> sem_value_shape t e'' with begin
    introduce _  ==> sem_value_shape t e'' with _. begin
      lem_step_implies_steps e e' h oev;
      lem_steps_transitive e e' e'' h (as_lt oev) lt';
      eliminate forall e' lt. steps e e' h lt /\ indexed_irred e' (h++lt) ==> sem_value_shape t e' with e'' ((as_lt oev) @ lt');
      ()
    end
  end

let lem_steps_preserve_is_value (e e_ :closed_exp) (h:history) (lt_:local_trace h) :
  Lemma (requires (forall e' lt. steps e e' h lt /\ indexed_irred e' (h++lt) ==> is_value e') /\ steps e e_ h lt_)
        (ensures (forall e' lt. steps e_ e' (h++lt_) lt /\ indexed_irred e' ((h++lt_)++lt) ==> is_value e')) =
  introduce forall e' lt. steps e_ e' (h++lt_) lt /\ indexed_irred e' ((h++lt_)++lt) ==> is_value e' with begin
    introduce _ ==> _ with _. begin
      lem_steps_transitive e e_ e' h lt_ lt
    end
  end

let lem_steps_preserve_is_lam_value (e e_ :closed_exp) (h:history) (lt_:local_trace h) :
  Lemma (requires (forall e' lt. steps e e' h lt /\ indexed_irred e' (h++lt) ==> (ELam? e' /\ is_closed e')) /\ steps e e_ h lt_)
        (ensures (forall e' lt. steps e_ e' (h++lt_) lt /\ indexed_irred e' ((h++lt_)++lt) ==> (ELam? e' /\ is_closed e'))) =
  introduce forall e' lt. steps e_ e' (h++lt_) lt /\ indexed_irred e' ((h++lt_)++lt) ==> (ELam? e' /\ is_closed e') with begin
    introduce _ ==> _ with _. begin
      lem_steps_transitive e e_ e' h lt_ lt
    end
  end

let lem_steps_preserve_is_bool_value (e e_ :closed_exp) (h:history) (lt_:local_trace h) :
  Lemma (requires (forall e' lt. steps e e' h lt /\ indexed_irred e' (h++lt) ==> (ETrue? e' \/ EFalse? e')) /\ steps e e_ h lt_)
        (ensures (forall e' lt. steps e_ e' (h++lt_) lt /\ indexed_irred e' ((h++lt_)++lt) ==> (ETrue? e' \/ EFalse? e'))) =
  introduce forall e' lt. steps e_ e' (h++lt_) lt /\ indexed_irred e' ((h++lt_)++lt) ==> (ETrue? e' \/ EFalse? e') with begin
    introduce _ ==> _ with _. begin
      lem_steps_transitive e e_ e' h lt_ lt
    end
  end

let lem_steps_preserve_is_pair_value (e e_ :closed_exp) (h:history) (lt_:local_trace h) :
  Lemma (requires (forall e' lt. steps e e' h lt /\ indexed_irred e' (h++lt) ==> (EPair? e' /\ is_value e')) /\ steps e e_ h lt_)
        (ensures (forall e' lt. steps e_ e' (h++lt_) lt /\ indexed_irred e' ((h++lt_)++lt) ==> (EPair? e' /\ is_value e'))) =
  introduce forall e' lt. steps e_ e' (h++lt_) lt /\ indexed_irred e' ((h++lt_)++lt) ==> (EPair? e' /\ is_value e') with begin
    introduce _ ==> _ with _. begin
      lem_steps_transitive e e_ e' h lt_ lt
    end
  end

let lem_steps_preserve_is_sum_value (e e_ :closed_exp) (h:history) (lt_:local_trace h) :
  Lemma (requires (forall e' lt. steps e e' h lt /\ indexed_irred e' (h++lt) ==> ((EInl? e' \/ EInr? e') /\ is_value e')) /\ steps e e_ h lt_)
        (ensures (forall e' lt. steps e_ e' (h++lt_) lt /\ indexed_irred e' ((h++lt_)++lt) ==> ((EInl? e' \/ EInr? e') /\ is_value e'))) =
  introduce forall e' lt. steps e_ e' (h++lt_) lt /\ indexed_irred e' ((h++lt_)++lt) ==> ((EInl? e' \/ EInr? e') /\ is_value e') with begin
    introduce _ ==> _ with _. begin
      lem_steps_transitive e e_ e' h lt_ lt
    end
  end

// DESTRUCT LEMMAS

let can_step_eapp_when_safe (e1 e2:closed_exp) (h:history) : Lemma
  (requires
    ((indexed_irred e1 h /\ steps e1 e1 h []) ==> (ELam? e1 /\ is_closed e1)) /\
    ((indexed_irred e2 h /\ steps e2 e2 h []) ==> is_value e2))
  (ensures (exists e' oev. step (EApp e1 e2) e' h oev))
  =
  (**
     We case analyze if e1 can step or if e2 can step,
       and for each case, we build a step accordingly **)

  introduce indexed_irred e1 h /\ indexed_irred e2 h ==> (exists e' oev. step (EApp e1 e2) e' h oev) with _. begin
    assert (steps e1 e1 h []);
    assert (steps e2 e2 h []);
    let ELam e11 = e1 in
    let st : step (EApp (ELam e11) e2) (subst_beta e2 e11) h None = Beta e11 e2 h in
    ()
  end;

  introduce ~(indexed_irred e1 h) /\ indexed_irred e2 h ==> (exists e' oev. step (EApp e1 e2) e' h oev) with _. begin
    assert (steps e2 e2 h []);
    assert (exists e1' oev1. step e1 e1' h oev1);
    eliminate exists e1' oev1. step e1 e1' h oev1 returns exists e' oev. step (EApp e1 e2) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (AppLeft e2 st))
    end
  end;

  introduce ~(indexed_irred e2 h) ==>  (exists e' oev. step (EApp e1 e2) e' h oev) with _. begin
    assert (exists e2' oev2. step e2 e2' h oev2);
    eliminate exists e2' oev2. step e2 e2' h oev2 returns exists e' oev. step (EApp e1 e2) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (AppRight e1 st))
    end
  end

let lem_irred_eapp_implies_irred_e2 (e1 e2:closed_exp) (h:history) :
  Lemma (requires indexed_irred (EApp e1 e2) h)
        (ensures indexed_irred e2 h) =
  introduce forall (e2':closed_exp) (oev:option (event_h h)). step e2 e2' h oev ==> False with begin
    introduce _ ==> _ with st. begin
      bind_squash st (fun st -> return_squash (AppRight e1 #e2 #e2' #h #oev st))
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
  (e2':closed_exp{is_value e2'})
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EApp e1 e2') e' h lt) :
  Pure (exp * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt) /\
              (forall e1' (lt1:local_trace h). (steps e1 e1' h lt1 /\ indexed_irred e1' (h++lt1)) ==> (ELam? e1' /\ is_closed e1')))
    (ensures fun (e11, (| lt1, lt' |)) ->
      is_closed (ELam e11) /\
      steps e1 (ELam e11) h lt1 /\
      steps (EApp e1 e2') (subst_beta e2' e11) h lt1 /\
      steps (subst_beta e2' e11) e' (h++lt1) lt' /\
      (lt == (lt1 @ lt')) /\
      (indexed_irred e1 h ==> (lt1 == [] /\ e1 == ELam e11)))
    (decreases st) =
    match st with
    | SRefl (EApp e1 e2') h -> begin
      can_step_eapp_when_safe e1 e2' h;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_eapp step_eapp_steps -> begin
      let (EApp e1 e2') = e in
      match step_eapp with
      | AppLeft #e1 e2' #e1' #h #oev1 step_e1 -> begin
        let (EApp e1' e2') = f2 in
        lem_step_implies_steps e1 e1' h oev1;
        lem_step_implies_steps (EApp e1 e2') (EApp e1' e2') h oev1;
        let lt1 : local_trace h = as_lt oev1 in
        let s2 : steps (EApp e1' e2') e' (h++lt1) lt23 = step_eapp_steps in
        lem_steps_preserve_is_lam_value e1 e1' h lt1;
        let (e11, (| lt1', lt' |)) = destruct_steps_eapp_e1 e1' e2' e' (h++lt1) lt23 s2 in
        lem_steps_transitive e1 e1' (ELam e11) h lt1 lt1';
        lem_steps_transitive (EApp e1 e2') (EApp e1' e2') (subst_beta e2' e11) h lt1 lt1';
        (e11, (| (lt1 @ lt1'), lt' |))
        end
      | AppRight _ _ -> begin
        lem_value_is_irred e2';
        (e1, (| [], lt |))
        end
      | Beta e11 e2' h -> begin
        lem_step_implies_steps (EApp e1 e2') (subst_beta e2' e11) h None;
        (e11, (| [], lt |))
        end
      end

let rec destruct_steps_eapp_e2
  (e1:closed_exp)
  (e2:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EApp e1 e2) e' h lt) :
  Pure (value * (lt2:local_trace h & local_trace (h++lt2)))
    (requires indexed_irred e' (h++lt) /\
      (forall e2' lt2. steps e2 e2' h lt2 /\ indexed_irred e2' (h++lt2) ==> is_value e2'))
    (ensures fun (e2', (| lt2, lt' |)) ->
      steps e2 e2' h lt2 /\
      steps (EApp e1 e2) (EApp e1 e2') h lt2 /\
      steps (EApp e1 e2') e' (h++lt2) lt' /\
      (lt == (lt2 @ lt')) /\
      (indexed_irred e2 h ==> (lt2 == [] /\ e2 == e2')))
    (decreases st) =
    match st with
    | SRefl (EApp e1 e2) h -> begin
      lem_irred_eapp_implies_irred_e2 e1 e2 h;
      (e2, (| [], lt |))
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_eapp step_eapp_steps -> begin
      let (EApp e1 e2) = e in
      match step_eapp with
      | AppRight e1 #e2 #e2' #h #oev2 step_e2 -> begin
        let (EApp e1 e2') = f2 in
        lem_step_implies_steps e2 e2' h oev2;
        lem_step_implies_steps (EApp e1 e2) (EApp e1 e2') h oev2;
        let lt2 : local_trace h = as_lt oev2 in
        let s2 : steps (EApp e1 e2') e' (h++lt2) lt23 = step_eapp_steps in
        lem_steps_preserve_is_value e2 e2' h lt2;
        let (e2'', (| lt2', lt' |)) = destruct_steps_eapp_e2 e1 e2' e' (h++lt2) lt23 s2 in
        lem_steps_transitive e2 e2' e2'' h lt2 lt2';
        lem_steps_transitive (EApp e1 e2) (EApp e1 e2') (EApp e1 e2'') h lt2 lt2';
        (e2'', (| (lt2 @ lt2'), lt' |))
        end
      | _ -> (e2, (| [], lt |))
      end

let can_step_eif_when_safe (e1 e2 e3:closed_exp) (h:history) : Lemma
  (requires
    (forall e1' lt1. (steps e1 e1' h lt1 /\ indexed_irred e1' (h++lt1)) ==> (ETrue? e1' \/ EFalse? e1')))
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

let rec destruct_steps_eif
  (e1:closed_exp)
  (e2:closed_exp)
  (e3:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EIf e1 e2 e3) e' h lt) :
  Pure (closed_exp * (lt1:local_trace h & (local_trace (h++lt1) * local_trace (h++lt1))))
    (requires indexed_irred e' (h++lt) /\
       (forall e1' lt1. (steps e1 e1' h lt1 /\ indexed_irred e1' (h++lt1)) ==> (ETrue? e1' \/ EFalse? e1')))
    (ensures fun (e1', (| lt1, (lt2, lt3) |)) ->
      indexed_irred e1' (h++lt1) /\
      steps e1 e1' h lt1 /\
      steps (EIf e1 e2 e3) (EIf e1' e2 e3) h lt1 /\
      (ETrue? e1' ==> (steps e2 e' (h++lt1) lt2 /\ lt == lt1 @ lt2)) /\
      (EFalse? e1' ==> (steps e3 e' (h++lt1) lt3 /\ lt == lt1 @ lt3)) /\
      ((lt == lt1 @ lt2) \/ (lt == lt1 @ lt3)) /\
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
        lem_steps_preserve_is_bool_value e1 e1' h lt1;
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
  (requires safe e1 /\ safe e2 /\ indexed_irred (EPair e1 e2) h)
  (ensures is_value (EPair e1 e2))
  =
  introduce indexed_irred e1 h /\ indexed_irred e2 h ==> is_value (EPair e1 e2) with _.
  begin
    assert (steps e1 e1 h []);
    assert (steps e2 e2 h []);
    ()
  end;

  introduce ~(indexed_irred e1 h) ==> is_value (EPair e1 e2) with _.
  begin
    assert (exists e1' oev1. step e1 e1' h oev1);
    eliminate exists e1' oev1. step e1 e1' h oev1 returns exists e' oev. step (EPair e1 e2) e' h oev with st.
    begin
      bind_squash st (fun st -> return_squash (PairLeft e2 st))
    end;
    false_elim ()
  end;

  introduce indexed_irred e1 h /\ ~(indexed_irred e2 h) ==> is_value (EPair e1 e2) with _.
  begin
    assert (steps e1 e1 h []);
    assert (exists e2' oev2. step e2 e2' h oev2);
    eliminate exists e2' oev2. step e2 e2' h oev2 returns exists e' oev. step (EPair e1 e2) e' h oev with st.
    begin
      bind_squash st (fun st -> return_squash (PairRight e1 st))
    end;
    false_elim ()
  end

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

let rec destruct_steps_epair_e1
  (e1:closed_exp)
  (e2:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EPair e1 e2) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt) /\
      (forall e1' lt1. steps e1 e1' h lt1 /\ indexed_irred e1' (h++lt1) ==> is_value e1'))
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
      lem_steps_preserve_is_value e1 e1' h lt1;
      let (e1'', (| lt1', lt' |)) = destruct_steps_epair_e1 e1' e2 e' (h++lt1) lt23 s2 in
      lem_steps_transitive e1 e1' e1'' h lt1 lt1';
      lem_steps_transitive (EPair e1 e2) (EPair e1' e2) (EPair e1'' e2) h lt1 lt1';
      (e1'', (| (lt1 @ lt1'), lt' |))
      end
    | _ -> (e1, (| [], lt |))
    end

let rec destruct_steps_epair_e2
  (e1':closed_exp{is_value e1'})
  (e2:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EPair e1' e2) e' h lt) :
  Pure (value * (lt2:local_trace h & local_trace (h++lt2)))
    (requires indexed_irred e' (h++lt) /\
      (forall e2' lt2. steps e2 e2' h lt2 /\ indexed_irred e2' (h++lt2) ==> is_value e2'))
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
      lem_steps_preserve_is_value e2 e2' h lt2;
      let (e2'', (| lt2', lt' |)) = destruct_steps_epair_e2 e1' e2' e' (h++lt2) lt23 s2 in
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
        (ensures ((EPair e1' e2') == e')) = admit ()

let can_step_efst_when_safe (e12:closed_exp) (h:history) : Lemma
  (requires
    (forall e12' lt12. (steps e12 e12' h lt12 /\ indexed_irred e12' (h++lt12)) ==> (EPair? e12' /\ is_value e12')))
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
  (st:steps (EFst e12) e' h lt) :
  Pure (value * (lt12:local_trace h & local_trace (h++lt12)))
    (requires indexed_irred e' (h++lt) /\
      (forall e12' lt12. (steps e12 e12' h lt12 /\ indexed_irred e12' (h++lt12)) ==> (EPair? e12' /\ is_value e12'))) (** CA: not sure if necessary **)
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
      can_step_efst_when_safe e12 h;
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
        lem_steps_preserve_is_pair_value e12 e12' h lt12;
        let s2 : steps (EFst e12') e' (h++lt12) lt23 = step_efst_steps in
        let (e12'', (| lt12', lt_f |)) = destruct_steps_epair_fst e12' e' (h++lt12) lt23 s2 in
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
  Lemma (requires (steps (EFst (EPair e1 e2)) e' h lt /\ indexed_irred e1 h /\ indexed_irred e2 h))
        (ensures (e1 == e') /\ lt == []) = admit ()

let can_step_esnd_when_safe (e12:closed_exp) (h:history) : Lemma
  (requires
    (forall e12' lt12. (steps e12 e12' h lt12 /\ indexed_irred e12' (h++lt12)) ==> (EPair? e12' /\ is_value e12')))
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
  (st:steps (ESnd e12) e' h lt) :
  Pure (value * (lt12:local_trace h & local_trace (h++lt12)))
    (requires indexed_irred e' (h++lt) /\
      (forall e12' lt12. (steps e12 e12' h lt12 /\ indexed_irred e12' (h++lt12)) ==> (EPair? e12' /\ is_value e12'))) (** CA: not sure if necessary **)
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
      can_step_esnd_when_safe e12 h;
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
        lem_steps_preserve_is_pair_value e12 e12' h lt12;
        let s2 : steps (ESnd e12') e' (h++lt12) lt23 = step_esnd_steps in
        let (e12'', (| lt12', lt_f |)) = destruct_steps_epair_snd e12' e' (h++lt12) lt23 s2 in
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
  Lemma (requires (steps (ESnd (EPair e1 e2)) e' h lt /\ indexed_irred e1 h /\ indexed_irred e2 h))
        (ensures (e2 == e') /\ lt == []) = admit ()

let srefl_einl_implies_value (e12:closed_exp) (h:history) : Lemma
  (requires (forall e12' lt12. steps e12 e12' h lt12 /\ indexed_irred e12' (h++lt12) ==> is_value e12') /\ indexed_irred (EInl e12) h)
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
      (forall e12' lt12. steps e12 e12' h lt12 /\ indexed_irred e12' (h++lt12) ==> is_value e12'))
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
      lem_steps_preserve_is_value e12 e12' h lt12;
      let s2 : steps (EInl e12') e' (h++lt12) lt23 = step_einl_steps in
      let (e12'', (| lt12', lt_f |)) = destruct_steps_einl e12' e' (h++lt12) lt23 s2 in
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
  (requires (forall e12' lt12. steps e12 e12' h lt12 /\ indexed_irred e12' (h++lt12) ==> is_value e12') /\ indexed_irred (EInr e12) h)
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
              (forall e12' lt12. steps e12 e12' h lt12 /\ indexed_irred e12' (h++lt12) ==> is_value e12'))
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
      lem_steps_preserve_is_value e12 e12' h lt12;
      let s2 : steps (EInr e12') e' (h++lt12) lt23 = step_einr_steps in
      let (e12'', (| lt12', lt_f |)) = destruct_steps_einr e12' e' (h++lt12) lt23 s2 in
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

let can_step_ecase_when_safe (e_case:closed_exp) (e_lc:exp{is_closed (ELam e_lc)}) (e_rc:exp{is_closed (ELam e_rc)}) (h:history) : Lemma
  (requires
    (forall e_case' lt'. steps e_case e_case' h lt' /\ indexed_irred e_case' (h++lt') ==> ((EInl? e_case' \/ EInr? e_case') /\ is_value e_case')))
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

#push-options "--z3rlimit 10000"
let rec destruct_steps_ecase
  (e_case:closed_exp)
  (e_lc:exp{is_closed (ELam e_lc)})
  (e_rc:exp{is_closed (ELam e_rc)})
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (ECase e_case e_lc e_rc) e' h lt) :
  Pure (closed_exp * (lt1:local_trace h & (local_trace (h++lt1) * local_trace (h++lt1))))
    (requires indexed_irred e' (h++lt) /\
      (forall e_case' lt'. steps e_case e_case' h lt' /\ indexed_irred e_case' (h++lt') ==> ((EInl? e_case' \/ EInr? e_case') /\ is_value e_case')))
    (ensures fun (e_case', (| lt1, (lt2, lt3) |)) ->
      indexed_irred e_case' (h++lt1) /\
      steps e_case e_case' h lt1 /\
      steps (ECase e_case e_lc e_rc) (ECase e_case' e_lc e_rc) h lt1 /\
      (EInl? e_case' ==>
        (e_case' == EInl (get_einl_v e_case')) /\
        (steps (ECase e_case e_lc e_rc) (subst_beta (get_einl_v e_case') e_lc) h lt1) /\
        (steps (subst_beta (get_einl_v e_case') e_lc) e' (h++lt1) lt2) /\
        (lt == (lt1 @ lt2))) /\
      (EInr? e_case' ==>
        (e_case' == EInr (get_einr_v e_case')) /\
        (steps (ECase e_case e_lc e_rc) (subst_beta (get_einr_v e_case') e_rc) h lt1) /\
        (steps (subst_beta (get_einr_v e_case') e_rc) e' (h++lt1) lt3) /\
        (lt == (lt1 @ lt3))) /\
      ((lt == lt1 @ lt2) \/ (lt == lt1 @ lt3)) /\
      (indexed_irred e_case h ==> (lt1 == [] /\ e_case == e_case')))
    (decreases st)
  = match st with
    | SRefl (ECase e_case e_lc e_rc) h -> begin
      can_step_ecase_when_safe e_case e_lc e_rc h;
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
        lem_steps_preserve_is_sum_value e_case e_case' h lt1;
        let s2 : steps (ECase e_case' e_lc e_rc) e' (h++lt1) lt23 = step_ecase_steps in
        let (e_case'', (| lt1', (lt2, lt3) |)) = destruct_steps_ecase e_case' e_lc e_rc e' (h++lt1) lt23 s2 in
        lem_steps_transitive e_case e_case' e_case'' h lt1 lt1';
        lem_steps_transitive (ECase e_case e_lc e_rc) (ECase e_case' e_lc e_rc) (ECase e_case'' e_lc e_rc) h lt1 lt1';
        match e_case'' with
        | EInl v -> begin
          lem_steps_transitive (ECase e_case e_lc e_rc) (ECase e_case' e_lc e_rc) (subst_beta v e_lc) h lt1 lt1';
          (e_case'', (| (lt1 @ lt1'), (lt2, lt3) |))
          end
        | EInr v -> begin
          lem_steps_transitive (ECase e_case e_lc e_rc) (ECase e_case' e_lc e_rc) (subst_beta v e_rc) h lt1 lt1';
          (e_case'', (| (lt1 @ lt1'), (lt2, lt3) |))
          end
        | _ -> false_elim ()
        end
      | SInlReturn e_c' e_lc e_rc h -> begin
        lem_step_implies_steps (ECase (EInl e_c') e_lc e_rc) (subst_beta e_c' e_lc) h None;
        lem_value_is_irred (EInl e_c');
        (EInl e_c', (| [], (lt, []) |))
        end
      | SInrReturn e_c' e_lc e_rc h -> begin
        lem_step_implies_steps (ECase (EInr e_c') e_lc e_rc) (subst_beta e_c' e_rc) h None;
        lem_value_is_irred (EInr e_c');
        (EInr e_c', (| [], ([], lt) |))
        end
      end
#pop-options

(*let can_step_eread (h:history) :
  Lemma (ensures (exists e' oev. step ERead e' h oev)) =
  let st1 : step ERead (EInl ETrue) h (Some (EvRead () (Inl true))) = SRead (Inl true) h in
  let st2 : step ERead (EInl EFalse) h (Some (EvRead () (Inl false))) = SRead (Inl false) h in
  let st3: step ERead (EInr EUnit) h (Some (EvRead () (Inr ()))) = SRead (Inr ()) h in
  ()

let destruct_steps_eread
  (fd:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (ERead fd) e' h lt) :
  Pure (value * file_descr * (lt1:local_trace h & lt2:local_trace (h++lt1) & (local_trace ((h++lt1)++lt2) * local_trace ((h++lt1)++lt2) * local_trace ((h++lt1)++lt2))))
    (requires indexed_irred e' (h++lt) /\
      (forall fd' lt'. (steps fd fd' h lt' /\ indexed_irred fd' (h++lt')) ==> (EFileDescr? fd' /\ is_value fd')))
    (ensures fun (e_r, fd', (| lt1, lt2, (lt3, lt4, lt5) |)) ->
       steps (ERead fd) (ERead (get_efd fd')) h lt1 /\
       steps (ERead (get_efd fd')) e_r (h++lt1) lt2 /\
       (e_r == EInl ETrue \/ e_r == EInl EFalse \/ e_r == EInr EUnit) /\
       (EInl? e_r ==> (ETrue? (get_einl_v e_r) ==> (steps e_r e' ((h++lt1)++lt2) lt3 /\ lt == ((lt1 @ lt2) @ lt3) /\ lt2 == [EvRead fd' (Inl true)])) /\
                     (EFalse? (get_einl_v e_r) ==> (steps e_r e' ((h++lt1)++lt2) lt4 /\ lt == ((lt1 @ lt2) @ lt3) /\ lt2 == [EvRead fd' (Inl false)]))) /\
       (EInr? e_r ==> steps e_r e' ((h++lt1)++lt2) lt5 /\ lt == ((lt1 @ lt2) @ lt4) /\ lt2 == [EvRead fd' (Inr ())]) /\
       ((lt == (lt1 @ lt2) @ lt3) \/ (lt == (lt1 @ lt2) @ lt4) \/ (lt == (lt1 @ lt2) @ lt5)))
    (decreases st) = admit ()
    (*match st with
    | SRefl ERead h -> begin
      can_step_eread h;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_eread step_eread_steps -> begin
      let ERead = e in
      match step_eread with
      | SRead (Inl true) h -> begin
        let EInl ETrue = f2 in
        lem_step_implies_steps ERead (EInl ETrue) h (Some (EvRead () (Inl true)));
        let lt' : local_trace h = [EvRead () (Inl true)] in
        let s2 : steps (EInl ETrue) e' (h++lt') lt23 = step_eread_steps in
        lem_value_is_safe ETrue;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einl ETrue e' (h++lt') lt23 s2 TBool TUnit in
        (f2, (| lt', (lt12 @ lt_f, [], []) |))
        end
      | SRead (Inl false) h -> begin
        let EInl EFalse = f2 in
        lem_step_implies_steps ERead (EInl EFalse) h (Some (EvRead () (Inl false)));
        let lt' : local_trace h = [EvRead () (Inl false)] in
        let s2 : steps (EInl EFalse) e' (h++lt') lt23 = step_eread_steps in
        lem_value_is_safe EFalse;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einl EFalse e' (h++lt') lt23 s2 TBool TUnit in
        (f2, (| lt', ([], lt12 @ lt_f, []) |))
        end
      | SRead (Inr ()) h -> begin
        let EInr EUnit = f2 in
        lem_step_implies_steps ERead (EInr EUnit) h (Some (EvRead () (Inr ())));
        let lt' : local_trace h = [EvRead () (Inr ())] in
        let s2 : steps (EInr EUnit) e' (h++lt') lt23 = step_eread_steps in
        lem_value_is_safe EUnit;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einr EUnit e' (h++lt') lt23 s2 TBool TUnit in
        (f2, (| lt', ([], [], (lt12 @ lt_f)) |))
        end
      end

(*let can_step_ewrite_when_safe (arg:closed_exp) (h:history) :
  Lemma (requires
          safe arg /\
          indexed_sem_expr_shape TBool arg h)
        (ensures (exists e' oev. step (EWrite arg) e' h oev))
  =
  introduce indexed_irred arg h /\ arg == ETrue ==> (exists e' oev. step (EWrite arg) e' h oev) with _. begin
    assert (steps arg arg h []);
    let _ : step (EWrite ETrue) (EInl EUnit) h (Some (EvWrite true (Inl ()))) = SWriteReturn ETrue (Inl ()) h in
    let _ : step (EWrite ETrue) (EInr EUnit) h (Some (EvWrite true (Inr ()))) = SWriteReturn ETrue (Inr ()) h in
    ()
  end;

  introduce indexed_irred arg h /\ arg == EFalse ==> (exists e' oev. step (EWrite arg) e' h oev) with _. begin
    assert (steps arg arg h []);
    let _ : step (EWrite EFalse) (EInl EUnit) h (Some (EvWrite false (Inl ()))) = SWriteReturn EFalse (Inl ()) h in
    let _ : step (EWrite EFalse) (EInr EUnit) h (Some (EvWrite false (Inr ()))) = SWriteReturn EFalse (Inr ()) h in
    ()
  end;

  introduce indexed_irred arg h /\ ~(arg == EFalse \/ arg == ETrue) ==> (exists e' oev. step (EWrite arg) e' h oev) with _. begin
    assert (steps arg arg h []);
    false_elim ()
  end;

  introduce ~(indexed_irred arg h) ==> (exists e' oev. step (EWrite arg) e' h oev) with _. begin
    assert (exists arg' oev'. step arg arg' h oev');
    eliminate exists arg' oev'. step arg arg' h oev' returns exists e' oev. step (EWrite arg) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (SWrite st))
    end
  end

let rec destruct_steps_ewrite
  (arg:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EWrite arg) e' h lt) :
  Pure (closed_exp * value * (lt1:local_trace h & (lt2:local_trace (h++lt1) & (local_trace ((h++lt1)++lt2) * local_trace ((h++lt1)++lt2)))))
    (requires indexed_irred e' (h++lt) /\
      safe arg /\
      indexed_sem_expr_shape TBool arg h)
    (ensures fun (arg', e_r, (| lt1, (| lt2, (lt3, lt4) |) |)) ->
      indexed_irred arg' (h++lt1) /\
      steps arg arg' h lt1 /\
      steps (EWrite arg) (EWrite arg') h lt1 /\
      steps (EWrite arg') e_r (h++lt1) lt2 /\
      (e_r == EInl EUnit \/ e_r == EInr EUnit) /\
      (ETrue? arg' ==>
        (EInl? e_r ==> steps e_r e' ((h++lt1)++lt2) lt3 /\ lt == ((lt1 @ lt2) @ lt3) /\ lt2 == [EvWrite true (Inl ())]) /\
        (EInr? e_r ==> steps e_r e' ((h++lt1)++lt2) lt4 /\ lt == ((lt1 @ lt2) @ lt4) /\ lt2 == [EvWrite true (Inr ())])) /\
      (EFalse? arg' ==>
        (EInl? e_r ==> steps e_r e' ((h++lt1)++lt2) lt3 /\ lt == ((lt1 @ lt2) @ lt3) /\ lt2 == [EvWrite false (Inl ())]) /\
        (EInr? e_r ==> steps e_r e' ((h++lt1)++lt2) lt4 /\ lt == ((lt1 @ lt2) @ lt4) /\ lt2 == [EvWrite false (Inr ())])) /\
      ((lt == (lt1 @ lt2) @ lt3) \/ (lt == (lt1 @ lt2) @ lt4)) /\
      (indexed_irred arg h ==> (lt1 == [] /\ arg == arg')))
    (decreases st) =
    match st with
    | SRefl (EWrite arg) h -> begin
      can_step_ewrite_when_safe arg h;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_ewrite step_ewrite_steps -> begin
      let (EWrite arg) = e in
      match step_ewrite with
      | SWrite #arg #arg' #h #oev step_arg -> begin
        let (EWrite arg') = f2 in
        lem_step_implies_steps arg arg' h oev;
        lem_step_implies_steps (EWrite arg) (EWrite arg') h oev;
        let lt1 : local_trace h = as_lt oev in
        lem_step_preserve_safe arg arg' h oev;
        lem_step_preserve_sem_expr_shape arg arg' h oev TBool;
        let s2 : steps (EWrite arg') e' (h++lt1) lt23 = step_ewrite_steps in
        let (arg'', e_r, (| lt1', (| lt2, (lt3, lt4) |) |)) = destruct_steps_ewrite arg' e' (h++lt1) lt23 s2 in
        lem_steps_transitive arg arg' arg'' h lt1 lt1';
        lem_steps_transitive (EWrite arg) (EWrite arg') (EWrite arg'') h lt1 lt1';
        associative_history #h lt1 lt1' lt2;
        (arg'', e_r, (| (lt1 @ lt1'), (| lt2, (lt3, lt4) |) |))
        end
      | SWriteReturn arg (Inl ()) h -> begin
        let EInl EUnit = f2 in
        lem_step_implies_steps (EWrite arg) (EInl EUnit) h (Some (EvWrite (get_bool arg) (Inl ())));
        lem_value_is_irred arg;
        let lt' : local_trace h = [EvWrite (get_bool arg) (Inl ())] in
        let s2 : steps (EInl EUnit) e' (h++lt') lt23 = step_ewrite_steps in
        lem_value_is_safe EUnit;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einl EUnit e' (h++lt') lt23 s2 TUnit TUnit in
        (arg, f2, (| [], (| lt', (lt12 @ lt_f, []) |) |))
        end
      | SWriteReturn arg (Inr ()) h -> begin
        let EInr EUnit = f2 in
        lem_step_implies_steps (EWrite arg) (EInr EUnit) h (Some (EvWrite (get_bool arg) (Inr ())));
        lem_value_is_irred arg;
        let lt' : local_trace h = [EvWrite (get_bool arg) (Inr ())] in
        let s2 : steps (EInr EUnit) e' (h++lt') lt23 = step_ewrite_steps in
        lem_value_is_safe EUnit;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einr EUnit e' (h++lt') lt23 s2 TUnit TUnit in
        (arg, f2, (| [], (| lt', ([], lt12 @ lt_f) |) |))
        end
      end
*)

// HISTORY INDEPENDENCE PROOFS:
(*
let rec construct_step (#e #e':closed_exp) (#h:history) (#oev:option (event_h h)) (st:step e e' h oev) (h':history) (oev':option (event_h h')) : Pure (step e e' h' oev')
  (requires step e e' h oev /\
            (None? oev ==> None? oev') /\
            ((Some? oev /\ (EvRead? (Some?.v oev) \/ EvWrite? (Some?.v oev))) ==> (oev == oev')) /\
            ((Some? oev /\ ~(EvRead? (Some?.v oev) \/ EvWrite? (Some?.v oev))) ==> (test_event h' (Some?.v oev) ==> (oev == oev'))) /\
            ((Some? oev /\ ~(EvRead? (Some?.v oev) \/ EvWrite? (Some?.v oev))) ==> (~(test_event h' (Some?.v oev)) ==> (None? oev'))))
            // TODO: this is not correct - look at corresponding_event for correct spec
  (ensures fun _ -> step e e' h' oev')
  (decreases st) =
  match st with
  | AppRight e1 hst -> begin
    let hst' = construct_step hst h' oev' in
    AppRight e1 hst'
    end
  | AppLeft e2 hst -> begin
    let hst' = construct_step hst h' oev' in
    AppLeft e2 hst'
    end
  | Beta e11 e2 h -> Beta e11 e2 h'
  | IfCond e2 e3 hst -> begin
    let hst' = construct_step hst h' oev' in
    IfCond e2 e3 hst'
    end
  | IfTrue e2 e3 h -> IfTrue e2 e3 h'
  | IfFalse e2 e3 h -> IfFalse e2 e3 h'
  | PairLeft e2 hst -> begin
    let hst' = construct_step hst h' oev' in
    PairLeft e2 hst'
    end
  | PairRight e1 hst -> begin
    let hst' = construct_step hst h' oev' in
    PairRight e1 hst'
    end
  | FstPair hst -> begin
    let hst' = construct_step hst h' oev' in
    FstPair hst'
    end
  | FstPairReturn #e1 #e2 h -> FstPairReturn #e1 #e2 h'
  | SndPair hst -> begin
    let hst' = construct_step hst h' oev' in
    SndPair hst'
    end
  | SndPairReturn #e1 #e2 h -> SndPairReturn #e1 #e2 h'
  | SCase e2 e3 hst -> begin
    let hst' = construct_step hst h' oev' in
    SCase e2 e3 hst'
    end
  | SInl hst -> begin
    let hst' = construct_step hst h' oev' in
    SInl hst'
    end
  | SInlReturn e1 e2 e3 h -> SInlReturn e1 e2 e3 h'
  | SInr hst -> begin
    let hst' = construct_step hst h' oev' in
    SInr hst'
    end
  | SInrReturn e1 e2 e3 h -> SInrReturn e1 e2 e3 h'
  | SRead b h -> SRead b h'
  | SWrite hst -> begin
    let hst' = construct_step hst h' oev' in
    SWrite hst'
    end
  | SWriteReturn arg r h -> SWriteReturn arg r h'
  | SOpen hst -> begin
    let hst' = construct_step hst h' oev' in
    SOpen hst'
    end
  | SOpenReturnSuccess str h -> SOpenReturnSuccess str h'
  | SOpenReturnFail str h -> SOpenReturnFail str h'
  | SClose hst -> begin
    let hst' = construct_step hst h' oev' in
    SClose hst'
    end
  | SCloseReturn file_descr r h -> SCloseReturn file_descr r h'

let rec construct_option_ev (#e #e':closed_exp) (#h:history) (#oev:option (event_h h)) (st:step e e' h oev) (h':history) : Pure (option (event_h h'))
  (requires step e e' h oev)
  (ensures fun (oev') ->
    (step e e' h' oev') /\
    (None? oev ==> None? oev') /\
    ((Some? oev /\ (EvRead? (Some?.v oev) \/ EvWrite? (Some?.v oev))) ==> (oev == oev')) /\
    ((Some? oev /\ ~(EvRead? (Some?.v oev) \/ EvWrite? (Some?.v oev))) ==> (test_event h' (Some?.v oev) ==> (oev == oev'))) /\
    ((Some? oev /\ ~(EvRead? (Some?.v oev) \/ EvWrite? (Some?.v oev))) ==> (~(test_event h' (Some?.v oev)) ==> (None? oev'))))
  (decreases st) =
  match st with
  | AppRight e1 #e2 #e2' #h #oev2 hst2 -> begin
    let oev2' = construct_option_ev hst2 h' in
    let hst' : step e2 e2' h' oev2' = construct_step hst2 h' oev2' in
    let _ : step e e' h' oev2' = AppRight e1 hst' in
    oev2'
    end
  | AppLeft #e1 e2 #e1' #h #oev1 hst1 -> begin
    let oev1' = construct_option_ev hst1 h' in
    let hst' : step e1 e1' h' oev1' = construct_step hst1 h' oev1' in
    let _ : step e e' h' oev1' = AppLeft e2 hst' in
    oev1'
    end
  | Beta e11 e2 h -> begin
    let _ : step e e' h' None = Beta e11 e2 h' in
    None
    end
  | IfCond #e1 e2 e3 #e1' #h #oev1 hst1 -> begin
    let oev1' = construct_option_ev hst1 h' in
    let hst' : step e1 e1' h' oev1' = construct_step hst1 h' oev1' in
    let _ : step e e' h' oev1' = IfCond e2 e3 hst' in
    oev1'
    end
  | IfTrue e2 e3 h -> begin
    let _ : step e e' h' None = IfTrue e2 e3 h' in
    None
    end
  | IfFalse e2 e3 h -> begin
    let _ : step e e' h' None = IfFalse e2 e3 h' in
    None
    end
  | PairLeft #e1 e2 #e1' #h #oev1 hst1 -> begin
    let oev1' = construct_option_ev hst1 h' in
    let hst' : step e1 e1' h' oev1' = construct_step hst1 h' oev1' in
    let _ : step e e' h' oev1' = PairLeft e2 hst' in
    oev1'
    end
  | PairRight e1 #e2 #e2' #h #oev2 hst2 -> begin
    let oev2' = construct_option_ev hst2 h' in
    let hst' : step e2 e2' h' oev2' = construct_step hst2 h' oev2' in
    let _ : step e e' h' oev2' = PairRight e1 hst' in
    oev2'
    end
  | FstPair #e1 #e1' #h #oev hst -> begin
    let oev' = construct_option_ev hst h' in
    let hst' : step e1 e1' h' oev' = construct_step hst h' oev' in
    let _ : step e e' h' oev' = FstPair hst' in
    oev'
    end
  | FstPairReturn #e1 #e2 h -> begin
    let _ : step e e' h' None = FstPairReturn #e1 #e2 h' in
    None
    end
  | SndPair #e2 #e2' #h #oev hst -> begin
    let oev' = construct_option_ev hst h' in
    let hst' : step e2 e2' h' oev' = construct_step hst h' oev' in
    let _ : step e e' h' oev' = SndPair hst' in
    oev'
    end
  | SndPairReturn #e1 #e2 h -> begin
    let _ : step e e' h' None = SndPairReturn #e1 #e2 h' in
    None
    end
  | SCase #e1 e2 e3 #e1' #h #oev1 hst1 -> begin
    let oev1' = construct_option_ev hst1 h' in
    let hst' : step e1 e1' h' oev1' = construct_step hst1 h' oev1' in
    let _ : step e e' h' oev1' = SCase e2 e3 hst' in
    oev1'
    end
  | SInl #e12 #e12' #h #oev hst -> begin
    let oev' = construct_option_ev hst h' in
    let hst' : step e12 e12' h' oev' = construct_step hst h' oev' in
    let _ : step e e' h' oev' = SInl hst' in
    oev'
    end
  | SInlReturn e1 e2 e3 h -> begin
    let _ : step e e' h' None = SInlReturn e1 e2 e3 h' in
    None
    end
  | SInr #e12 #e12' #h #oev hst -> begin
    let oev' = construct_option_ev hst h' in
    let hst' : step e12 e12' h' oev' = construct_step hst h' oev' in
    let _ : step e e' h' oev' = SInr hst' in
    oev'
    end
  | SInrReturn e1 e2 e3 h -> begin
    let _ : step e e' h' None = SInrReturn e1 e2 e3 h' in
    None
    end
  | SRead b h -> begin
    let _ : step e e' h' (Some (EvRead () b)) = SRead b h' in
    Some (EvRead () b)
    end
  | SWrite #arg #arg' #h #oev hst -> begin
    let oev' = construct_option_ev hst h' in
    let hst' : step arg arg' h' oev' = construct_step hst h' oev' in
    let _ : step e e' h' oev' = SWrite hst' in
    oev'
    end
  | SWriteReturn arg r h -> begin
    let _ : step e e' h' (Some (EvWrite (get_bool arg) r)) = SWriteReturn arg r h' in
    Some (EvWrite (get_bool arg) r)
    end
  | SOpen #str #str' #h #oev hst -> begin
    let oev' = construct_option_ev hst h' in
    let hst' : step str str' h' oev' = construct_step hst h' oev' in
    let _ : step e e' h' oev' = SOpen hst' in
    oev'
    end
  | SOpenReturnSuccess str h -> begin
    let _ : step e e' h' (Some (EvOpen (get_bool str) (Inl (fresh_fd h)))) = SOpenReturnSuccess str h' in
    (Some (EvOpen (get_bool str) (Inl (fresh_fd h))))
    end
  | SOpenReturnFail str h -> begin
    let _ : step e e' h' (Some (EvOpen (get_bool str) (Inr ()))) = SOpenReturnFail str h' in
    (Some (EvOpen (get_bool str) (Inr ())))
    end
  | SClose #fd #fd' #h #oev hst -> begin
    let oev' = construct_option_ev hst h' in
    let hst' : step fd fd' h' oev' = construct_step hst h' oev' in
    let _ : step e e' h' oev' = SClose hst' in
    oev'
    end
  | SCloseReturn file_descr r h -> begin
    let _ : step e e' h' (Some (EvClose file_descr r)) = SCloseReturn file_descr r h' in
    Some (EvClose file_descr r)
    end

let step_history_independence (#e #e':closed_exp) (#h:history) (#oev:option (event_h h)) (st:step e e' h oev) :
  Lemma (ensures forall h'. exists oev'. step e e' h' oev' /\ (None? oev <==> None? oev')) =
  introduce forall h'. exists oev'. step e e' h' oev' /\ (None? oev <==> None? oev') with begin
    assert (step e e' h' (construct_option_ev st h'))
  end

let rec construct_local_trace (#e #e':closed_exp) (#h:history) (#lt:local_trace h) (st:steps e e' h lt) (h':history) : Pure (local_trace h')
  (requires steps e e' h lt)
  (ensures fun lt' ->
    steps e e' h' lt' /\
    (lt == [] <==> lt' == []))
  (decreases st) =
  match st with
  | SRefl _ _ -> []
  | STrans #e #e_i #e' #h #oev #_ e_step steps_to_e' -> begin
    step_history_independence e_step;
    let oev' = construct_option_ev e_step h' in
    assert (oev == oev');
    lem_step_implies_steps e e_i h' oev';
    let lt_ = as_lt oev' in
    let rest_of_trace = construct_local_trace steps_to_e' (h'++lt_) in
    lem_steps_transitive e e_i e' h' lt_ rest_of_trace;
    match oev' with
    | Some ev' -> [ev'] @ rest_of_trace
    | None -> rest_of_trace
    end

let steps_history_independence (#e #e':closed_exp) (#h:history) (#lt:local_trace h) (sts:steps e e' h lt) :
  Lemma (ensures forall h'. exists lt'. steps e e' h' lt' /\ (lt == [] <==> lt' == [])) =
  introduce forall h'. exists lt'. steps e e' h' lt' /\ (lt == [] <==> lt' == []) with begin
    assert (steps e e' h' (construct_local_trace sts h'))
 end

let indexed_can_step_history_independence (e:closed_exp) (h:history) :
  Lemma (requires indexed_can_step e h)
        (ensures forall h'. indexed_can_step e h') =
  introduce forall h'. exists (e':closed_exp) (oev:option (event_h h')). step e e' h' oev with begin
    eliminate exists e' oev. step e e' h oev
    returns exists e' oev. step e e' h' oev with _. begin
      bind_squash #(step e e' h oev) () (fun st ->
        assert (step e e' h' (construct_option_ev st h'))
      )
    end
  end

let lem_step_preserve_safe (e e':closed_exp) (h:history) (oev:option (event_h h)) :
  Lemma (requires safe e /\ step e e' h oev)
        (ensures safe e') =
  introduce forall e'' h' lt'. steps e' e'' h' lt' ==> (is_value e'' \/ indexed_can_step e'' (h'++lt')) with begin
    introduce steps e' e'' h' lt' ==> (is_value e'' \/ indexed_can_step e'' (h'++lt')) with _. begin
      bind_squash #(steps e' e'' h' lt') () (fun sts ->
      steps_history_independence sts;
      assert (forall h_. exists lt_. steps e' e'' h_ lt_);
      let lt_ev = as_lt oev in
      eliminate forall h_. exists lt_. steps e' e'' h_ lt_ with (h++lt_ev);
      assert (exists lt_. steps e' e'' (h++lt_ev) lt_);
      eliminate exists lt_. steps e' e'' (h++lt_ev) lt_
      returns is_value e'' \/ indexed_can_step e'' (h'++lt') with _. begin
        lem_step_implies_steps e e' h oev;
        assert (steps e e' h lt_ev);
        lem_steps_transitive e e' e'' h lt_ev lt_;
        eliminate forall e' h lt. steps e e' h lt ==> (is_value e' \/ indexed_can_step e' (h++lt)) with e'' h (lt_ev @ lt_);
        introduce indexed_can_step e'' (h++(lt_ev @ lt_)) ==> indexed_can_step e'' (h'++lt') with _. begin
          indexed_can_step_history_independence e'' (h++(lt_ev @ lt_))
        end
      end)
    end
  end

let indexed_irred_history_independence (e:closed_exp) (h:history) :
  Lemma (requires indexed_irred e h)
        (ensures forall h'. indexed_irred e h') =
  introduce forall (h':history) (e':closed_exp) (oev':option (event_h h')). step e e' h' oev' ==> False with begin
    introduce step e e' h' oev' ==> False with _. begin
      bind_squash #(step e e' h' oev') () (fun st ->
      step_history_independence st;
      eliminate forall h_. exists oev_. step e e' h_ oev_ with h;
      eliminate exists oev_. step e e' h oev_
      returns False with _. begin
        eliminate forall e_ oev_. step e e_ h oev_ ==> False with e' oev_
      end)
    end
  end

let sem_expr_shape_history_independence (e:closed_exp) (h:history) (t:typ) :
  Lemma (requires indexed_sem_expr_shape t e h)
        (ensures forall h'. indexed_sem_expr_shape t e h') =
  introduce forall (h':history) (e':closed_exp) (lt':local_trace h'). steps e e' h' lt' /\ indexed_irred e' (h'++lt') ==> sem_value_shape t e' with begin
    introduce steps e e' h' lt' /\ indexed_irred e' (h'++lt') ==> sem_value_shape t e' with _. begin
      bind_squash #(steps e e' h' lt') () (fun sts ->
      steps_history_independence sts;
      eliminate forall h_. exists lt_. steps e e' h_ lt_ with h;
      eliminate exists lt_. steps e e' h lt_
      returns sem_value_shape t e' with _. begin
        eliminate forall e_ (lt_:local_trace h). steps e e_ h lt_ /\ indexed_irred e_ (h++lt_) ==> sem_value_shape t e_ with e' lt_;
        assert (steps e e' h lt_ /\ indexed_irred e' (h++lt_) ==> sem_value_shape t e');
        indexed_irred_history_independence e' (h'++lt')
      end)
    end
  end

let lem_step_preserve_sem_expr_shape (e e':closed_exp) (h:history) (oev:option (event_h h)) (t:typ) :
  Lemma
    (requires indexed_sem_expr_shape t e h /\ step e e' h oev)
    (ensures indexed_sem_expr_shape t e' (h++(as_lt oev))) =
  introduce forall e'' lt'. steps e' e'' (h++(as_lt oev)) lt' /\ indexed_irred e'' ((h++(as_lt oev))++lt') ==> sem_value_shape t e'' with begin
    introduce _  ==> sem_value_shape t e'' with _. begin
      bind_squash #(steps e' e'' (h++(as_lt oev)) lt') () (fun sts ->
      steps_history_independence sts;
      let lt_ev = as_lt oev in
      eliminate forall h_. exists lt_. steps e' e'' h_ lt_ with (h++lt_ev);
      eliminate exists lt_. steps e' e'' (h++lt_ev) lt_
      returns sem_value_shape t e'' with _. begin
        lem_step_implies_steps e e' h oev;
        lem_steps_transitive e e' e'' h lt_ev lt_;
        eliminate forall e' lt. steps e e' h lt /\ indexed_irred e' (h++lt) ==> sem_value_shape t e' with e'' (lt_ev @ lt_);
        indexed_irred_history_independence e'' ((h++(as_lt oev))++lt')
      end)
    end
  end

let indexed_irred_history_independence (e:closed_exp) (h:history) :
  Lemma (requires indexed_irred e h)
        (ensures forall h'. indexed_irred e h') =
  introduce forall (h':history) (e':closed_exp) (oev':option (event_h h')). step e e' h' oev' ==> False with begin
    introduce step e e' h' oev' ==> False with _. begin
      bind_squash #(step e e' h' oev') () (fun st ->
      step_history_independence st;
      eliminate forall h_. exists oev_. step e e' h_ oev_ with h;
      eliminate exists oev_. step e e' h oev_
      returns False with _. begin
        eliminate forall e_ oev_. step e e_ h oev_ ==> False with e' oev_
      end)
    end
  end

let sem_expr_shape_history_independence (e:closed_exp) (h:history) (t:typ) :
  Lemma (requires indexed_sem_expr_shape t e h)
        (ensures forall h'. indexed_sem_expr_shape t e h') =
  introduce forall (h':history) (e':closed_exp) (lt':local_trace h'). steps e e' h' lt' /\ indexed_irred e' (h'++lt') ==> sem_value_shape t e' with begin
    introduce steps e e' h' lt' /\ indexed_irred e' (h'++lt') ==> sem_value_shape t e' with _. begin
      bind_squash #(steps e e' h' lt') () (fun sts ->
      steps_history_independence sts;
      eliminate forall h_. exists lt_. steps e e' h_ lt_ with h;
      eliminate exists lt_. steps e e' h lt_
      returns sem_value_shape t e' with _. begin
        eliminate forall e_ (lt_:local_trace h). steps e e_ h lt_ /\ indexed_irred e_ (h++lt_) ==> sem_value_shape t e_ with e' lt_;
        assert (steps e e' h lt_ /\ indexed_irred e' (h++lt_) ==> sem_value_shape t e');
        indexed_irred_history_independence e' (h'++lt')
      end)
    end
  end
  *)
