(* Substitution proof from: https://fstar-lang.org/tutorial/book/part2/part2_stlc.html *)

module STLC

open FStar.Tactics
open FStar.Classical.Sugar
open Trace

type typ =
  | TUnit  : typ
  | TBool  : typ
  | TFileDescr : typ
  | TString : typ
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
  | EFileDescr : fd:file_descr -> exp
  | EString : s:string -> exp
  | ERead  : exp -> exp
  | EWrite : exp -> exp -> exp
  | EOpen  : exp -> exp
  | EClose : exp -> exp

(* Parallel substitution operation `subst` *)
let sub (renaming:bool) =
    f:(var -> exp){ renaming ==> (forall x. EVar? (f x)) }

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
    | EString s' -> EString s'
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

let rec equiv_subs_implies_equiv_substs #b #b' (f:sub b) (g:sub b') (e:exp) : Lemma
    (requires (forall x. f x == g x))
    (ensures subst f e == subst g e)
    (decreases e) =
  match e with
  | EUnit
  | ETrue
  | EFalse
  | EVar _
  | EFileDescr _
  | EString _ -> ()
  | ELam e1 -> equiv_subs_implies_equiv_substs (sub_elam f) (sub_elam g) e1
  | EFst e1
  | ESnd e1
  | EInl e1
  | EInr e1
  | ERead e1
  | EOpen e1
  | EClose e1 -> equiv_subs_implies_equiv_substs f g e1
  | EApp e1 e2
  | EWrite e1 e2
  | EPair e1 e2 -> begin
    equiv_subs_implies_equiv_substs f g e1;
    equiv_subs_implies_equiv_substs f g e2
    end
  | EIf e1 e2 e3 -> begin
    equiv_subs_implies_equiv_substs f g e1;
    equiv_subs_implies_equiv_substs f g e2;
    equiv_subs_implies_equiv_substs f g e3
    end
  | ECase e1 e2 e3 -> begin
    equiv_subs_implies_equiv_substs f g e1;
    equiv_subs_implies_equiv_substs (sub_elam f) (sub_elam g) e2;
    equiv_subs_implies_equiv_substs (sub_elam f) (sub_elam g) e3
    end

module L = FStar.List.Tot

let rec free_vars_indx (e:exp) (n:nat) : list var = // n is the number of binders
  match e with
  | EUnit -> []
  | ETrue -> []
  | EFalse -> []
  | ELam e' -> free_vars_indx e' (n+1)
  | EApp e1 e2 -> free_vars_indx e1 n `L.append` free_vars_indx e2 n
  | EIf e1 e2 e3 -> free_vars_indx e1 n `L.append` free_vars_indx e2 n `L.append` free_vars_indx e3 n
  | EVar i -> if i < n then [] else [i-n]
  | EPair e1 e2 -> free_vars_indx e1 n `L.append` free_vars_indx e2 n
  | EFst e' -> free_vars_indx e' n
  | ESnd e' -> free_vars_indx e' n
  | EInl e' -> free_vars_indx e' n
  | EInr e' -> free_vars_indx e' n
  | ECase e1 e2 e3 -> free_vars_indx e1 n `L.append` free_vars_indx e2 (n+1) `L.append` free_vars_indx e3 (n+1)
  | ERead e' -> free_vars_indx e' n
  | EWrite e1 e2 -> free_vars_indx e1 n `L.append` free_vars_indx e2 n
  | EFileDescr i -> []
  | EString _ -> []
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
  | EString _ -> True
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
    lem_shifting_preserves_closed (sub_elam s) e2 (n+1);
    lem_shifting_preserves_closed (sub_elam s) e3 (n+1)
  | _ -> ()

let lemma_memP_append (l1 l2:list var) :
  Lemma ((forall x. x `L.memP` l1 ==> x `L.memP` (l1 `L.append` l2)) /\
         (forall x. x `L.memP` l2 ==> x `L.memP` (l1 `L.append` l2))) =
  introduce forall (x:var).
    (x `L.memP` l1 ==> x `L.memP` (l1 `L.append` l2)) /\
    (x `L.memP` l2 ==> x `L.memP` (l1 `L.append` l2))
  with L.append_memP l1 l2 x

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
      (forall fv. fv `L.memP` free_vars_indx e n ==>
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
    lemma_memP_append (free_vars_indx e1 n) (free_vars_indx e2 n);
    lem_subst_freevars_closes_exp s e1 n;
    lem_subst_freevars_closes_exp s e2 n
  | EIf e1 e2 e3 ->
    lemma_memP_append (free_vars_indx e1 n) (free_vars_indx e2 n);
    lemma_memP_append (free_vars_indx e1 n `L.append` free_vars_indx e2 n) (free_vars_indx e3 n);
    lem_subst_freevars_closes_exp s e1 n;
    lem_subst_freevars_closes_exp s e2 n;
    lem_subst_freevars_closes_exp s e3 n
  | EFst e'
  | ESnd e'
  | EInl e'
  | EInr e'
  | EClose e'
  | EOpen e'
  | ERead e' ->
    lem_subst_freevars_closes_exp s e' n
  | ECase e1 e2 e3 -> begin
    let s' = sub_elam s in
    let n' = n+1 in
    lemma_memP_append (free_vars_indx e1 n) (free_vars_indx e2 n');
    lemma_memP_append (free_vars_indx e1 n `L.append` free_vars_indx e2 n') (free_vars_indx e3 n');
    lem_subst_freevars_closes_exp s e1 n;
    introduce forall x. free_vars_indx (s x) n == [] ==> free_vars_indx (s' (x+1)) n' == [] with begin
      introduce _ ==> _ with _. begin
        assert (free_vars_indx (s x) n == []);
        lem_shifting_preserves_closed (sub_inc) (s x) n;
        assert (free_vars_indx (subst sub_inc (s x)) n' == [])
      end
    end;
    lem_subst_freevars_closes_exp s' e2 n';
    lem_subst_freevars_closes_exp s' e3 n'
  end
  | _ -> ()
#pop-options

let subst_beta (v e:exp) :
  Pure closed_exp
    (requires (is_closed (ELam e)) /\ is_closed v)
    (ensures (fun _ -> True)) =
  // assume (free_vars_indx e 0 == [0]); (** should be provable **)
  assume (forall x. x `L.memP` free_vars_indx e 0 ==> x == 0);
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

let get_string (e:value{EString? e}) : string = EString?.s e

let get_fd (e:closed_exp{EFileDescr? e}) : file_descr =
  let EFileDescr fd = e in
  fd

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

let get_resexn_string (x:resexn string) : closed_exp =
  match x with
  | Inl s -> EInl (EString s)
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
    e1:closed_exp{ELam? e1 /\ is_closed e1} ->
    #e2:closed_exp ->
    #e2':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step e2 e2' h oev ->
    step (EApp e1 e2) (EApp e1 e2') h oev
  | AppLeft :
    #e1:closed_exp ->
    e2:closed_exp -> (** e2 being a value makes the semantics to be call by value. TODO: funny one cannot use [value] directly **)
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
    r:resexn string ->
    step (ERead (get_efd fd)) (get_resexn_string r) h (Some (EvRead fd r))
  | SWriteArg :
    #arg:closed_exp ->
    #arg':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    fd:closed_exp{EFileDescr? fd} ->
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
    arg:value{EString? arg} ->
    r:resexn unit ->
    step (EWrite (get_efd fd) arg) (get_resexn_unit r) h (Some (EvWrite (fd, get_string arg) r))
  | SOpen :
    #str:closed_exp ->
    #str':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step str str' h oev ->
    step (EOpen str) (EOpen str') h oev
  | SOpenReturnSuccess :
    str:value{EString? str} ->
    h:history ->
    step (EOpen str) (get_resexn_fd (Inl (fresh_fd h))) h (Some (EvOpen (get_string str) (Inl (fresh_fd h))))
  | SOpenReturnFail :
    str:value{EString? str} ->
    h:history ->
    step (EOpen str) (EInr EUnit) h (Some (EvOpen (get_string str) (Inr ())))
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
           steps e1 e3 h ((as_lt oev) @ lt)

let rec lem_steps_transitive_constructive
  (#e1 #e2 #e3:closed_exp)
  (#h:history)
  (#lt1:local_trace h) (#lt2:local_trace (h++lt1))
  (st12:steps e1 e2 h lt1)
  (st23:steps e2 e3 (h++lt1) lt2)
  : Tot (steps e1 e3 h (lt1 @ lt2)) (decreases st12)
  = match st12 with
    | SRefl _ _ -> st23
    | STrans #e1 #e1' #e2 #h #oev1 #lt1' e1_can_step st12' ->
      trans_history h (as_lt oev1) lt1';
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
      trans_history h (as_lt oev) lt';
      ()
    end
  end

let lem_irred_implies_srefl_steps (#e #e':closed_exp) (#h:history) (#lt:local_trace h) (sts:steps e e' h lt) :
  Lemma (requires indexed_irred e h)
        (ensures e == e' /\ lt == []) =
  match sts with
  | SRefl e h -> ()
  | STrans _ _ -> false_elim ()

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

let get_epair_e1 (x:closed_exp{EPair? x}) =
  match x with
  | EPair e1 e2 -> e1

let get_epair_e2 (x:closed_exp{EPair? x}) =
  match x with
  | EPair e1 e2 -> e2

(* We need syntactic types for this, or at least the top-level shape of types *)
let sem_value_shape (t:typ) (e:closed_exp) : Tot Type0 =
  match t with
  | TUnit -> e == EUnit
  | TBool -> e == ETrue \/ e == EFalse
  | TFileDescr -> EFileDescr? e
  | TString -> EString? e
  | TArr t1 t2 -> ELam? e /\ is_closed e
  | TPair t1 t2 -> EPair? e /\ is_value (get_epair_e1 e) /\ is_value (get_epair_e2 e)
  | TSum t1 t2 -> (EInl? e /\ is_value (get_einl_v e)) \/ (EInr? e /\ is_value (get_einr_v e))

let indexed_sem_expr_shape (t:typ) (e:closed_exp) (h:history) : Tot Type0 =
  forall (e':closed_exp) (lt:local_trace h). steps e e' h lt /\ indexed_irred e' (h++lt) ==> sem_value_shape t e'

let lem_value_preserves_value (e:closed_exp) (h:history) (t:typ) :
  Lemma (requires is_value e /\ sem_value_shape t e)
        (ensures indexed_sem_expr_shape t e h) =
  introduce forall e' lt. steps e e' h lt /\ indexed_irred e' (h++lt) ==> sem_value_shape t e' with begin
    introduce _ ==> _ with _. begin
      lem_value_is_irred e;
      FStar.Squash.bind_squash #(steps e e' h lt) () (fun sts ->
      lem_irred_implies_srefl_steps sts)
    end
  end

let lem_step_preserve_indexed_sem_expr_shape (e e':closed_exp) (h:history) (oev:option (event_h h)) (t:typ) :
  Lemma
    (requires indexed_sem_expr_shape t e h /\ step e e' h oev)
    (ensures indexed_sem_expr_shape t e' (h++(as_lt oev))) =
  introduce forall e'' lt'. steps e' e'' (h++(as_lt oev)) lt' /\ indexed_irred e'' ((h++(as_lt oev))++lt') ==> sem_value_shape t e'' with begin
    introduce _  ==> sem_value_shape t e'' with _. begin
      lem_step_implies_steps e e' h oev;
      lem_steps_transitive e e' e'' h (as_lt oev) lt';
      trans_history h (as_lt oev) lt'
    end
  end

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
      indexed_sem_expr_shape (TPair t1 t2) e12 h) (** CA: not sure if necessary **)
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

let lem_destruct_steps_epair_fst
  (e1 e2:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h) :
  Lemma (requires (steps (EFst (EPair e1 e2)) e' h lt /\ indexed_irred e1 h /\ indexed_irred e2 h))
        (ensures (e1 == e') /\ lt == []) = admit ()

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

let lem_destruct_steps_epair_snd
  (e1 e2:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h) :
  Lemma (requires (steps (ESnd (EPair e1 e2)) e' h lt /\ indexed_irred e1 h /\ indexed_irred e2 h))
        (ensures (e2 == e') /\ lt == []) = admit ()

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

#push-options "--z3rlimit 10000"
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

let can_step_eread_fd (fd:closed_exp{EFileDescr? fd}) (h:history) :
  Lemma (exists e' oev. step (ERead fd) e' h oev)
  =
  let st1 : step (ERead fd) (EInl (EString "")) h (Some (EvRead (get_fd fd) (Inl ""))) = SReadReturn h (get_fd fd) (Inl "") in
  let st2 : step (ERead fd) (EInr EUnit) h (Some (EvRead (get_fd fd) (Inr ()))) = SReadReturn h (get_fd fd) (Inr ()) in
  ()

let can_step_eread (fd:closed_exp) (h:history) :
  Lemma
  (requires indexed_sem_expr_shape TFileDescr fd h)
  (ensures (exists e' oev. step (ERead fd) e' h oev))
  =
  introduce indexed_irred fd h ==> (exists e' oev. step (ERead fd) e' h oev) with _. begin
    assert (steps fd fd h []);
    let st1 : step (ERead fd) (EInl (EString "")) h (Some (EvRead (get_fd fd) (Inl ""))) = SReadReturn h (get_fd fd) (Inl "") in
    let st2 : step (ERead fd) (EInr EUnit) h (Some (EvRead (get_fd fd) (Inr ()))) = SReadReturn h (get_fd fd) (Inr ()) in
  ()
  end;

  introduce ~(indexed_irred fd h) ==> (exists e' oev. step (ERead fd) e' h oev) with _. begin
    assert (exists fd' oev'. step fd fd' h oev');
    eliminate exists fd' oev'. step fd fd' h oev' returns exists e' oev. step (ERead fd) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (SRead st))
    end
  end

let rec destruct_steps_eread_fd
  (fd:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (ERead fd) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
  (requires indexed_irred e' (h++lt) /\
    indexed_sem_expr_shape TFileDescr fd h)
  (ensures fun (fd', (| lt1, lt' |)) ->
    EFileDescr? fd' /\
    steps fd fd' h lt1 /\
    steps (ERead fd) (ERead fd') h lt1 /\
    steps (ERead fd') e' (h++lt1) lt' /\
    (lt == (lt1 @ lt')))
  (decreases st) =
  match st with
  | SRefl (ERead fd) h -> begin
    can_step_eread fd h;
    false_elim ()
    end
  | STrans #e #f2 #e' #h #_ #lt23 step_eread step_eread_steps -> begin
    let (ERead fd) = e in
    match step_eread with
    | SRead #fd #fd' #h #oev step_fd -> begin
      let (ERead fd') = f2 in
      lem_step_implies_steps fd fd' h oev;
      lem_step_implies_steps (ERead fd) (ERead fd') h oev;
      let lt1 : local_trace h = as_lt oev in
      let s2 : steps (ERead fd') e' (h++lt1) lt23 = step_eread_steps in
      trans_history h lt1 lt23;
      lem_step_preserve_indexed_sem_expr_shape fd fd' h oev TFileDescr;
      let (fd'', (| lt1', lt' |)) = destruct_steps_eread_fd fd' e' (h++lt1) lt23 s2 in
      trans_history h lt1 lt1';
      lem_steps_transitive fd fd' fd'' h lt1 lt1';
      lem_steps_transitive (ERead fd) (ERead fd') (ERead fd'') h lt1 lt1';
      (fd'', (| (lt1 @ lt1'), lt' |))
      end
    | _ -> (fd, (| [], lt |))
    end

#push-options "--z3rlimit 10000"
let destruct_steps_eread
  (fd:closed_exp{EFileDescr? fd})
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (ERead fd) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt))
    (ensures fun (e_r, (| lt1, lt2 |)) ->
       steps (ERead fd) e_r h lt1 /\
       (EInl? e_r /\ EString? (get_einl_v e_r) \/ e_r == EInr EUnit) /\
       (EInl? e_r ==>
         (EString? (get_einl_v e_r) ==>
           (steps e_r e' (h++lt1) lt2 /\ lt == (lt1 @ lt2) /\
            lt1 == [EvRead (get_fd fd) (Inl (get_string (get_einl_v e_r)))]))) /\
       (EInr? e_r ==> steps e_r e' (h++lt1) lt2 /\ lt == (lt1 @ lt2) /\ lt1 == [EvRead (get_fd fd) (Inr ())]) /\
       (lt == (lt1 @ lt2)))
    (decreases st) =
    match st with
    | SRefl (ERead fd) h -> begin
      can_step_eread_fd fd h;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_eread step_eread_steps -> begin
      let ERead fd = e in
      match step_eread with
      | SReadReturn h fd (Inl s) -> begin
        let EInl (EString _) = f2 in
        lem_step_implies_steps (ERead (get_efd fd)) (EInl (EString s)) h (Some (EvRead fd (Inl s)));
        let lt' : local_trace h = [EvRead fd (Inl s)] in
        let s2 : steps (EInl (EString s)) e' (h++lt') lt23 = step_eread_steps in
        trans_history h lt' lt23;
        lem_value_preserves_value (EString s) (h++lt') TString;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einl (EString s) e' (h++lt') lt23 s2 in
        (f2, (| lt', lt12 @ lt_f |))
        end
      | SReadReturn h fd (Inr ()) -> begin
        let EInr EUnit = f2 in
        lem_step_implies_steps (ERead (get_efd fd)) (EInr EUnit) h (Some (EvRead fd (Inr ())));
        let lt' : local_trace h = ev_lt (EvRead fd (Inr ())) in
        let s2 : steps (EInr EUnit) e' (h++lt') lt23 = step_eread_steps in
        trans_history h lt' lt23;
        lem_value_preserves_value EUnit (h++lt') TUnit;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einr EUnit e' (h++lt') lt23 s2 in
        (f2, (| lt', lt12 @ lt_f |))
        end
      end
#pop-options

let can_step_ewrite_when_fd_arg_value (fd:value{EFileDescr? fd}) (arg:value{EString? arg}) (h:history) :
  Lemma (ensures (exists e' oev. step (EWrite fd arg) e' h oev))
  =
  let _ : step (EWrite fd arg) (EInl EUnit) h (Some (EvWrite (get_fd fd, get_string arg) (Inl ()))) = SWriteReturn h (get_fd fd) arg (Inl ()) in
  ()

let lem_irred_ewrite_implies_irred_fd (fd arg:closed_exp) (h:history) :
  Lemma (requires indexed_irred (EWrite fd arg) h)
        (ensures indexed_irred fd h) =
  introduce forall fd' oev. step fd fd' h oev ==> False with begin
    introduce _ ==> _ with _. begin
      bind_squash #(step fd fd' h oev) () (fun st ->
      let _ : step (EWrite fd arg) (EWrite fd' arg) h oev = SWriteFd arg st in ())
    end
  end

let lem_irred_ewrite_implies_irred_arg (fd:closed_exp{EFileDescr? fd})  (arg:closed_exp) (h:history) :
  Lemma (requires indexed_irred (EWrite fd arg) h)
        (ensures indexed_irred arg h) =
  introduce forall arg' oev. step arg arg' h oev ==> False with begin
    introduce _ ==> _ with _. begin
      bind_squash #(step arg arg' h oev) () (fun st ->
      let _ : step (EWrite fd arg) (EWrite fd arg') h oev = SWriteArg fd st in ())
    end
  end

let rec destruct_steps_ewrite_fd
  (fd:closed_exp)
  (arg:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EWrite fd arg) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt) /\
      indexed_sem_expr_shape TFileDescr fd h)
    (ensures fun (fd', (| lt1, lt' |)) ->
      EFileDescr? fd' /\
      steps fd fd' h lt1 /\
      steps (EWrite fd arg) (EWrite fd' arg) h lt1 /\
      steps (EWrite fd' arg) e' (h++lt1) lt' /\
      (lt == (lt1 @ lt')))
    (decreases st) =
  match st with
  | SRefl (EWrite fd arg) h -> begin
    lem_irred_ewrite_implies_irred_fd fd arg h;
    (fd, (| [], lt |))
  end
  | STrans #e #f2 #e' #h #_ #lt23 step_ewrite step_ewrite_steps -> begin
    let (EWrite fd arg) = e in
    match step_ewrite with
    | SWriteFd #fd #fd' #h #oev arg step_fd -> begin
      let (EWrite fd' arg) = f2 in
      lem_step_implies_steps fd fd' h oev;
      lem_step_implies_steps (EWrite fd arg) (EWrite fd' arg) h oev;
      let lt1 : local_trace h = as_lt oev in
      let s2 : steps (EWrite fd' arg) e' (h++lt1) lt23 = step_ewrite_steps in
      trans_history h lt1 lt23;
      lem_step_preserve_indexed_sem_expr_shape fd fd' h oev TFileDescr;
      let (fd'', (| lt1', lt' |)) = destruct_steps_ewrite_fd fd' arg e' (h++lt1) lt23 s2 in
      trans_history h lt1 lt1';
      lem_steps_transitive fd fd' fd'' h lt1 lt1';
      lem_steps_transitive (EWrite fd arg) (EWrite fd' arg) (EWrite fd'' arg) h lt1 lt1';
      (fd'', (| (lt1 @ lt1'), lt' |))
      end
    | _ -> (fd, (| [], lt |))
    end

let rec destruct_steps_ewrite_arg
  (fd':closed_exp{EFileDescr? fd'})
  (arg:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EWrite fd' arg) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt) /\
      indexed_sem_expr_shape TString arg h)
    (ensures fun (arg', (| lt1, lt' |)) ->
      EString? arg' /\
      steps arg arg' h lt1 /\
      steps (EWrite fd' arg) (EWrite fd' arg') h lt1 /\
      steps (EWrite fd' arg') e' (h++lt1) lt' /\
      (lt == (lt1 @ lt')))
    (decreases st) =
  match st with
  | SRefl (EWrite fd' arg) h -> begin
    lem_irred_ewrite_implies_irred_arg fd' arg h;
    (arg, (| [], lt |))
    end
  | STrans #e #f2 #e' #h #_ #lt23 step_ewrite step_ewrite_steps -> begin
    let (EWrite fd' arg) = e in
    match step_ewrite with
    | SWriteArg #arg #arg' #h #oev fd' step_arg -> begin
      let (EWrite fd' arg') = f2 in
      lem_step_implies_steps arg arg' h oev;
      lem_step_implies_steps (EWrite fd' arg) (EWrite fd' arg') h oev;
      let lt1 : local_trace h = as_lt oev in
      let s2 : steps (EWrite fd' arg') e' (h++lt1) lt23 = step_ewrite_steps in
      trans_history h lt1 lt23;
      lem_step_preserve_indexed_sem_expr_shape arg arg' h oev TString;
      let (arg'', (| lt1', lt' |)) = destruct_steps_ewrite_arg fd' arg' e' (h++lt1) lt23 s2 in
      trans_history h lt1 lt1';
      lem_steps_transitive arg arg' arg'' h lt1 lt1';
      lem_steps_transitive (EWrite fd' arg) (EWrite fd' arg') (EWrite fd' arg'') h lt1 lt1';
      (arg'', (| (lt1 @ lt1'), lt' |))
      end
    | SWriteFd _ _ -> (arg, (| [], lt |))
    | SWriteReturn _ _ _ _ -> (arg, (| [], lt |))
    end

#push-options "--z3rlimit 10000"
let destruct_steps_ewrite
  (fd':closed_exp{EFileDescr? fd'})
  (arg':closed_exp{EString? arg'})
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EWrite fd' arg') e' h lt) :
  Pure (closed_exp * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt))
    (ensures fun (e_r, (| lt1, lt2 |)) ->
      steps (EWrite fd' arg') e_r h lt1 /\
      (e_r == EInl EUnit \/ e_r == EInr EUnit) /\
      (EString? arg' ==>
        (EInl? e_r ==> steps e_r e' (h++lt1) lt2 /\ lt == (lt1 @ lt2) /\ lt1 == [EvWrite (get_fd fd', get_string arg') (Inl ())]) /\
        (EInr? e_r ==> steps e_r e' (h++lt1) lt2 /\ lt == (lt1 @ lt2) /\ lt1 == [EvWrite (get_fd fd', get_string arg') (Inr ())])) /\
      (lt == (lt1 @ lt2) \/ lt == (lt1 @ lt2)))
    (decreases st) =
    match st with
    | SRefl (EWrite fd' arg') h -> begin
      can_step_ewrite_when_fd_arg_value fd' arg' h;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_ewrite step_ewrite_steps -> begin
      let (EWrite fd' arg') = e in
      match step_ewrite with
      | SWriteReturn h fd_t arg' (Inl ()) -> begin
        let EInl EUnit = f2 in
        lem_step_implies_steps (EWrite (get_efd fd_t) arg') (EInl EUnit) h (Some (EvWrite (fd_t, get_string arg') (Inl ())));
        lem_value_is_irred arg';
        let lt' : local_trace h = [EvWrite (fd_t, get_string arg') (Inl ())] in
        let s2 : steps (EInl EUnit) e' (h++lt') lt23 = step_ewrite_steps in
        trans_history h lt' lt23;
        lem_value_preserves_value EUnit (h++lt') TUnit;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einl EUnit e' (h++lt') lt23 s2 in
        (f2, (| lt', (lt12 @ lt_f) |))
        end
      | SWriteReturn h fd_t arg' (Inr ()) -> begin
        let EInr EUnit = f2 in
        lem_step_implies_steps (EWrite (get_efd fd_t) arg') (EInr EUnit) h (Some (EvWrite (fd_t, get_string arg') (Inr ())));
        lem_value_is_irred arg';
        let lt' : local_trace h = [EvWrite (fd_t, get_string arg') (Inr ())] in
        let s2 : steps (EInr EUnit) e' (h++lt') lt23 = step_ewrite_steps in
        trans_history h lt' lt23;
        lem_value_preserves_value EUnit (h++lt') TUnit;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einr EUnit e' (h++lt') lt23 s2 in
        (f2, (| lt', (lt12 @ lt_f) |))
        end
      | SWriteArg _ _ -> false_elim ()
      | SWriteFd _ _ -> false_elim ()
      end
#pop-options

let can_step_eopen_str (str:closed_exp{EString? str}) (h:history) :
  Lemma (exists e' oev. step (EOpen str) e' h oev)
  =
  let st1 : step (EOpen str) (EInl (get_efd (fresh_fd h))) h (Some (EvOpen (get_string str) (Inl (fresh_fd h)))) = SOpenReturnSuccess str h in
  let st2 : step (EOpen str) (EInr EUnit) h (Some (EvOpen (get_string str) (Inr ()))) = SOpenReturnFail str h in
  ()

let can_step_eopen (str:closed_exp) (h:history) :
  Lemma
  (requires indexed_sem_expr_shape TString str h)
  (ensures (exists e' oev. step (EOpen str) e' h oev))
  =
  introduce indexed_irred str h ==> (exists e' oev. step (EOpen str) e' h oev) with _. begin
    assert (steps str str h []);
    let _ : step (EOpen str) (EInl (get_efd (fresh_fd h))) h (Some (EvOpen (get_string str) (Inl (fresh_fd h)))) = SOpenReturnSuccess str h in
    let _ : step (EOpen str) (EInr EUnit) h (Some (EvOpen (get_string str) (Inr ()))) = SOpenReturnFail str h in
  ()
  end;

  introduce ~(indexed_irred str h) ==> (exists e' oev. step (EOpen str) e' h oev) with _. begin
    assert (exists str' oev'. step str str' h oev');
    eliminate exists str' oev'. step str str' h oev' returns exists e' oev. step (EOpen str) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (SOpen st))
    end
  end

let rec destruct_steps_eopen_str
  (str:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EOpen str) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
  (requires indexed_irred e' (h++lt) /\
    indexed_sem_expr_shape TString str h)
  (ensures fun (str', (| lt1, lt' |)) ->
    EString? str' /\
    steps str str' h lt1 /\
    steps (EOpen str) (EOpen str') h lt1 /\
    steps (EOpen str') e' (h++lt1) lt' /\
    (lt == (lt1 @ lt')))
  (decreases st) =
  match st with
  | SRefl (EOpen str) h -> begin
    can_step_eopen str h;
    false_elim ()
    end
  | STrans #e #f2 #e' #h #_ #lt23 step_eopen step_eopen_steps -> begin
    let (EOpen str) = e in
    match step_eopen with
    | SOpen #str #str' #h #oev step_str -> begin
      let (EOpen str') = f2 in
      lem_step_implies_steps str str' h oev;
      lem_step_implies_steps (EOpen str) (EOpen str') h oev;
      let lt1 : local_trace h = as_lt oev in
      let s2 : steps (EOpen str') e' (h++lt1) lt23 = step_eopen_steps in
      trans_history h lt1 lt23;
      lem_step_preserve_indexed_sem_expr_shape str str' h oev TString;
      let (str'', (| lt1', lt' |)) = destruct_steps_eopen_str str' e' (h++lt1) lt23 s2 in
      trans_history h lt1 lt1';
      lem_steps_transitive str str' str'' h lt1 lt1';
      lem_steps_transitive (EOpen str) (EOpen str') (EOpen str'') h lt1 lt1';
      (str'', (| (lt1 @ lt1'), lt' |))
      end
    | _ -> (str, (| [], lt |))
    end

#push-options "--z3rlimit 10000"
let destruct_steps_eopen
  (str':closed_exp{EString? str'})
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EOpen str') e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt))
    (ensures fun (e_r, (| lt1, lt2 |)) ->
       steps (EOpen str') e_r h lt1 /\
       (e_r == EInl (get_efd (fresh_fd h)) \/ e_r == EInr EUnit) /\
       (EInl? e_r ==>
         steps e_r e' (h++lt1) lt2 /\ lt == (lt1 @ lt2) /\ lt1 == [EvOpen (get_string str') (Inl (fresh_fd h))]) /\
       (EInr? e_r ==>
         steps e_r e' (h++lt1) lt2 /\ lt == (lt1 @ lt2) /\ lt1 == [EvOpen (get_string str') (Inr ())]) /\
       lt == (lt1 @ lt2))
    (decreases st) =
    match st with
    | SRefl (EOpen str') h -> begin
      can_step_eopen_str str' h;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_eopen step_eopen_steps -> begin
      let EOpen str' = e in
      match step_eopen with
      | SOpenReturnSuccess str' h -> begin
        assert (EInl (get_efd (fresh_fd h)) == f2);
        lem_step_implies_steps (EOpen str') (EInl (get_efd (fresh_fd h))) h (Some (EvOpen (get_string str') (Inl (fresh_fd h))));
        let lt' : local_trace h = [EvOpen (get_string str') (Inl (fresh_fd h))] in
        let s2 : steps (EInl (get_efd (fresh_fd h))) e' (h++lt') lt23 = step_eopen_steps in
        trans_history h lt' lt23;
        lem_value_preserves_value (get_efd (fresh_fd h)) (h++lt') TFileDescr;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einl (get_efd (fresh_fd h)) e' (h++lt') lt23 s2 in
        (f2, (| lt', lt12 @ lt_f |))
        end
      | SOpenReturnFail str' h -> begin
        let EInr EUnit = f2 in
        lem_step_implies_steps (EOpen str') (EInr EUnit) h (Some (EvOpen (get_string str') (Inr ())));
        let lt' : local_trace h = [EvOpen (get_string str') (Inr ())] in
        let s2 : steps (EInr EUnit) e' (h++lt') lt23 = step_eopen_steps in
        trans_history h lt' lt23;
        lem_value_preserves_value EUnit (h++lt') TUnit;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einr EUnit e' (h++lt') lt23 s2 in
        (f2, (| lt', lt12 @ lt_f |))
        end
      end
#pop-options

let can_step_eclose (fd:closed_exp) (h:history) :
  Lemma
  (requires indexed_sem_expr_shape TFileDescr fd h)
  (ensures (exists e' oev. step (EClose fd) e' h oev))
  =
  introduce indexed_irred fd h ==> (exists e' oev. step (EClose fd) e' h oev) with _. begin
    assert (steps fd fd h []);
    let st1 : step (EClose fd) (EInl EUnit) h (Some (EvClose (get_fd fd) (Inl ()))) = SCloseReturn h (get_fd fd) (Inl ()) in
    let st2 : step (EClose fd) (EInr EUnit) h (Some (EvClose (get_fd fd) (Inr ()))) = SCloseReturn h (get_fd fd) (Inr ()) in
  ()
  end;

  introduce ~(indexed_irred fd h) ==> (exists e' oev. step (EClose fd) e' h oev) with _. begin
    assert (exists fd' oev'. step fd fd' h oev');
    eliminate exists fd' oev'. step fd fd' h oev' returns exists e' oev. step (EClose fd) e' h oev with st. begin
      bind_squash st (fun st -> return_squash (SClose st))
    end
  end

let rec destruct_steps_eclose_fd
  (fd:closed_exp)
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EClose fd) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
  (requires indexed_irred e' (h++lt) /\
    indexed_sem_expr_shape TFileDescr fd h)
  (ensures fun (fd', (| lt1, lt' |)) ->
    EFileDescr? fd' /\
    steps fd fd' h lt1 /\
    steps (EClose fd) (EClose fd') h lt1 /\
    steps (EClose fd') e' (h++lt1) lt' /\
    (lt == (lt1 @ lt')))
  (decreases st) =
  match st with
  | SRefl (EClose fd) h -> begin
    can_step_eclose fd h;
    false_elim ()
    end
  | STrans #e #f2 #e' #h #_ #lt23 step_eclose step_eclose_steps -> begin
    let (EClose fd) = e in
    match step_eclose with
    | SClose #fd #fd' #h #oev step_fd -> begin
      let (EClose fd') = f2 in
      lem_step_implies_steps fd fd' h oev;
      lem_step_implies_steps (EClose fd) (EClose fd') h oev;
      let lt1 : local_trace h = as_lt oev in
      let s2 : steps (EClose fd') e' (h++lt1) lt23 = step_eclose_steps in
      trans_history h lt1 lt23;
      lem_step_preserve_indexed_sem_expr_shape fd fd' h oev TFileDescr;
      let (fd'', (| lt1', lt' |)) = destruct_steps_eclose_fd fd' e' (h++lt1) lt23 s2 in
      trans_history h lt1 lt1';
      lem_steps_transitive fd fd' fd'' h lt1 lt1';
      lem_steps_transitive (EClose fd) (EClose fd') (EClose fd'') h lt1 lt1';
      (fd'', (| (lt1 @ lt1'), lt' |))
      end
    | _ -> (fd, (| [], lt |))
    end

let can_step_eclose_fd (fd:closed_exp{EFileDescr? fd}) (h:history) :
  Lemma (exists e' oev. step (EClose fd) e' h oev)
  =
  let st1 : step (EClose fd) (EInl EUnit) h (Some (EvClose (get_fd fd) (Inl ()))) = SCloseReturn h (get_fd fd) (Inl ()) in
  let st2 : step (EClose fd) (EInr EUnit) h (Some (EvClose (get_fd fd) (Inr ()))) = SCloseReturn h (get_fd fd) (Inr ()) in
  ()

#push-options "--z3rlimit 10000"
let destruct_steps_eclose
  (fd:closed_exp{EFileDescr? fd})
  (e':closed_exp)
  (h:history)
  (lt:local_trace h)
  (st:steps (EClose fd) e' h lt) :
  Pure (value * (lt1:local_trace h & local_trace (h++lt1)))
    (requires indexed_irred e' (h++lt))
    (ensures fun (e_r, (| lt1, lt2 |)) ->
       steps (EClose fd) e_r h lt1 /\
       (e_r == EInl EUnit \/ e_r == EInr EUnit) /\
       steps e_r e' (h++lt1) lt2 /\
       (EInl? e_r ==> lt1 == ev_lt (EvClose (get_fd fd) (Inl ()))) /\
       (EInr? e_r ==> lt1 == ev_lt (EvClose (get_fd fd) (Inr ()))) /\
       (lt == (lt1 @ lt2)))
    (decreases st) =
    match st with
    | SRefl (EClose fd) h -> begin
      can_step_eclose_fd fd h;
      false_elim ()
      end
    | STrans #e #f2 #e' #h #_ #lt23 step_eclose step_eclose_steps -> begin
      let EClose fd = e in
      match step_eclose with
      | SCloseReturn h fd (Inl ()) -> begin
        let EInl EUnit = f2 in
        lem_step_implies_steps (EClose (get_efd fd)) (EInl EUnit) h (Some (EvClose fd (Inl ())));
        let lt' : local_trace h = ev_lt (EvClose fd (Inl ())) in
        let s2 : steps (EInl EUnit) e' (h++lt') lt23 = step_eclose_steps in
        trans_history h lt' lt23;
        lem_value_preserves_value EUnit (h++lt') TUnit;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einl EUnit e' (h++lt') lt23 s2 in
        (f2, (| lt', (lt12 @ lt_f) |))
        end
      | SCloseReturn h fd (Inr ()) -> begin
        let EInr EUnit = f2 in
        lem_step_implies_steps (EClose (get_efd fd)) (EInr EUnit) h (Some (EvClose fd (Inr ())));
        let lt' : local_trace h = ev_lt (EvClose fd (Inr ())) in
        let s2 : steps (EInr EUnit) e' (h++lt') lt23 = step_eclose_steps in
        trans_history h lt' lt23;
        lem_value_preserves_value EUnit (h++lt') TUnit;
        let (e12', (| lt12, lt_f |)) = destruct_steps_einr EUnit e' (h++lt') lt23 s2 in
        (f2, (| lt', (lt12 @ lt_f) |))
        end
      end
#pop-options
