(* Substitution proof from: https://fstar-lang.org/tutorial/book/part2/part2_stlc.html *)

module LambdaIO

open FStar.Tactics
open FStar.Classical.Sugar
include Trace

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
  | EStringEq : exp -> exp -> exp
  | ECall  : io_ops -> exp -> exp

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
      | ECall op e' -> ECall op (subst s e')
    | EFileDescr i -> EFileDescr i
    | EString s' -> EString s'
    | EStringEq e1 e2 -> EStringEq (subst s e1) (subst s e2)

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
  | ECall _ e1 -> equiv_subs_implies_equiv_substs f g e1
  | EStringEq e1 e2
  | EApp e1 e2
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
  | EUnit
  | ETrue
  | EFalse
  | EFileDescr _
  | EString _ -> []
  | EVar i -> if i < n then [] else [i-n]
  | EFst e'
  | ESnd e'
  | EInl e'
  | EInr e'
  | ECall _ e' -> free_vars_indx e' n
  | EPair e1 e2
  | EStringEq e1 e2
  | EApp e1 e2 -> free_vars_indx e1 n `L.append` free_vars_indx e2 n
  | ELam e' -> free_vars_indx e' (n+1)
  | EIf e1 e2 e3 -> free_vars_indx e1 n `L.append` free_vars_indx e2 n `L.append` free_vars_indx e3 n
  | ECase e1 e2 e3 -> free_vars_indx e1 n `L.append` free_vars_indx e2 (n+1) `L.append` free_vars_indx e3 (n+1)

let free_vars e = free_vars_indx e 0

let is_closed (e:exp) : bool =
  free_vars e = []

let rec is_value (e:exp) : Type0 =
  match e with
  | EUnit
  | ETrue
  | EFalse
  | EFileDescr _ 
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
  | ECall _ e ->
    lem_shifting_preserves_closed s e n
  | EApp e1 e2
  | EStringEq e1 e2
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
  | EStringEq e1 e2
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
  | ECall _ e' ->
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

let append_eq_nil (#a:Type) (l1 l2:list a) :
  Lemma (requires l1 `L.append` l2 == [])
        (ensures l1 == [] /\ l2 == []) = ()

let rec lem_free_vars_next_binder (e:exp) (n:nat) :
  Lemma
    (requires free_vars_indx e (n+1) == [])
    (ensures (forall x. x `L.memP` free_vars_indx e n ==> x == 0))
    (decreases e) =
  match e with
  | EUnit | ETrue | EFalse | EFileDescr _ | EString _ -> ()
  | EVar _ -> ()
  | ELam e' -> lem_free_vars_next_binder e' (n+1)
  | EFst e' | ESnd e' | EInl e' | EInr e' | ECall _ e' ->
    lem_free_vars_next_binder e' n
  | EApp e1 e2 | EPair e1 e2 | EStringEq e1 e2 ->
    append_eq_nil (free_vars_indx e1 (n+1)) (free_vars_indx e2 (n+1));
    lem_free_vars_next_binder e1 n;
    lem_free_vars_next_binder e2 n;
    introduce forall x. x `L.memP` free_vars_indx e n ==> x == 0
    with introduce _ ==> _ with _.
      L.append_memP (free_vars_indx e1 n) (free_vars_indx e2 n) x
  | EIf e1 e2 e3 ->
    append_eq_nil (free_vars_indx e1 (n+1) `L.append` free_vars_indx e2 (n+1)) (free_vars_indx e3 (n+1));
    append_eq_nil (free_vars_indx e1 (n+1)) (free_vars_indx e2 (n+1));
    lem_free_vars_next_binder e1 n;
    lem_free_vars_next_binder e2 n;
    lem_free_vars_next_binder e3 n;
    introduce forall x. x `L.memP` free_vars_indx e n ==> x == 0
    with introduce _ ==> _ with _.
      (L.append_memP (free_vars_indx e1 n `L.append` free_vars_indx e2 n) (free_vars_indx e3 n) x;
       L.append_memP (free_vars_indx e1 n) (free_vars_indx e2 n) x)
  | ECase e1 e2 e3 ->
    append_eq_nil (free_vars_indx e1 (n+1) `L.append` free_vars_indx e2 (n+2)) (free_vars_indx e3 (n+2));
    append_eq_nil (free_vars_indx e1 (n+1)) (free_vars_indx e2 (n+2));
    lem_free_vars_next_binder e1 n;
    lem_free_vars_next_binder e2 (n+1);
    lem_free_vars_next_binder e3 (n+1);
    introduce forall x. x `L.memP` free_vars_indx e n ==> x == 0
    with introduce _ ==> _ with _.
      (L.append_memP (free_vars_indx e1 n `L.append` free_vars_indx e2 (n+1)) (free_vars_indx e3 (n+1)) x;
       L.append_memP (free_vars_indx e1 n) (free_vars_indx e2 (n+1)) x)

let subst_beta (v e:exp) :
  Pure closed_exp
    (requires (is_closed (ELam e)) /\ is_closed v)
    (ensures (fun _ -> True)) =
  lem_free_vars_next_binder e 0;
  lem_subst_freevars_closes_exp (sub_beta v) e 0;
  subst (sub_beta v) e


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

val as_e_io_args (op:io_ops) (arg:io_args op) : value
let as_e_io_args op arg =
  match op with
  | OOpen -> EString arg
  | ORead -> EFileDescr arg
  | OWrite -> 
    let arg : file_descr * string = arg in
    EPair (EFileDescr (fst arg)) (EString (snd arg))
  | OClose -> EFileDescr arg

val as_e_io_res (op:io_ops) (arg:io_args op) (res:io_res op arg) : value
let as_e_io_res op _ res =
  match op with
  | OOpen -> let res : resexn file_descr = res in get_resexn_fd res
  | ORead -> let res : resexn string = res in get_resexn_string res
  | OWrite -> get_resexn_unit res
  | OClose -> get_resexn_unit res

(* Small-step operational semantics  *)

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
  | SCall :
    #arg:closed_exp ->
    #arg':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    #op:io_ops ->
    hst:step arg arg' h oev ->
    step (ECall op arg) (ECall op arg') h oev
  | SCallReturn :
    h:history ->
    op:io_ops ->
    arg:(io_args op){io_pre h op arg} ->
    res:(io_res op arg){io_post h op arg res} ->
    step (ECall op (as_e_io_args op arg)) (as_e_io_res op arg res) h (Some (op_to_ev op arg res))
  | StringEqLeft :
    #e1:closed_exp ->
    e2:closed_exp ->
    #e1':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step e1 e1' h oev ->
    step (EStringEq e1 e2) (EStringEq e1' e2) h oev
  | StringEqRight :
    e1:closed_exp{EString? e1} ->
    #e2:closed_exp ->
    #e2':closed_exp ->
    #h:history ->
    #oev:option (event_h h) ->
    hst:step e2 e2' h oev ->
    step (EStringEq e1 e2) (EStringEq e1 e2') h oev
  | StringEqReturn :
    s1:string ->
    s2:string ->
    h:history ->
    step (EStringEq (EString s1) (EString s2)) (if s1 = s2 then ETrue else EFalse) h None

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
