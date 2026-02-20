module QTyp

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open IO

(** We define quotation for Type **)

(** We need quotation for types to define the logical relation. **)
noeq
type type_quotation : Type0 -> Type u#1 =
| QUnit : type_quotation unit
| QBool : type_quotation bool
| QFileDescriptor : type_quotation file_descr
| QString : type_quotation string
| QArr : #t1:Type ->
         #t2:Type ->
         type_quotation t1 ->
         type_quotation t2 ->
         type_quotation (t1 -> t2)
| QArrIO : #t1:Type ->
         #t2:Type ->
         type_quotation t1 ->
         type_quotation t2 ->
         type_quotation (t1 -> io t2)
| QPair : #t1:Type ->
          #t2:Type ->
          type_quotation t1 ->
          type_quotation t2 ->
          type_quotation (t1 & t2)
| QSum  : #t1:Type ->
          #t2:Type ->
          type_quotation t1 ->
          type_quotation t2 ->
          type_quotation (either t1 t2)

let test_match t (tq:type_quotation t) = (** why does this work so well? **)
  match tq with
  | QUnit -> assert (t == unit)
  | QBool -> assert (t == bool)
  | QFileDescriptor -> assert (t == file_descr)
  | QString -> assert (t == string)
  | QArr #t1 #t2 _ _ -> assert (t == (t1 -> t2))
  | QArrIO #t1 #t2 _ _ -> assert (t == (t1 -> io t2))
  | QPair #t1 #t2 _ _ -> assert (t == (t1 & t2))
  | QSum #t1 #t2 _ _ -> assert (t == either t1 t2)

let rec type_quotation_to_typ #s (qt:type_quotation s) : typ =
  match qt with
  | QUnit -> TUnit
  | QBool -> TBool
  | QFileDescriptor -> TFileDescr
  | QString -> TString
  | QPair qt1 qt2 -> TPair (type_quotation_to_typ qt1) (type_quotation_to_typ qt2)
  | QArr qt1 qt2
  | QArrIO qt1 qt2 ->
    TArr (type_quotation_to_typ qt1) (type_quotation_to_typ qt2)
  | QSum qt1 qt2 -> TSum (type_quotation_to_typ qt1) (type_quotation_to_typ qt2)

(** Type of Quotable Types **)
type qType =
  t:Type & type_quotation t

let pack (q:type_quotation 's) : qType = (| _, q |)

let get_Type (t:qType) = Mkdtuple2?._1 t
let get_rel (t:qType) = Mkdtuple2?._2 t
let lem_pack_get_rel t : Lemma (pack (get_rel t) == t) = ()

let qUnit : qType = (| _, QUnit |)
let qBool : qType = (| _, QBool |)
let qFileDescr : qType = (| _, QFileDescriptor |)
let qString : qType = (| _, QString |)
let (^->) (t1 t2:qType) : qType =
  (| _, QArr (get_rel t1) (get_rel t2) |)
let (^->!@) (t1 t2:qType) : qType =
  (| _, QArrIO (get_rel t1) (get_rel t2) |)

let (^*) (t1 t2:qType) : qType =
  (| _, QPair (get_rel t1) (get_rel t2) |)
let (^+) (t1 t2:qType) : qType =
  (| _, QSum (get_rel t1) (get_rel t2) |)

let qResexn (t1:qType) : qType = t1 ^+ qUnit

(** typ_env is a typing environment: variables to Quotable F* Types **)
type typ_env = var -> option qType
let empty : typ_env = fun _ -> None

(* we only need extend at 0 *)
let extend (t:qType) (g:typ_env)
  : typ_env
  = fun y -> if y = 0 then Some t
          else g (y-1)

let fv_in_env (g:typ_env) (e:exp) : Type0 =
  forall (fv:var). fv `memP` free_vars e ==> Some? (g fv)

let lem_no_fv_is_closed (e:exp) : Lemma
  (requires fv_in_env empty e)
  (ensures is_closed e)
  [SMTPat (is_closed e)] =
  ()

let lem_closed_is_no_fv (e:exp) : Lemma
  (requires is_closed e)
  (ensures fv_in_env empty e)
  [SMTPat (is_closed e)] =
  ()

(** Helper: incrementing the binder depth shifts free variable indices by -1.
    I.e., fv in free_vars_indx at depth n+1 iff fv+1 in free_vars_indx at depth n. **)
let rec lem_free_vars_indx_shift (e:exp) (n:nat) :
  Lemma (ensures forall (fv:var). fv `memP` free_vars_indx e (n+1) <==> (fv+1) `memP` free_vars_indx e n)
        (decreases e) =
  match e with
  | EUnit | ETrue | EFalse | EFileDescr _ | EString _ -> ()
  | EVar _ -> ()
  | ELam e' -> lem_free_vars_indx_shift e' (n+1)
  | EFst e' | ESnd e' | EInl e' | EInr e'
  | ERead e' | EOpen e' | EClose e' -> lem_free_vars_indx_shift e' n
  | EApp e1 e2 | EPair e1 e2 | EWrite e1 e2 | EStringEq e1 e2 ->
    lem_free_vars_indx_shift e1 n;
    lem_free_vars_indx_shift e2 n;
    append_memP_forall (free_vars_indx e1 (n+1)) (free_vars_indx e2 (n+1));
    append_memP_forall (free_vars_indx e1 n) (free_vars_indx e2 n)
  | EIf e1 e2 e3 ->
    lem_free_vars_indx_shift e1 n;
    lem_free_vars_indx_shift e2 n;
    lem_free_vars_indx_shift e3 n;
    append_memP_forall (free_vars_indx e1 (n+1) @ free_vars_indx e2 (n+1)) (free_vars_indx e3 (n+1));
    append_memP_forall (free_vars_indx e1 (n+1)) (free_vars_indx e2 (n+1));
    append_memP_forall (free_vars_indx e1 n @ free_vars_indx e2 n) (free_vars_indx e3 n);
    append_memP_forall (free_vars_indx e1 n) (free_vars_indx e2 n)
  | ECase e1 e2 e3 ->
    lem_free_vars_indx_shift e1 n;
    lem_free_vars_indx_shift e2 (n+1);
    lem_free_vars_indx_shift e3 (n+1);
    append_memP_forall (free_vars_indx e1 (n+1) @ free_vars_indx e2 (n+2)) (free_vars_indx e3 (n+2));
    append_memP_forall (free_vars_indx e1 (n+1)) (free_vars_indx e2 (n+2));
    append_memP_forall (free_vars_indx e1 n @ free_vars_indx e2 (n+1)) (free_vars_indx e3 (n+1));
    append_memP_forall (free_vars_indx e1 n) (free_vars_indx e2 (n+1))

(** Helper: a "shift-at-depth-n" substitution (identity below n, +1 at/above n)
    shifts all free variable indices by +1. *)
#push-options "--split_queries always --z3rlimit 15"
let rec lem_free_vars_subst_inc (s:sub true) (e:exp) (n:nat) :
  Lemma
    (requires
      (forall (y:var). y < n ==> s y == EVar y) /\
      (forall (y:var). y >= n ==> s y == EVar (y + 1)))
    (ensures forall (fv:var). (fv+1) `memP` free_vars_indx (subst s e) n <==> fv `memP` free_vars_indx e n)
    (decreases e) =
  match e with
  | EUnit | ETrue | EFalse | EFileDescr _ | EString _ -> ()
  | EVar _ -> ()
  | ELam e' ->
    let s' = sub_elam s in
    introduce forall (y:var). y < n+1 ==> s' y == EVar y with begin
      introduce _ ==> _ with _. begin
        if y = 0 then () else ()
      end
    end;
    introduce forall (y:var). y >= n+1 ==> s' y == EVar (y + 1) with begin
      introduce _ ==> _ with _. ()
    end;
    lem_free_vars_subst_inc s' e' (n+1)
  | EFst e' | ESnd e' | EInl e' | EInr e'
  | ERead e' | EOpen e' | EClose e' ->
    lem_free_vars_subst_inc s e' n
  | EApp e1 e2 | EPair e1 e2 | EWrite e1 e2 | EStringEq e1 e2 ->
    lem_free_vars_subst_inc s e1 n;
    lem_free_vars_subst_inc s e2 n;
    append_memP_forall (free_vars_indx (subst s e1) n) (free_vars_indx (subst s e2) n);
    append_memP_forall (free_vars_indx e1 n) (free_vars_indx e2 n)
  | EIf e1 e2 e3 ->
    lem_free_vars_subst_inc s e1 n;
    lem_free_vars_subst_inc s e2 n;
    lem_free_vars_subst_inc s e3 n;
    append_memP_forall (free_vars_indx (subst s e1) n @ free_vars_indx (subst s e2) n) (free_vars_indx (subst s e3) n);
    append_memP_forall (free_vars_indx (subst s e1) n) (free_vars_indx (subst s e2) n);
    append_memP_forall (free_vars_indx e1 n @ free_vars_indx e2 n) (free_vars_indx e3 n);
    append_memP_forall (free_vars_indx e1 n) (free_vars_indx e2 n)
  | ECase e1 e2 e3 ->
    lem_free_vars_subst_inc s e1 n;
    let s' = sub_elam s in
    introduce forall (y:var). y < n+1 ==> s' y == EVar y with begin
      introduce _ ==> _ with _. begin
        if y = 0 then () else ()
      end
    end;
    introduce forall (y:var). y >= n+1 ==> s' y == EVar (y + 1) with begin
      introduce _ ==> _ with _. ()
    end;
    lem_free_vars_subst_inc s' e2 (n+1);
    lem_free_vars_subst_inc s' e3 (n+1);
    append_memP_forall (free_vars_indx (subst s e1) n @ free_vars_indx (subst s' e2) (n+1)) (free_vars_indx (subst s' e3) (n+1));
    append_memP_forall (free_vars_indx (subst s e1) n) (free_vars_indx (subst s' e2) (n+1));
    append_memP_forall (free_vars_indx e1 n @ free_vars_indx e2 (n+1)) (free_vars_indx e3 (n+1));
    append_memP_forall (free_vars_indx e1 n) (free_vars_indx e2 (n+1))
#pop-options

let lem_fv_in_env_varS (g:typ_env) (t:qType) (e:exp) :
  Lemma (fv_in_env g e <==> fv_in_env (extend t g) (subst sub_inc e))
  = lem_free_vars_subst_inc sub_inc e 0

let lem_fv_in_env_lam (g:typ_env) (t:qType) (body:exp) :
  Lemma (fv_in_env (extend t g) body <==>  fv_in_env g (ELam body))
   = lem_free_vars_indx_shift body 0

let lem_fv_in_env_app (g:typ_env) (e1 e2:exp) :
  Lemma ((fv_in_env g e1 /\ fv_in_env g e2) <==> fv_in_env g (EApp e1 e2))
  = append_memP_forall (free_vars e1) (free_vars e2)

let lem_fv_in_env_if (g:typ_env) (e1 e2 e3:exp) :
  Lemma ((fv_in_env g e1 /\ fv_in_env g e2 /\ fv_in_env g e3) <==> fv_in_env g (EIf e1 e2 e3))
  = append_memP_forall (free_vars e1 @ free_vars e2) (free_vars e3);
    append_memP_forall (free_vars e1) (free_vars e2)

let lem_fv_in_env_pair (g:typ_env) (e1 e2:exp) :
  Lemma ((fv_in_env g e1 /\ fv_in_env g e2) <==> fv_in_env g (EPair e1 e2))
  = append_memP_forall (free_vars e1) (free_vars e2)

let lem_fv_in_env_string_eq (g:typ_env) (e1 e2:exp) :
  Lemma ((fv_in_env g e1 /\ fv_in_env g e2) <==> fv_in_env g (EStringEq e1 e2))
  = append_memP_forall (free_vars e1) (free_vars e2)

let lem_fv_in_env_fst (g:typ_env) (e:exp) :
  Lemma (fv_in_env g (EFst e) <==> fv_in_env g e)
  = ()

let lem_fv_in_env_snd (g:typ_env) (e:exp) :
  Lemma (fv_in_env g (ESnd e) <==>  fv_in_env g e)
  = ()

let lem_fv_in_env_inl (g:typ_env) (e:exp) :
  Lemma (fv_in_env g (EInl e) <==>  fv_in_env g e)
  = ()

let lem_fv_in_env_inr (g:typ_env) (e:exp) :
  Lemma (fv_in_env g (EInr e) <==>  fv_in_env g e)
  = ()


#push-options "--split_queries always --z3rlimit 10"
let lem_fv_in_env_case (g:typ_env) (t1 t2:qType) (e1 e2 e3:exp) :
  Lemma ((fv_in_env g e1 /\ fv_in_env (extend t1 g) e2 /\ fv_in_env (extend t2 g) e3) <==> fv_in_env g (ECase e1 e2 e3))
  =
  (* Split memP over the appended free variable lists *)
  append_memP_forall (free_vars_indx e1 0 @ free_vars_indx e2 1) (free_vars_indx e3 1);
  append_memP_forall (free_vars_indx e1 0) (free_vars_indx e2 1);
  (* Connect fv_in_env (extend t g) e with free_vars_indx e at depth 1 *)
  lem_free_vars_indx_shift e2 0;
  lem_free_vars_indx_shift e3 0
#pop-options

let lem_fv_in_env_openfile (g:typ_env) (fnm:exp) :
  Lemma (fv_in_env g fnm <==> fv_in_env g (EOpen fnm))
  = ()

let lem_fv_in_env_read (g:typ_env) (fd:exp) :
  Lemma (fv_in_env g fd <==> fv_in_env g (ERead fd))
  = ()

let lem_fv_in_env_write (g:typ_env) (fd msg:exp) :
  Lemma ((fv_in_env g fd /\ fv_in_env g msg) <==> fv_in_env g (EWrite fd msg))
  = append_memP_forall (free_vars fd) (free_vars msg)

let lem_fv_in_env_close (g:typ_env) (fd:exp) :
  Lemma (fv_in_env g fd <==> fv_in_env g (EClose fd))
  = ()

(** STLC Evaluation Environment : variable -> value **)
let gsub (g:typ_env) (b:bool{b ==> (forall x. None? (g x))}) = (** CA: this b is polluting **)
  s:(sub b){forall x. Some? (g x) ==> is_value (s x)}

let gsub_empty : gsub empty true =
  (fun v -> EVar v)

let gsub_extend (#g:typ_env) #b (s:gsub g b) (t:qType) (v:value) : gsub (extend t g) false =
  let f = fun (y:var) -> if y = 0 then v else s (y-1) in
  introduce exists (x:var). ~(EVar? (f x)) with 0 and ();
  f

let gsub_comp #b #b' (g:sub b) (f:sub b') : sub (b && b') =
  fun (y:var) -> subst g (f y)

#push-options "--split_queries always --z3rlimit 32"
(* this should be true for arbitrary b b' *)
let rec subst_comp (f:sub false) (g:sub true) (e:exp) :
  Lemma (ensures subst f (subst g e) == subst (gsub_comp f g) e)
        (decreases e) =
  match e with
  | EUnit
  | ETrue
  | EFalse
  | EVar _
  | EFileDescr _
  | EString _ -> ()
  | ELam e1 -> begin
    subst_comp (sub_elam f) (sub_elam g) e1;
    introduce forall (x:var). (gsub_comp (sub_elam f) (sub_elam g)) x == (sub_elam (gsub_comp f g)) x with begin
      ()
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam f) (sub_elam g)) (sub_elam (gsub_comp f g)) e1
    end
  | EFst e1
  | ESnd e1
  | EInl e1
  | EInr e1
  | ERead e1
  | EOpen e1
  | EClose e1 -> subst_comp f g e1
  | EApp e1 e2
  | EWrite e1 e2
  | EStringEq e1 e2
  | EPair e1 e2 -> begin
    subst_comp f g e1;
    subst_comp f g e2
    end
  | EIf e1 e2 e3 -> begin
    subst_comp f g e1;
    subst_comp f g e2;
    subst_comp f g e3
    end
  | ECase e1 e2 e3 -> begin
    subst_comp f g e1;
    subst_comp (sub_elam f) (sub_elam g) e2;
    subst_comp (sub_elam f) (sub_elam g) e3;
    introduce forall (x:var). (gsub_comp (sub_elam f) (sub_elam g)) x == (sub_elam (gsub_comp f g)) x with begin
      ()
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam f) (sub_elam g)) (sub_elam (gsub_comp f g)) e2;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam f) (sub_elam g)) (sub_elam (gsub_comp f g)) e3
    end

let rec shift_sub_equiv_sub_inc_no_rename #t #g
  (s':gsub (extend t g) false)
  (e:exp)
  (f:gsub g false{forall (x:var). (f x) == (s' (x+1))}) :
  Lemma (ensures subst s' (subst sub_inc e) == subst #false f e) =
  match e with
  | EUnit
  | ETrue
  | EFalse
  | EVar _
  | EFileDescr _
  | EString _ -> ()
  | ELam e1 -> begin
    subst_comp (sub_elam s') (sub_elam sub_inc) e1;
    introduce forall (x:var). (gsub_comp (sub_elam s') (sub_elam sub_inc)) x == (sub_elam f) x with begin
      ()
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam s') (sub_elam sub_inc)) (sub_elam f) e1
  end
  | EFst e1
  | ESnd e1
  | EInl e1
  | EInr e1
  | ERead e1
  | EOpen e1
  | EClose e1 -> shift_sub_equiv_sub_inc_no_rename #t #g s' e1 f
  | EApp e1 e2
  | EWrite e1 e2
  | EStringEq e1 e2
  | EPair e1 e2 -> begin
    shift_sub_equiv_sub_inc_no_rename #t #g s' e1 f;
    shift_sub_equiv_sub_inc_no_rename #t #g s' e2 f
  end
  | EIf e1 e2 e3 -> begin
    shift_sub_equiv_sub_inc_no_rename #t #g s' e1 f;
    shift_sub_equiv_sub_inc_no_rename #t #g s' e2 f;
    shift_sub_equiv_sub_inc_no_rename #t #g s' e3 f
  end
  | ECase e1 e2 e3 -> begin
    shift_sub_equiv_sub_inc_no_rename #t #g s' e1 f;
    subst_comp (sub_elam s') (sub_elam sub_inc) e2;
    subst_comp (sub_elam s') (sub_elam sub_inc) e3;
    introduce forall (x:var). (gsub_comp (sub_elam s') (sub_elam sub_inc)) x == (sub_elam f) x with begin
      ()
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam s') (sub_elam sub_inc)) (sub_elam f) e2;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam s') (sub_elam sub_inc)) (sub_elam f) e3
  end

let rec shift_sub_equiv_sub_inc_rename #t
  (s':gsub (extend t empty) false)
  (e:exp)
  (f:gsub empty true{forall (x:var). (f x) == (s' (x+1))}) :
  Lemma (ensures subst s' (subst sub_inc e) == subst #true f e)
        (decreases e) =
  match e with
  | EUnit
  | ETrue
  | EFalse
  | EVar _
  | EFileDescr _
  | EString _ -> ()
  | ELam e1 -> begin
    subst_comp (sub_elam s') (sub_elam sub_inc) e1;
    introduce forall (x:var). (gsub_comp (sub_elam s') (sub_elam sub_inc)) x == (sub_elam f) x with ();
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam s') (sub_elam sub_inc)) (sub_elam f) e1
  end
  | EFst e1
  | ESnd e1
  | EInl e1
  | EInr e1
  | ERead e1
  | EOpen e1
  | EClose e1 -> shift_sub_equiv_sub_inc_rename #t s' e1 f
  | EApp e1 e2
  | EWrite e1 e2
  | EStringEq e1 e2
  | EPair e1 e2 -> begin
    shift_sub_equiv_sub_inc_rename #t s' e1 f;
    shift_sub_equiv_sub_inc_rename #t s' e2 f
  end
  | EIf e1 e2 e3 -> begin
    shift_sub_equiv_sub_inc_rename #t s' e1 f;
    shift_sub_equiv_sub_inc_rename #t s' e2 f;
    shift_sub_equiv_sub_inc_rename #t s' e3 f
  end
  | ECase e1 e2 e3 -> begin
    shift_sub_equiv_sub_inc_rename #t s' e1 f;
    subst_comp (sub_elam s') (sub_elam sub_inc) e2;
    subst_comp (sub_elam s') (sub_elam sub_inc) e3;
    introduce forall (x:var). (gsub_comp (sub_elam s') (sub_elam sub_inc)) x == (sub_elam f) x with begin
      ()
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam s') (sub_elam sub_inc)) (sub_elam f) e2;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam s') (sub_elam sub_inc)) (sub_elam f) e3
  end
#pop-options

let gsubst (#g:typ_env) #b (s:gsub g b) (e:exp{fv_in_env g e}) : closed_exp =
  introduce forall fv. fv `memP` free_vars_indx e 0 ==> free_vars_indx (s fv) 0 == [] with begin
    introduce _ ==> _ with _. begin
    match (s fv) with
    | EUnit -> ()
    | ETrue -> ()
    | EFalse -> ()
    | EFileDescr _ -> ()
    | EString _ -> ()
    | ELam _ -> ()
    | EPair e1 e2 -> begin
      lem_value_is_closed e1;
      lem_value_is_closed e2
      end
    | EInl e' -> lem_value_is_closed e'
    | EInr e' -> lem_value_is_closed e'
    end
  end;
  lem_subst_freevars_closes_exp s e 0;
  subst s e

(** Helper: identity substitution is the identity **)
let sub_id : sub true = fun (y:var) -> EVar y

let rec lem_subst_id (e:exp) :
  Lemma (ensures subst sub_id e == e)
  (decreases e) =
  match e with
  | EUnit | ETrue | EFalse | EFileDescr _ | EString _ -> ()
  | EVar _ -> ()
  | ELam e' ->
    introduce forall (y:var). sub_elam sub_id y == sub_id y with begin
      if y = 0 then () else ()
    end;
    equiv_subs_implies_equiv_substs (sub_elam sub_id) sub_id e';
    lem_subst_id e'
  | EFst e' | ESnd e' | EInl e' | EInr e'
  | ERead e' | EOpen e' | EClose e' -> lem_subst_id e'
  | EApp e1 e2 | EPair e1 e2 | EWrite e1 e2 | EStringEq e1 e2 ->
    lem_subst_id e1; lem_subst_id e2
  | EIf e1 e2 e3 ->
    lem_subst_id e1; lem_subst_id e2; lem_subst_id e3
  | ECase e1 e2 e3 ->
    lem_subst_id e1;
    introduce forall (y:var). sub_elam sub_id y == sub_id y with begin
      if y = 0 then () else ()
    end;
    equiv_subs_implies_equiv_substs (sub_elam sub_id) sub_id e2;
    equiv_subs_implies_equiv_substs (sub_elam sub_id) sub_id e3;
    lem_subst_id e2;
    lem_subst_id e3

(** Helper: composition with a renaming on the left **)
(** Helper: gsub_comp (sub_elam r) sub_inc and gsub_comp sub_inc r agree
    pointwise. Both map y to subst sub_inc (r y). *)
let lem_gsub_comp_sub_elam_sub_inc (r:sub true) (y:var) :
  Lemma (gsub_comp (sub_elam r) sub_inc y == gsub_comp sub_inc r y) = ()

(** Helper: subst distributes equally for both compositions above *)
let lem_equiv_subst_comp_inc_ren (r:sub true) (e:exp) :
  Lemma (subst (gsub_comp (sub_elam r) sub_inc) e == subst (gsub_comp sub_inc r) e) =
  introduce forall (y:var). (gsub_comp (sub_elam r) sub_inc) y == (gsub_comp sub_inc r) y with begin
    lem_gsub_comp_sub_elam_sub_inc r y
  end;
  equiv_subs_implies_equiv_substs (gsub_comp (sub_elam r) sub_inc) (gsub_comp sub_inc r) e

(** Helper: composition of two renamings (both sub true).
    Unlike subst_comp which coerces the first arg to sub false,
    this keeps all subst calls at #r=true, avoiding SMT encoding mismatches. *)
#push-options "--split_queries always --z3rlimit 32"
let rec subst_comp_ren_ren (f:sub true) (g:sub true) (e:exp) :
  Lemma (ensures subst f (subst g e) == subst (gsub_comp f g) e)
        (decreases e) =
  match e with
  | EUnit | ETrue | EFalse | EVar _ | EFileDescr _ | EString _ -> ()
  | ELam e1 ->
    subst_comp_ren_ren (sub_elam f) (sub_elam g) e1;
    introduce forall (x:var). (gsub_comp (sub_elam f) (sub_elam g)) x == (sub_elam (gsub_comp f g)) x with begin
      ()
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam f) (sub_elam g)) (sub_elam (gsub_comp f g)) e1
  | EFst e1 | ESnd e1 | EInl e1 | EInr e1
  | ERead e1 | EOpen e1 | EClose e1 -> subst_comp_ren_ren f g e1
  | EApp e1 e2 | EPair e1 e2 | EWrite e1 e2 | EStringEq e1 e2 ->
    subst_comp_ren_ren f g e1; subst_comp_ren_ren f g e2
  | EIf e1 e2 e3 ->
    subst_comp_ren_ren f g e1; subst_comp_ren_ren f g e2; subst_comp_ren_ren f g e3
  | ECase e1 e2 e3 ->
    subst_comp_ren_ren f g e1;
    subst_comp_ren_ren (sub_elam f) (sub_elam g) e2;
    subst_comp_ren_ren (sub_elam f) (sub_elam g) e3;
    introduce forall (x:var). (gsub_comp (sub_elam f) (sub_elam g)) x == (sub_elam (gsub_comp f g)) x with begin
      ()
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam f) (sub_elam g)) (sub_elam (gsub_comp f g)) e2;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam f) (sub_elam g)) (sub_elam (gsub_comp f g)) e3
#pop-options

(** Pointwise equality: (sub_elam r) composed with (sub_elam g) equals
    sub_elam of the composition. Uses subst_comp_ren_ren to keep
    all subst applications at #r=true. *)
let lem_pointwise_sub_elam_ren #b (r:sub true) (g:sub b) (x:var) :
  Lemma (gsub_comp (sub_elam r) (sub_elam g) x == sub_elam (gsub_comp r g) x)
  = if x = 0 then ()
    else begin
      let gx = g (x-1) in
      subst_comp_ren_ren (sub_elam r) sub_inc gx;
      subst_comp_ren_ren sub_inc r gx;
      lem_equiv_subst_comp_inc_ren r gx
    end

#push-options "--split_queries always --z3rlimit 32"

let rec subst_comp_ren #b (r:sub true) (g:sub b) (e:exp) :
  Lemma (ensures subst r (subst g e) == subst (gsub_comp r g) e)
        (decreases e) =
  match e with
  | EUnit | ETrue | EFalse | EVar _ | EFileDescr _ | EString _ -> ()
  | ELam e1 ->
    subst_comp_ren (sub_elam r) (sub_elam g) e1;
    introduce forall (x:var). (gsub_comp (sub_elam r) (sub_elam g)) x == (sub_elam (gsub_comp r g)) x with begin
      lem_pointwise_sub_elam_ren r g x
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam r) (sub_elam g)) (sub_elam (gsub_comp r g)) e1
  | EFst e1 | ESnd e1 | EInl e1 | EInr e1
  | ERead e1 | EOpen e1 | EClose e1 -> subst_comp_ren r g e1
  | EApp e1 e2 | EPair e1 e2 | EWrite e1 e2 | EStringEq e1 e2 ->
    subst_comp_ren r g e1; subst_comp_ren r g e2
  | EIf e1 e2 e3 ->
    subst_comp_ren r g e1; subst_comp_ren r g e2; subst_comp_ren r g e3
  | ECase e1 e2 e3 ->
    subst_comp_ren r g e1;
    subst_comp_ren (sub_elam r) (sub_elam g) e2;
    subst_comp_ren (sub_elam r) (sub_elam g) e3;
    introduce forall (x:var). (gsub_comp (sub_elam r) (sub_elam g)) x == (sub_elam (gsub_comp r g)) x with begin
      lem_pointwise_sub_elam_ren r g x
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam r) (sub_elam g)) (sub_elam (gsub_comp r g)) e2;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam r) (sub_elam g)) (sub_elam (gsub_comp r g)) e3
#pop-options

(** Pointwise equality when g is a renaming: trivially holds by
    destructuring the EVar produced by the renaming. *)
let lem_pointwise_sub_elam_ren_right #b (f:sub b) (g:sub true) (x:var) :
  Lemma (gsub_comp (sub_elam f) (sub_elam g) x == sub_elam (gsub_comp f g) x)
  = if x = 0 then ()
    else match g (x-1) with
         | EVar _ -> ()

(** Composition with a renaming on the right, for general left substitution. *)
#push-options "--split_queries always --z3rlimit 32"
let rec subst_comp_ren_right #b (f:sub b) (g:sub true) (e:exp) :
  Lemma (ensures subst f (subst g e) == subst (gsub_comp f g) e)
        (decreases e) =
  match e with
  | EUnit | ETrue | EFalse | EVar _ | EFileDescr _ | EString _ -> ()
  | ELam e1 ->
    subst_comp_ren_right (sub_elam f) (sub_elam g) e1;
    introduce forall (x:var). (gsub_comp (sub_elam f) (sub_elam g)) x == (sub_elam (gsub_comp f g)) x with begin
      lem_pointwise_sub_elam_ren_right f g x
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam f) (sub_elam g)) (sub_elam (gsub_comp f g)) e1
  | EFst e1 | ESnd e1 | EInl e1 | EInr e1
  | ERead e1 | EOpen e1 | EClose e1 -> subst_comp_ren_right f g e1
  | EApp e1 e2 | EPair e1 e2 | EWrite e1 e2 | EStringEq e1 e2 ->
    subst_comp_ren_right f g e1; subst_comp_ren_right f g e2
  | EIf e1 e2 e3 ->
    subst_comp_ren_right f g e1; subst_comp_ren_right f g e2; subst_comp_ren_right f g e3
  | ECase e1 e2 e3 ->
    subst_comp_ren_right f g e1;
    subst_comp_ren_right (sub_elam f) (sub_elam g) e2;
    subst_comp_ren_right (sub_elam f) (sub_elam g) e3;
    introduce forall (x:var). (gsub_comp (sub_elam f) (sub_elam g)) x == (sub_elam (gsub_comp f g)) x with begin
      lem_pointwise_sub_elam_ren_right f g x
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam f) (sub_elam g)) (sub_elam (gsub_comp f g)) e2;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam f) (sub_elam g)) (sub_elam (gsub_comp f g)) e3
#pop-options

(** Helper: gsub_comp (sub_elam f) sub_inc and gsub_comp sub_inc f agree
    pointwise for general f. Both map y to subst sub_inc (f y). *)
let lem_gsub_comp_sub_elam_sub_inc_gen #b (f:sub b) (y:var) :
  Lemma (gsub_comp (sub_elam f) sub_inc y == gsub_comp sub_inc f y) = ()

let lem_equiv_subst_comp_inc_gen #b (f:sub b) (e:exp) :
  Lemma (subst (gsub_comp (sub_elam f) sub_inc) e == subst (gsub_comp sub_inc f) e) =
  introduce forall (y:var). (gsub_comp (sub_elam f) sub_inc) y == (gsub_comp sub_inc f) y with begin
    lem_gsub_comp_sub_elam_sub_inc_gen f y
  end;
  equiv_subs_implies_equiv_substs (gsub_comp (sub_elam f) sub_inc) (gsub_comp sub_inc f) e

(** Pointwise equality: (sub_elam f) composed with (sub_elam g) equals
    sub_elam of the composition, for general f. *)
let lem_pointwise_sub_elam_gen #b1 #b2 (f:sub b1) (g:sub b2) (x:var) :
  Lemma (gsub_comp (sub_elam f) (sub_elam g) x == sub_elam (gsub_comp f g) x)
  = if x = 0 then ()
    else begin
      subst_comp_ren_right (sub_elam f) sub_inc (g (x-1));
      subst_comp_ren sub_inc f (g (x-1));
      lem_equiv_subst_comp_inc_gen f (g (x-1))
    end

#push-options "--split_queries always --z3rlimit 32"
let rec subst_comp_general #b1 #b2 (f:sub b1) (g:sub b2) (e:exp) :
  Lemma (ensures subst f (subst g e) == subst (gsub_comp f g) e)
        (decreases e) =
  match e with
  | EUnit | ETrue | EFalse | EVar _ | EFileDescr _ | EString _ -> ()
  | ELam e1 ->
    subst_comp_general (sub_elam f) (sub_elam g) e1;
    introduce forall (x:var). (gsub_comp (sub_elam f) (sub_elam g)) x == (sub_elam (gsub_comp f g)) x with begin
      lem_pointwise_sub_elam_gen f g x
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam f) (sub_elam g)) (sub_elam (gsub_comp f g)) e1
  | EFst e1 | ESnd e1 | EInl e1 | EInr e1
  | ERead e1 | EOpen e1 | EClose e1 -> subst_comp_general f g e1
  | EApp e1 e2 | EPair e1 e2 | EWrite e1 e2 | EStringEq e1 e2 ->
    subst_comp_general f g e1; subst_comp_general f g e2
  | EIf e1 e2 e3 ->
    subst_comp_general f g e1; subst_comp_general f g e2; subst_comp_general f g e3
  | ECase e1 e2 e3 ->
    subst_comp_general f g e1;
    subst_comp_general (sub_elam f) (sub_elam g) e2;
    subst_comp_general (sub_elam f) (sub_elam g) e3;
    introduce forall (x:var). (gsub_comp (sub_elam f) (sub_elam g)) x == (sub_elam (gsub_comp f g)) x with begin
      lem_pointwise_sub_elam_gen f g x
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam f) (sub_elam g)) (sub_elam (gsub_comp f g)) e2;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_elam f) (sub_elam g)) (sub_elam (gsub_comp f g)) e3
#pop-options

(** Substitution lemma: beta-reducing after extending a substitution under a
    binder is the same as extending the substitution with the value directly. **)
let lem_substitution #g #b (s:gsub g b) (t:qType) (v:value) (e:exp)
  : Lemma (
    (subst (sub_beta v) (subst (sub_elam s) e)) == (subst (gsub_extend s t v) e))
  =
    subst_comp_general (sub_beta v) (sub_elam s) e;
    introduce forall (x:var). gsub_comp (sub_beta v) (sub_elam s) x == gsub_extend s t v x with begin
      if x = 0 then ()
      else begin
        subst_comp (sub_beta v) sub_inc (s (x-1));
        equiv_subs_implies_equiv_substs (gsub_comp (sub_beta v) sub_inc) sub_id (s (x-1));
        lem_subst_id (s (x-1))
      end
    end;
    equiv_subs_implies_equiv_substs (gsub_comp (sub_beta v) (sub_elam s)) (gsub_extend s t v) e

(** Helper: substitution is identity on closed expressions.
    If e has no free variables at binder depth n, and s acts as identity on
    variables below n, then subst s e == e. *)
let rec lem_subst_closed_identity #b (s:sub b) (e:exp) (n:nat) :
  Lemma
    (requires free_vars_indx e n == [] /\
              (forall (x:var). x < n ==> s x == EVar x))
    (ensures subst s e == e)
    (decreases e) =
  match e with
  | EUnit | ETrue | EFalse | EFileDescr _ | EString _ -> ()
  | EVar _ -> ()
  | ELam e' ->
    introduce forall (x:var). x < n+1 ==> sub_elam s x == EVar x with begin
      introduce _ ==> _ with _. begin
        if x = 0 then () else ()
      end
    end;
    lem_subst_closed_identity (sub_elam s) e' (n+1)
  | EFst e' | ESnd e' | EInl e' | EInr e'
  | ERead e' | EOpen e' | EClose e' ->
    lem_subst_closed_identity s e' n
  | EApp e1 e2 | EPair e1 e2 | EWrite e1 e2 | EStringEq e1 e2 ->
    lem_subst_closed_identity s e1 n;
    lem_subst_closed_identity s e2 n
  | EIf e1 e2 e3 ->
    lem_subst_closed_identity s e1 n;
    lem_subst_closed_identity s e2 n;
    lem_subst_closed_identity s e3 n
  | ECase e1 e2 e3 ->
    lem_subst_closed_identity s e1 n;
    introduce forall (x:var). x < n+1 ==> sub_elam s x == EVar x with begin
      introduce _ ==> _ with _. begin
        if x = 0 then () else ()
      end
    end;
    lem_subst_closed_identity (sub_elam s) e2 (n+1);
    lem_subst_closed_identity (sub_elam s) e3 (n+1)

let lem_gsubst_closed_identiy #g #b (s:gsub g b) (e:closed_exp) :
  Lemma (gsubst s e == e)
  [SMTPat (gsubst s e)] =
  lem_subst_closed_identity s e 0

module FE = FStar.FunctionalExtensionality

(** eval_env is F* Evaluation Environment : variable -> F* values **)
type eval_env g =
  FE.restricted_t (x:var{Some? (g x)}) (fun x -> get_Type (Some?.v (g x)))
let empty_eval : eval_env empty =
  FE.on_dom
    (x:var{Some? (empty x)})
    #(fun x -> get_Type (Some?.v (empty x)))
    (fun _ -> assert False)
val hd : #t:qType -> #g:_ -> eval_env (extend t g) -> get_Type t
let hd #g fsG = fsG 0
val stack : #g:_ -> fsG:eval_env g -> #t:qType -> get_Type t -> eval_env (extend t g)
let stack #g fsG #t fs_v =
  FE.on_dom
    (x:var{Some? ((extend t g) x)})
    #(fun x -> get_Type (Some?.v ((extend t g) x)))
    (fun y ->
      if y = 0 then fs_v else fsG (y-1))
val tail : #t:qType -> #g:_ -> eval_env (extend t g) -> eval_env g
let tail #t #g fsG =
  FE.on_dom
    (x:var{Some? (g x)})
    #(fun x -> get_Type (Some?.v (g x)))
    (fun y -> fsG (y+1))
val index : #g:_ -> eval_env g -> x:STLC.var{Some? (g x)} -> get_Type (Some?.v (g x))
let index #g fsG x = fsG x

val lem_hd_stack #t #g (fsG:eval_env g) (v:get_Type t)
  : Lemma (
 // (fs_hd fsG == fs_hd (fs_tail (fs_stack fsG v))) /\
   hd (stack fsG v) == v)
  [SMTPat (hd (stack fsG v))]
let lem_hd_stack fsG v = ()

val lem_stack_index #g (fsG:eval_env g) #t (v:get_Type t) : Lemma (
  (forall (x:var). Some? (g x) ==>  index fsG x == index (stack fsG v) (x+1)) /\
  index (stack fsG v) 0 == v)
  [SMTPat (stack fsG v)]
let lem_stack_index fsG v = ()

val lem_index_tail #g #t (fsG:eval_env (extend t g)) : Lemma (
  (forall (x:var). Some? (g x) ==>  index fsG (x+1) == index (tail fsG) x))
  [SMTPat (tail fsG)]
let lem_index_tail fsG = ()

val tail_stack_inverse #g (fsG:eval_env g) #t (x:get_Type t)
  : Lemma (tail (stack fsG x) == fsG)
  [SMTPat (tail (stack fsG x))]
let tail_stack_inverse #g fsG #t v =
  let fsG' : eval_env g = tail (stack fsG v) in
  assert (forall x. fsG' x == fsG x);
  assert (FE.feq fsG' fsG);
  FE.extensionality (x:var{Some? (g x)}) (fun x -> get_Type (Some?.v (g x))) fsG' fsG;
  assert (fsG' == fsG)

val index_0_hd #g #t (fsG:eval_env (extend t g))
  : Lemma (index fsG 0 == hd fsG)
let index_0_hd fsG = ()

(** Closed values **)
type fs_val (t:qType) =
  get_Type t

let fs_val_if (#a:qType) (c:fs_val qBool) (e:fs_val a) (t:fs_val a) : fs_val a =
  if c then e else t

unfold
val fs_val_case : #a  : qType ->
                  #b  : qType ->
                  #c  : qType ->
                  cond: fs_val (a ^+ b) ->
                  inlc: (fs_val a -> fs_val c) ->
                  inrc: (fs_val b -> fs_val c) ->
                  fs_val c
let fs_val_case cond inlc inrc =
  match cond with
  | Inl x -> inlc x
  | Inr x -> inrc x

let fs_val_pair #a #b (x:fs_val a) (y:fs_val b) : fs_val (a ^* b) =
  (x, y)

(** Open values **)
type fs_oval (g:typ_env) (t:qType) =
  eval_env g -> get_Type t

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

unfold
let fs_oval_return (g:typ_env) (t:qType) (x:fs_val t) : fs_oval g t =
  fun _ -> x

unfold
let fs_oval_var0 (g:typ_env) (t:qType) : fs_oval (extend t g) t =
  fun fsG -> hd fsG

unfold
let fs_oval_varS (#g:typ_env) (#a:qType) (b:qType) (x:fs_oval g a) : fs_oval (extend b g) a =
  fun fsG -> x (tail fsG)

unfold
let fs_oval_var (g:typ_env) (x:var{Some? (g x)}) : fs_oval g (Some?.v (g x)) =
  fun fsG -> index fsG x

unfold
val fs_oval_app: #g : typ_env ->
                 #a : qType ->
                 #b : qType ->
                 f :fs_oval g (a ^-> b) ->
                 x :fs_oval g a ->
                 fs_oval g b
let fs_oval_app f x fsG = (f fsG) (x fsG)

unfold
val fs_oval_lambda : #g :typ_env ->
                     #a :qType ->
                     #b :qType ->
                     body :fs_oval (extend a g) b ->
                     fs_oval g (a ^-> b)
let fs_oval_lambda #_ #_ body fsG x = body (stack fsG x)

unfold
val fs_oval_eq_string :
  #g : typ_env ->
  s1 : fs_oval g qString ->
  s2 : fs_oval g qString ->
  fs_oval g qBool
let fs_oval_eq_string s1 s2 fsG =
  (s1 fsG) = (s2 fsG)

unfold
val fs_oval_if : #g :typ_env ->
                 #a  : qType ->
                 c   : fs_oval g qBool ->
                 t   : fs_oval g a ->
                 e   : fs_oval g a ->
                 fs_oval g a
let fs_oval_if c t e fsG =
  if c fsG then t fsG else e fsG

unfold
val fs_oval_pair : #g : typ_env ->
                   #a : qType ->
                   #b : qType ->
                   x : fs_oval g a ->
                   y : fs_oval g b ->
                   fs_oval g (a ^* b)
let fs_oval_pair x y fsG =
  fs_val_pair (x fsG) (y fsG)

unfold
val fs_oval_fmap : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    p : fs_oval g a ->
                    f : (fs_val a -> fs_val b) ->
                    fs_oval g b
let fs_oval_fmap p f fsG = f (p fsG)

unfold
val fs_oval_case : #g :typ_env ->
                  #a  : qType ->
                  #b  : qType ->
                  #c  : qType ->
                  cond: fs_oval g (a ^+ b) ->
                  inlc: fs_oval (extend a g) c ->
                  inrc: fs_oval (extend b g) c ->
                  fs_oval g c
let fs_oval_case cond inlc inrc fsG =
  match cond fsG with
  | Inl x -> inlc (stack fsG x)
  | Inr x -> inrc (stack fsG x)

(** Producers **)
type fs_prod (t:qType) =
   io (get_Type t)

unfold
val fs_prod_bind : #a:qType ->
                    #b:qType ->
                    m:fs_prod a ->
                    k:(fs_val a -> fs_prod b) ->
                    fs_prod b
let fs_prod_bind m k = io_bind m k

unfold
val fs_prod_if_val :
                #a  : qType ->
                c   : fs_val qBool ->
                t   : fs_prod a ->
                e   : fs_prod a ->
                fs_prod a
let fs_prod_if_val c t e =
  if c then t else e

unfold
val fs_prod_case_val : #a  : qType ->
                #b : qType ->
                #c : qType ->
                cond : fs_val (a ^+ b) ->
                inlc : (fs_val a -> fs_prod c) ->
                inrc : (fs_val b -> fs_prod c) ->
                fs_prod c
let fs_prod_case_val cond inlc inrc =
  match cond with
  | Inl x -> inlc x
  | Inr x -> inrc x

val fs_prod_openfile_val :
        fnm:fs_val qString ->
        fs_prod (qResexn qFileDescr)
let fs_prod_openfile_val fnm = openfile fnm

val fs_prod_read_val :
        fd:fs_val qFileDescr ->
        fs_prod (qResexn qString)
let fs_prod_read_val fd = read fd

val fs_prod_write_val :
        fd:fs_val qFileDescr ->
        msg:fs_val qString ->
        fs_prod (qResexn qUnit)
let fs_prod_write_val fd msg = write (fd, msg)

val fs_prod_close_val :
        fd:fs_val qFileDescr ->
        fs_prod (qResexn qUnit)
let fs_prod_close_val fd = close fd

type fs_oprod (g:typ_env) (t:qType) =
  eval_env g -> io (get_Type t)

unfold
val fs_oprod_return :
        #g:typ_env ->
        #a:qType ->
        x:fs_oval g a ->
        fs_oprod g a
let fs_oprod_return x fsG = return (x fsG)

unfold
val fs_oprod_bind : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    m:fs_oprod g a ->
                    k:fs_oprod (extend a g) b ->
                    fs_oprod g b
let fs_oprod_bind m k fsG =
  fs_prod_bind (m fsG) (fun x -> k (stack fsG x))

(** a standard version of the bind **)
unfold
val fs_oprod_bind' : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    m:fs_oprod g a ->
                    k:(fs_val a -> fs_oprod g b) ->
                    fs_oprod g b
let fs_oprod_bind' m k =
  fs_oprod_bind m (fun fsG -> k (hd fsG) (tail fsG))

unfold
val fs_oprod_openfile_oval :
        #g:typ_env ->
        fnm:fs_oval g qString ->
        fs_oprod g (qResexn qFileDescr)
let fs_oprod_openfile_oval fnm fsG = openfile (fnm fsG)

unfold
val fs_oprod_read_oval :
        #g:typ_env ->
        fd:fs_oval g qFileDescr ->
        fs_oprod g (qResexn qString)
let fs_oprod_read_oval fd fsG = read (fd fsG)

unfold
val fs_oprod_write_oval :
        #g:typ_env ->
        fd:fs_oval g qFileDescr ->
        msg:fs_oval g qString ->
        fs_oprod g (qResexn qUnit)
let fs_oprod_write_oval fd msg fsG = write ((fd fsG), (msg fsG))

unfold
val fs_oprod_close_oval :
        #g:typ_env ->
        fd:fs_oval g qFileDescr ->
        fs_oprod g (qResexn qUnit)
let fs_oprod_close_oval fd fsG = close (fd fsG)

unfold
val fs_oval_lambda_oprod : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                body :fs_oprod (extend a g) b ->
                fs_oval g (a ^->!@ b)
let fs_oval_lambda_oprod #_ #_ body fsG x = body (stack fsG x)

unfold
val fs_oprod_app_oval_oval :
                #g : typ_env ->
                #a : qType ->
                #b : qType ->
                f :fs_oval g (a ^->!@ b) ->
                x :fs_oval g a ->
                fs_oprod g b
let fs_oprod_app_oval_oval f x fsG =
  (f fsG) (x fsG)

unfold
val fs_oprod_if_val : #g :typ_env ->
                #a  : qType ->
                c   : fs_val qBool ->
                t   : fs_oprod g a ->
                e   : fs_oprod g a ->
                fs_oprod g a
let fs_oprod_if_val c t e fsG =
  fs_prod_if_val c (t fsG) (e fsG)

unfold
val fs_oprod_if_oval : #g :typ_env ->
                #a  : qType ->
                c   : fs_oval g qBool ->
                t   : fs_oprod g a ->
                e   : fs_oprod g a ->
                fs_oprod g a
let fs_oprod_if_oval c t e fsG =
  fs_oprod_if_val (c fsG) t e fsG

val fs_oprod_if : #g :typ_env ->
                  #a : qType ->
                  c  : fs_oprod g qBool ->
                  t  : fs_oprod g a ->
                  e  : fs_oprod g a ->
                  fs_oprod g a
let fs_oprod_if c t e =
  fs_oprod_bind' c (fun c' -> fs_oprod_if_val c' t e)

unfold
val fs_oprod_case_val : #g :typ_env ->
                #a  : qType ->
                #b : qType ->
                #c : qType ->
                cond : fs_val (a ^+ b) ->
                inlc : fs_oprod (extend a g) c ->
                inrc : fs_oprod (extend b g) c ->
                fs_oprod g c
let fs_oprod_case_val cond inlc inrc fsG =
  match cond with
  | Inl x -> inlc (stack fsG x)
  | Inr x -> inrc (stack fsG x)

unfold
val fs_oprod_case_oval : #g :typ_env ->
                #a  : qType ->
                #b : qType ->
                #c : qType ->
                cond : fs_oval g (a ^+ b) ->
                inlc : fs_oprod (extend a g) c ->
                inrc : fs_oprod (extend b g) c ->
                fs_oprod g c
let fs_oprod_case_oval cond inlc inrc fsG =
  fs_oprod_case_val (cond fsG) inlc inrc fsG

val fs_oprod_case : #g :typ_env ->
                #a  : qType ->
                #b : qType ->
                #c : qType ->
                cond : fs_oprod g (a ^+ b) ->
                inlc : fs_oprod (extend a g) c ->
                inrc : fs_oprod (extend b g) c ->
                fs_oprod g c
let fs_oprod_case cond inlc inrc =
  fs_oprod_bind' cond (fun cond' ->
    fs_oprod_case_val cond' inlc inrc)

(** Necessary for the backtranslation **)
val fs_oprod_return_prod :
        g:typ_env ->
        a:qType ->
        x:fs_prod a ->
        fs_oprod g a
let fs_oprod_return_prod g a x =
  (fun _ -> x)

val fs_oprod_return_val :
        g:typ_env ->
        a:qType ->
        x:fs_val a ->
        fs_oprod g a
let fs_oprod_return_val g a x =
  fs_oprod_return (fs_oval_return g a x)

let fs_oprod_var (g:typ_env) (x:var{Some? (g x)}) : fs_oprod g (Some?.v (g x)) =
  fs_oprod_return (fs_oval_var g x)

val fs_oprod_lambda : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                body :fs_oprod (extend a g) b ->
                fs_oprod g (a ^->!@ b)
let fs_oprod_lambda body =
  fs_oprod_return (fs_oval_lambda_oprod body)

val fs_oprod_app : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    f:fs_oprod g (a ^->!@ b) ->
                    x:fs_oprod g a ->
                    fs_oprod g b
let fs_oprod_app f x =
  fs_oprod_bind' f (fun f' ->
    fs_oprod_bind' x (fun x' ->
      fs_oprod_return_prod _ _ (f' x')))

val fs_oprod_pair : #g : typ_env ->
                   #a : qType ->
                   #b : qType ->
                   x : fs_oprod g a ->
                   y : fs_oprod g b ->
                   fs_oprod g (a ^* b)
let fs_oprod_pair x y =
  fs_oprod_bind' x (fun x' ->
    fs_oprod_bind' y (fun y' ->
      fs_oprod_return_val _ _ (fs_val_pair x' y')))

val fs_oprod_string_eq : #g : typ_env ->
                         x : fs_oprod g qString ->
                         y : fs_oprod g qString ->
                         fs_oprod g qBool
let fs_oprod_string_eq x y =
  fs_oprod_bind' x (fun x' ->
    fs_oprod_bind' y (fun y' ->
      fs_oprod_return_val _ _ (x' = y')))

val fs_oprod_fmap : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    p : fs_oprod g a ->
                    f : (fs_val a -> fs_val b) ->
                    fs_oprod g b
let fs_oprod_fmap p f =
  fs_oprod_bind' p (fun p' ->
    fs_oprod_return_val _ _ (f p'))


val fs_oprod_openfile :
        #g:typ_env ->
        fnm:fs_oprod g qString ->
        fs_oprod g (qResexn qFileDescr)
let fs_oprod_openfile fnm =
  fs_oprod_bind' fnm (fun fnm' ->
    fs_oprod_return_prod _ _ (openfile fnm'))

val fs_oprod_read :
        #g:typ_env ->
        fd:fs_oprod g qFileDescr ->
        fs_oprod g (qResexn qString)
let fs_oprod_read fd =
  fs_oprod_bind' fd (fun fd' ->
    fs_oprod_return_prod _ _ (read fd'))

val fs_oprod_write :
        #g:typ_env ->
        fd:fs_oprod g qFileDescr ->
        msg:fs_oprod g qString ->
        fs_oprod g (qResexn qUnit)
let fs_oprod_write fd msg =
  fs_oprod_bind' fd (fun fd' ->
    fs_oprod_bind' msg (fun msg' ->
      fs_oprod_return_prod _ _ (write (fd', msg'))))

val fs_oprod_close :
        #g:typ_env ->
        fd:fs_oprod g qFileDescr ->
        fs_oprod g (qResexn qUnit)
let fs_oprod_close fd =
  fs_oprod_bind' fd (fun fd' ->
    fs_oprod_return_prod _ _ (close fd'))

open Trace

unfold val fs_beh : #t:qType -> fs_prod t -> h:history -> hist_post h (get_Type t)
let fs_beh m = thetaP m

let lem_fs_beh_open (arg:io_args OOpen) (res:io_res OOpen arg) (h:history) :
  Lemma (requires Inl? res ==> Inl?.v res == fresh_fd h)
        (ensures fs_beh #(qResexn qFileDescr) (openfile arg) h (ev_lt (EvOpen arg res)) res) =
  lem_theta_open arg res h

let lem_fs_beh_read (arg:io_args ORead) (res:io_res ORead arg) (h:history) :
  Lemma (fs_beh #(qResexn qString) (read arg) h (ev_lt (EvRead arg res)) res) =
  lem_theta_read arg res h

let lem_fs_beh_write (arg:io_args OWrite) (res:io_res OWrite arg) (h:history) :
  Lemma (fs_beh #(qResexn qUnit) (write arg) h (ev_lt (EvWrite arg res)) res) =
  lem_theta_write arg res h

let lem_fs_beh_close (arg:io_args OClose) (res:io_res OClose arg) (h:history) :
  Lemma (fs_beh #(qResexn qUnit) (close arg) h (ev_lt (EvClose arg res)) res) =
  lem_theta_close arg res h

let lem_fs_beh_return #a (x:fs_val a) (h:history) :
  Lemma (fs_beh (return x) h [] x) =
  lem_thetaP_return x h

let lem_fs_beh_bind #a #b (m:fs_prod a) (h:history) (lt1:local_trace h) (fs_r_m:fs_val a) (k:fs_val a -> fs_prod b) (lt2:local_trace (h++lt1)) (fs_r:fs_val b) :
  Lemma (requires fs_beh m h lt1 fs_r_m /\
                  fs_beh (k fs_r_m) (h++lt1) lt2 fs_r)
        (ensures fs_beh (fs_prod_bind m k) h (lt1@lt2) fs_r) =
  lem_thetaP_bind m h lt1 fs_r_m k lt2 fs_r

unfold val e_beh : closed_exp -> closed_exp -> h:history -> local_trace h -> Type0
let e_beh e e' h lt =
  steps e e' h lt /\ indexed_irred e' (h++lt)
