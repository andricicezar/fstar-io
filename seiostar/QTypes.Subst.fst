module QTypes.Subst

open FStar.Tactics

open LambdaIO
include QTypes.TypEnv

(** Ground substitutions for LambdaIO: maps variables to values, respecting the typing env **)
let gsub (g:typ_env) (b:bool{b ==> (forall x. None? (g x))}) =
  s:(sub b){forall x. Some? (g x) ==> is_value (s x)}

let gsub_empty : gsub empty true =
  (fun v -> EVar v)

let gsub_extend (#g:typ_env) #b (s:gsub g b) (t:qType) (v:value) : gsub (extend t g) false =
  let f = fun (y:var) -> if y = 0 then v else s (y-1) in
  introduce exists (x:var). ~(EVar? (f x)) with 0 and ();
  f

let gsub_comp #b #b' (g:sub b) (f:sub b') : sub (b && b') =
  fun (y:var) -> subst g (f y)

#push-options "--z3rlimit 32"
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
  | ECall _ e1 -> subst_comp f g e1
  | EApp e1 e2
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
  | ECall _ e1 -> shift_sub_equiv_sub_inc_no_rename #t #g s' e1 f
  | EApp e1 e2
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
  | ECall _ e1 -> shift_sub_equiv_sub_inc_rename #t s' e1 f
  | EApp e1 e2
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
  introduce forall fv. fv `FStar.List.Tot.memP` free_vars_indx e 0 ==> free_vars_indx (s fv) 0 == [] with begin
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
  | ECall _ e' -> lem_subst_id e'
  | EApp e1 e2 | EPair e1 e2 | EStringEq e1 e2 ->
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
  | ECall _ e1 -> subst_comp_ren_ren f g e1
  | EApp e1 e2 | EPair e1 e2 | EStringEq e1 e2 ->
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
  | ECall _ e1 -> subst_comp_ren r g e1
  | EApp e1 e2 | EPair e1 e2 | EStringEq e1 e2 ->
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
  | ECall _ e1 -> subst_comp_ren_right f g e1
  | EApp e1 e2 | EPair e1 e2 | EStringEq e1 e2 ->
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
  | ECall _ e1 -> subst_comp_general f g e1
  | EApp e1 e2 | EPair e1 e2 | EStringEq e1 e2 ->
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
  | ECall _ e' ->
    lem_subst_closed_identity s e' n
  | EApp e1 e2 | EPair e1 e2 | EStringEq e1 e2 ->
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
