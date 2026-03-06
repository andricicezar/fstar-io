module QTypes.TypEnv

open FStar.Tactics
open FStar.Classical.Sugar

open LambdaIO

include QTypes

(** typ_env is a typing environment: variables to Quotable F* Types **)
type typ_env = var -> option qType
let empty : typ_env = fun _ -> None

(* we only need extend at 0 *)
let extend (t:qType) (g:typ_env)
  : typ_env
  = fun y -> if y = 0 then Some t
          else g (y-1)

let fv_in_env (g:typ_env) (e:exp) : Type0 =
  forall (fv:var). fv `FStar.List.Tot.memP` free_vars e ==> Some? (g fv)

let lem_no_fv_is_closed (e:exp) 
  : Lemma
    (requires fv_in_env empty e)
    (ensures is_closed e)
    [SMTPat (is_closed e)]
  = ()

let lem_closed_is_no_fv (e:exp)
  : Lemma
    (requires is_closed e)
    (ensures fv_in_env empty e)
    [SMTPat (is_closed e)]
  = ()

(** Helper: incrementing the binder depth shifts free variable indices by -1.
    I.e., fv in free_vars_indx at depth n+1 iff fv+1 in free_vars_indx at depth n. **)
let rec lem_free_vars_indx_shift (e:exp) (n:nat) :
  Lemma (ensures forall (fv:var). fv `FStar.List.Tot.memP` free_vars_indx e (n+1) <==> (fv+1) `FStar.List.Tot.memP` free_vars_indx e n)
        (decreases e) =
  let open FStar.List.Tot in
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
    (ensures forall (fv:var). (fv+1) `FStar.List.Tot.memP` free_vars_indx (subst s e) n <==> fv `FStar.List.Tot.memP` free_vars_indx e n)
    (decreases e) =
  let open FStar.List.Tot in
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
  = let open FStar.List.Tot in
    append_memP_forall (free_vars e1) (free_vars e2)

let lem_fv_in_env_if (g:typ_env) (e1 e2 e3:exp) :
  Lemma ((fv_in_env g e1 /\ fv_in_env g e2 /\ fv_in_env g e3) <==> fv_in_env g (EIf e1 e2 e3))
  = let open FStar.List.Tot in
    append_memP_forall (free_vars e1 @ free_vars e2) (free_vars e3);
    append_memP_forall (free_vars e1) (free_vars e2)

let lem_fv_in_env_pair (g:typ_env) (e1 e2:exp) :
  Lemma ((fv_in_env g e1 /\ fv_in_env g e2) <==> fv_in_env g (EPair e1 e2))
  = let open FStar.List.Tot in
    append_memP_forall (free_vars e1) (free_vars e2)

let lem_fv_in_env_string_eq (g:typ_env) (e1 e2:exp) :
  Lemma ((fv_in_env g e1 /\ fv_in_env g e2) <==> fv_in_env g (EStringEq e1 e2))
  = let open FStar.List.Tot in
    append_memP_forall (free_vars e1) (free_vars e2)

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
  let open FStar.List.Tot in
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
  = let open FStar.List.Tot in
    append_memP_forall (free_vars fd) (free_vars msg)

let lem_fv_in_env_close (g:typ_env) (fd:exp) :
  Lemma (fv_in_env g fd <==> fv_in_env g (EClose fd))
  = ()
