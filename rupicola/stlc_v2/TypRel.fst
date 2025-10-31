module TypRel

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC

noeq
type rtyp : Type0 -> Type u#1 =
| RUnit : rtyp unit
| RBool : rtyp bool
| RArr : #s1:Type ->
         #s2:Type ->
         rtyp s1 ->
         rtyp s2 ->
         rtyp (s1 -> s2)
| RPair : #s1:Type ->
          #s2:Type ->
          rtyp s1 ->
          rtyp s2 ->
          rtyp (s1 & s2)

let test_match s (r:rtyp s) = (** why does this work so well? **)
  match r with
  | RUnit -> assert (s == unit)
  | RBool -> assert (s == bool)
  | RArr #s1 #s2 _ _ -> assert (s == (s1 -> s2))
  | RPair #s1 #s2 _ _ -> assert (s == (s1 & s2))

let rec rtype_to_ttype s (r:rtyp s) : typ =
  match r with
  | RUnit -> TUnit
  | RBool -> TBool
  | RArr #s1 #s2 rs1 rs2 -> TArr (rtype_to_ttype s1 rs1) (rtype_to_ttype s2 rs2)
  | RPair #s1 #s2 rs1 rs2 -> TPair (rtype_to_ttype s1 rs1) (rtype_to_ttype s2 rs2)

type typsr =
  s:Type & rtyp s

let get_Type (t:typsr) = t._1
let get_rel (t:typsr) = t._2

let mk_arrow (t1 t2:typsr) : typsr =
  (| _, RArr (get_rel t1) (get_rel t2) |)

let mk_pair (t1 t2:typsr) : typsr =
  (| _, RPair (get_rel t1) (get_rel t2) |)

(** Typing environment **)
type env = var -> option typsr

let empty : env = fun _ -> None

(* we only need extend at 0 *)
let extend (t:typsr) (g:env)
  : env
  = fun y -> if y = 0 then Some t
          else g (y-1)

let fv_in_env (g:env) (e:exp) : Type0 =
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

let lem_fv_in_env_lam (g:env) (t:typsr) (body:exp) :
  Lemma
    (requires fv_in_env (extend t g) body)
    (ensures  fv_in_env g (ELam body)) = admit ()

let lem_fv_in_env_app (g:env) (e1 e2:exp) :
  Lemma
    (requires fv_in_env g e1 /\ fv_in_env g e2)
    (ensures  fv_in_env g (EApp e1 e2)) = admit ()

let lem_app_fv_in_env (g:env) (e1 e2:exp) :
  Lemma
    (requires fv_in_env g (EApp e1 e2))
    (ensures fv_in_env g e1 /\ fv_in_env g e2) = admit ()

let lem_fv_in_env_if (g:env) (e1 e2 e3:exp) :
  Lemma
    (requires fv_in_env g e1 /\ fv_in_env g e2 /\ fv_in_env g e3)
    (ensures  fv_in_env g (EIf e1 e2 e3)) = admit ()

let lem_if_fv_in_env (g:env) (e1 e2 e3:exp) :
  Lemma
    (requires fv_in_env g (EIf e1 e2 e3))
    (ensures fv_in_env g e1 /\ fv_in_env g e2 /\ fv_in_env g e3) = admit ()

let lem_fv_in_env_pair (g:env) (e1 e2:exp) :
  Lemma
    (requires fv_in_env g e1 /\ fv_in_env g e2)
    (ensures  fv_in_env g (EPair e1 e2)) = admit ()

let lem_pair_fv_in_env (g:env) (e1 e2:exp) :
  Lemma 
    (requires fv_in_env g (EPair e1 e2))
    (ensures fv_in_env g e1 /\ fv_in_env g e2) = admit ()

let lem_fst_fv_in_env (g:env) (e:exp) : // this only makes sense because of how we defined free_vars_indx 
  Lemma
    (requires fv_in_env g (EFst e))
    (ensures fv_in_env g e) = admit ()

let lem_snd_fv_in_env (g:env) (e:exp) :
  Lemma 
    (requires fv_in_env g (ESnd e))
    (ensures fv_in_env g e) = admit ()

let lem_lam_fv_in_env (g:env) (body:exp) (t1:typsr) :
  Lemma
    (requires fv_in_env g (ELam body))
    (ensures fv_in_env (extend t1 g) body) = admit ()

(** STLC Evaluation Environment : variable -> value **)
let gsub (g:env) (b:bool{b ==> (forall x. None? (g x))}) = (** CA: this b is polluting **)
  s:(sub b){forall x. Some? (g x) ==> is_value (s x)}

let gsub_empty : gsub empty true =
  (fun v -> EVar v)

let gsub_extend (#g:env) #b (s:gsub g b) (t:typsr) (v:value) : gsub (extend t g) false =
  let f = fun (y:var) -> if y = 0 then v else s (y-1) in
  introduce exists (x:var). ~(EVar? (f x)) with 0 and ();
  f

let gsubst (#g:env) #b (s:gsub g b) (e:exp{fv_in_env g e}) : closed_exp =
  lem_subst_freevars_closes_exp s e 0;
  subst s e

let lem_substitution #g #b (s:gsub g b) (t:typsr) (v:value) (e:exp)
  : Lemma (
    (subst (sub_beta v) (subst (sub_elam s) e)) == (subst (gsub_extend s t v) e))
  = admit () (** common lemma **)

let lem_gsubst_closed_identiy #g #b (s:gsub g b) (e:closed_exp) :
  Lemma (gsubst s e == e)
  [SMTPat (gsubst s e)] =
  admit ()
