(*
   Copyright 2014-2015
     Simon Forest - Inria and ENS Paris
     Catalin Hritcu - Inria
     Nikhil Swamy - Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module STLC

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot
(* Constructive-style progress and preservation proof for STLC with
   strong reduction, using deBruijn indices and parallel substitution. *)

type typ =
  | TUnit : typ
  | TArr  : typ -> typ -> typ

let var = nat
type exp =
  | EUnit : exp
  | EVar  : v:var -> exp
  | ELam  : typ -> exp -> exp
  | EApp  : exp -> exp -> exp

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
    | ELam t e1 -> ELam t (subst (sub_elam s) e1)
    | EApp e1 e2 -> EApp (subst s e1) (subst s e2)
    | EUnit -> EUnit

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

(* Type system; as inductive relation (not strictly necessary for STLC) *)

type env = var -> option typ

let empty : env = fun _ -> None

(* we only need extend at 0 *)
let extend (t:typ) (g:env)
  : env
  = fun y -> if y = 0 then Some t
          else g (y-1)

noeq
type typing : env -> exp -> typ -> Type =
  | TyUnit : #g:env ->
             typing g EUnit TUnit

  | TyVar : #g:env ->
             x:var{Some? (g x)} ->
             typing g (EVar x) (Some?.v (g x))

  | TyLam : #g :env ->
            t:typ ->
            #e1:exp ->
            #t':typ ->
            hbody:typing (extend t g) e1 t' ->
            typing g (ELam t e1) (TArr t t')

  | TyApp : #g:env ->
            #e1:exp ->
            #e2:exp ->
            #t1:typ ->
            #t2:typ ->
            h1:typing g e1 (TArr t1 t2) ->
            h2:typing g e2 t1 ->
            typing g (EApp e1 e2) t2


(** Semantic type soundness *)
let rec free_vars_indx (e:exp) (n:nat) : list var = // n is the number of binders
  match e with
  | EUnit -> []
  | ELam _ e' -> free_vars_indx e' (n+1)
  | EApp e1 e2 -> free_vars_indx e1 n @ free_vars_indx e2 n
  | EVar i -> if i < n then [] else [i-n]

let free_vars e = free_vars_indx e 0

let is_closed (e:exp) : bool =
  free_vars e = []

let is_value (e:exp) : Type0 =
  match e with
  | EUnit -> True
  | ELam _ _ -> is_closed e
  | _ -> False

type value = e:exp{is_value e}
type closed_exp = e:exp{is_closed e}

let fv_in_env (g:env) (e:exp) : Type0 =
  forall (fv:var). fv `memP` free_vars e <==> Some? (g fv)

let rec lem_shifting_preserves_closed (s:sub true) (e:exp) (n:nat) :
  Lemma
    (requires (free_vars_indx e n == [] /\
               (forall (x:var). EVar?.v (s x) <= x+1)))
    (ensures (free_vars_indx (subst s e) (n+1) == []))
    (decreases e) =
  match e with
  | EApp e1 e2 ->
    lem_shifting_preserves_closed s e1 n;
    lem_shifting_preserves_closed s e2 n
  | ELam t e' -> begin
    assert (free_vars_indx e' (n+1) == []);
    let s' : sub true = sub_elam s in
    assert (forall (x:var). EVar?.v (s' x) <= x+1);
    lem_shifting_preserves_closed s' e' (n+1);
    assert (free_vars_indx (subst s' e') (n+2) == []);
    assert (free_vars_indx (subst s' e') (n+2) ==
            free_vars_indx (subst s (ELam t e')) (n+1))
  end
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
  | EApp e1 e2 ->
    assume (forall x. x `memP` free_vars_indx e1 n ==> x `memP` free_vars_indx e n);(** should be easy **)
    lem_subst_freevars_closes_exp s e1 n;
    assume (forall x. x `memP` free_vars_indx e2 n ==> x `memP` free_vars_indx e n);(** should be easy **)
    lem_subst_freevars_closes_exp s e2 n
  | ELam t e' ->
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
  | _ -> ()

(* Small-step operational semantics; strong / full-beta reduction is
   non-deterministic, so necessarily as inductive relation *)

let subst_beta (t:typ) (v e:exp) :
  Pure closed_exp
    (requires (is_closed (ELam t e) /\ is_closed v))
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
            | ELam t e' -> begin
              Some (subst_beta t e2 e')
            end
            | _ -> None
          end
      end
  end
  | _ -> None

let can_step (e:closed_exp) : Type0 =
  Some? (step e)

let irred (e:closed_exp) : Type0 =
  None? (step e)

(** reflexive transitive closure of step *)
type steps : closed_exp -> closed_exp -> Type =
| SRefl  : e:closed_exp -> 
           squash (irred e) -> 
           steps e e
| STrans : #e0:closed_exp ->
           #e2:closed_exp ->
           squash (Some? (step e0)) ->
           steps (Some?.v (step e0)) e2 ->
           steps e0 e2

let safe (e:closed_exp) : Type0 =
  forall e'. steps e e' ==> is_value e' \/ can_step e'

(** CA: should e be a value? **)
let rec (∈) (e:closed_exp) (t:typ) : Tot Type0 (decreases %[t;0]) =
  match t with
  | TUnit -> e == EUnit
  | TArr t1 t2 ->
      match e with
      | ELam t' e' ->
          t' == t1 /\
          (forall (v:value). v ∈ t1 ==> subst_beta t' v e' ⋮ t2)
      | _ -> False
and (⋮) (e:closed_exp) (t:typ) : Tot Type0 (decreases %[t;1]) =
  forall (e':closed_exp). steps e e' ==> irred e' ==> e' ∈ t
(** definition of wb_expr is based on the fact that evaluation of expressions in the STLC
always terminates **)

let lem_value_is_typed_exp e t : Lemma (e ∈ t ==> e ⋮ t) = admit ()

(** ground substitution / value environment **)
let gsub (g:env) (b:bool{b ==> (forall x. None? (g x))}) = (** CA: this b is polluting **)
  s:(sub b){forall x. Some? (g x) ==> is_value (s x) /\ (s x) ∈ (Some?.v (g x))}
 // x:var{Some? (g x)} -> v:value{wb_value (Some?.v (g x)) v}

let gsub_empty : gsub empty true =
  (fun v -> EVar v)

let gsub_extend (#g:env) #b (s:gsub g b) (t:typ) (v:value{v ∈ t}) : gsub (extend t g) false =
  let f = fun (y:var) -> if y = 0 then v else s (y-1) in
  introduce exists (x:var). ~(EVar? (f x)) with 0 and ();
  f

let gsubst (#g:env) #b (s:gsub g b) (e:exp{fv_in_env g e}) : closed_exp =
 // let s : sub (is_closed e) = (fun x -> if Some? (g x) then gs x else EVar x) in
  lem_subst_freevars_closes_exp s e 0;
  subst s e

let substitution_lemma #g #b (s:gsub g b) (t:typ) (v:value{v ∈ t}) (e:exp) : Lemma
  ((subst (sub_beta v) (subst (sub_elam s) e)) == (subst (gsub_extend s t v) e)) = admit ()

let e_gsub_empty (e:closed_exp) :
  Lemma (gsubst gsub_empty e == e)
  [SMTPat (gsubst gsub_empty e)] =
  admit ()

let sem_typing (g:env) (e:exp) (t:typ) : Type0 =
  fv_in_env g e /\
  (forall b (s:gsub g b). (gsubst s e) ⋮ t)

let safety (e:closed_exp) (t:typ) : Lemma
  (requires sem_typing empty e t)
  (ensures safe e) =
  introduce forall e'. steps e e' ==> is_value e' \/ Some? (step e') with begin
    introduce steps e e' ==> is_value e' \/ Some? (step e') with _. begin
      introduce irred e' ==> is_value e' with _. begin
        eliminate forall b (s: gsub empty b). (gsubst s e) ⋮ t with true gsub_empty;
        assert (e' ∈ t)
      end
    end
  end

let rec lem_helper t1
  (e1:closed_exp)
  (e2:closed_exp)
  (e':closed_exp)
  (st:steps (EApp e1 e2) e') :
  Pure (exp * closed_exp)
    (requires irred e')
    (ensures fun (e11, e2') ->
      is_closed (ELam t1 e11) /\ irred (ELam t1 e11) /\
      irred e2' /\
      steps e1 (ELam t1 e11) /\
      steps e2 e2' /\
      steps (EApp e1 e2) (subst_beta t1 e2' e11) /\
      steps (subst_beta t1 e2' e11) e')
    (decreases st)
  = 
  match st with
  | SRefl _ _ -> begin
    assume (ELam? e1); (** how to prove this? **)
    let ELam _ e11 = e1 in
    let e2' = e2 in
    (e11, e2')
  end
  | STrans #e0 #e2 () st12 -> begin
    admit ()
    // e0 == (gsubst s (EApp e1 e2))
    // e2 == e'
  end

let rec fundamental_property_of_logical_relations (#g:env) (#e:exp) (#t:typ) (ht:typing g e t)
  : Lemma
    (requires (fv_in_env g e))
    (ensures sem_typing g e t)
  =
  match ht with
  | TyUnit -> assert (sem_typing g e t) by (explode ())
  | TyVar _ -> assert (sem_typing g e t) by (explode ())
  | TyLam t1 #body #t2 hbody -> begin
    introduce forall b (s:gsub g b). gsubst s (ELam t1 body) ⋮ TArr t1 t2 with begin
      let g' = extend t1 g in
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam t1 body) == ELam t1 body');
      introduce forall (v:value). v ∈ t1 ==>  subst_beta t1 v body' ⋮ t2 with begin
        introduce _ ==> _ with _. begin
          assume (fv_in_env g' body); (** should be easy to prove **)
          fundamental_property_of_logical_relations hbody;
          assert (sem_typing g' body t2);
          eliminate forall b (s:gsub g' b). (gsubst s body) ⋮ t2 with false (gsub_extend s t1 v);
          assert (gsubst (gsub_extend s t1 v) body ⋮ t2);
          substitution_lemma s t1 v body;
          assert (subst_beta t1 v body' ⋮ t2)
        end
      end;
      assert (gsubst s (ELam t1 body) ∈ TArr t1 t2);
      lem_value_is_typed_exp (gsubst s (ELam t1 body)) (TArr t1 t2)
    end
  end
  | TyApp #_ #e1 #e2 #t1 #t2 h1 h2 ->
    introduce forall b (s:gsub g b). gsubst s (EApp e1 e2) ⋮ t2 with begin
      introduce forall e'. steps (gsubst s (EApp e1 e2)) e' /\ irred e' ==> e' ∈ t2 with begin
        introduce _ ==> e' ∈ t2 with h. begin
          assume (fv_in_env g e1); (** should be easy to prove **)
          assume (fv_in_env g e2); (** should be easy to prove **)
          let steps_e_e' : squash (steps (EApp (gsubst s e1) (gsubst s e2)) e') = () in
          FStar.Squash.map_squash #_ #(squash (e' ∈ t2)) steps_e_e' (fun steps_e_e' ->
            assume (is_closed e1); (** should be easy to prove **)
            assume (is_closed e2); (** should be easy to prove **)
            let (e11, e2') = lem_helper t1 (gsubst s e1) (gsubst s e2) e' steps_e_e' in
            fundamental_property_of_logical_relations h1;
            assert (ELam t1 e11 ∈ TArr t1 t2);
            fundamental_property_of_logical_relations h2;
            assert (e2' ∈ t1);
            assert (subst_beta t1 e2' e11 ⋮ t2);
            assert (e' ∈ t2)
          )
        end
      end
    end