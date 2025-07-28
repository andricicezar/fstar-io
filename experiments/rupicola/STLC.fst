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
  | EVar  : var -> exp
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
let rec free_vars_indx (e:exp) (n:nat) : list var =
  match e with
  | EUnit -> []
  | ELam _ e' -> free_vars_indx e' (n+1)
  | EApp e1 e2 -> free_vars_indx e1 n @ free_vars_indx e2 n
  | EVar i -> if i < n then [] else [i]

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

(* Small-step operational semantics; strong / full-beta reduction is
   non-deterministic, so necessarily as inductive relation *)

let lem_subst_preserves_is_closed (t:typ) (e v:exp) :
  Lemma
    (requires (is_closed (ELam t e) /\ is_closed v))
    (ensures (is_closed (subst (sub_beta v) e))) = admit ()

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
              lem_subst_preserves_is_closed t e' e2;
              Some (subst (sub_beta e2) e')
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
| SRefl  : e:closed_exp -> steps e e
| STrans : #e0:closed_exp ->
           #e2:closed_exp ->
           squash (Some? (step e0)) ->
           steps (Some?.v (step e0)) e2 ->
           steps e0 e2

let safe (e:closed_exp) : Type0 =
  forall e'. steps e e' ==> is_value e' \/ can_step e'

let rec wb_value (t:typ) (e:closed_exp) : Tot Type0 (decreases %[t;0]) =
  match t with
  | TUnit -> e == EUnit
  | TArr t1 t2 ->
      match e with
      | ELam t' e' ->
          t' == t1 /\
          (forall (v:value). wb_value t1 v ==>
            (lem_subst_preserves_is_closed t' e' v;
            wb_expr t2 (subst (sub_beta v) e')))
      | _ -> False
and wb_expr (t:typ) (e:closed_exp) : Tot Type0 (decreases %[t;1]) =
  forall (e':closed_exp). steps e e' ==> irred e' ==>
    wb_value t e'
(** definition of wb_expr is based on the fact that evaluation of expressions in the STLC
always terminates **)

(** ground substitution / value environment **)
let gsub (g:env) =
  x:var{Some? (g x)} -> v:value{wb_value (Some?.v (g x)) v}

let gsub_empty : gsub empty =
  (fun v -> assert False; EVar v)

let subfun_extend (#g:env) (s:gsub g) (t:typ) (v:value{wb_value t v}) : gsub (extend t g) =
  fun y -> if y = 0 then v else s (y-1)

let lem_gsubst_closes_exp (#g:env) (s:gsub g) (e:exp) :
  Lemma
    (requires ((forall fv. fv `mem` free_vars e ==> Some? (g fv)) /\
               (exists x. Some? (g x))))
    (ensures (is_closed (subst #false (fun x -> if Some? (g x) then s x else EVar x) e))) = admit ()

let gsubst (#g:env) (s:gsub g) (e:exp)
  : Pure closed_exp
    (requires (forall (fv:var). fv `memP` free_vars e ==> Some? (g fv)))
    (ensures (fun _ -> True)) =
  if is_closed e then e
  else begin
    lem_gsubst_closes_exp s e;
    subst #false (fun x -> if Some? (g x) then s x else EVar x) e
  end

let e_gsub_empty (e:closed_exp) :
  Lemma (gsubst gsub_empty e == e)
  [SMTPat (gsubst gsub_empty e)] =
  ()

unfold
let sem_typing (g:env) (e:exp) (t:typ) : Type0 =
  (forall fv. fv `mem` free_vars e ==> Some? (g fv)) /\
  (forall (s:gsub g). wb_expr t (gsubst s e))

let safety (e:exp) (t:typ) : Lemma
  (requires sem_typing empty e t)
  (ensures safe e) =
  introduce forall e'. steps e e' ==> is_value e' \/ Some? (step e') with begin
    introduce steps e e' ==> is_value e' \/ Some? (step e') with _. begin
      introduce irred e' ==> is_value e' with _. begin
        assert (forall (s: gsub empty). (forall (e':exp). steps (gsubst s e) e' ==> irred e' ==> wb_value t e'));
        eliminate forall (s: gsub empty). (forall (e':exp). steps (gsubst s e) e' ==> irred e' ==> wb_value t e') with gsub_empty;
        assert (wb_value t e');
        admit ()
      end
    end
  end

let substitution_lemma #g (s:subfun g) t1 v body : Lemma
  ((subst (sub_beta v) (subst (sub_elam s) body)) ==
   (subst (subfun_extend s t1 v) body)) = admit ()

let rec fundamental_property_of_logical_relations (#g:env) (#e:exp) (#t:typ) (ht:typing g e t)
  : Lemma (sem_typing g e t)
  = match ht with
  | TyUnit ->
    assert (e == EUnit);
    assert (sem_typing g e t) by (explode ())
  | TyVar x ->
    assert (e == EVar x);
    assert (sem_typing g e t) by (explode ())
  | TyLam t1 #_ #t2 hbody ->
    let (ELam _ body) = e in
    fundamental_property_of_logical_relations hbody;
    introduce forall (s:subfun g). wb_expr t (subst s (ELam t1 body)) with begin
      assert (wb_expr t (subst s (ELam t1 body)) <==> wb_expr t (ELam t1 (subst (sub_elam s) body)));
      assume ( (** CA: refl **)
        wb_value t (ELam t1 (subst (sub_elam s) body)) ==>
        wb_expr t (ELam t1 (subst (sub_elam s) body)));
      introduce forall v. wb_value t1 v ==>  wb_expr t2 (subst (sub_beta v) (subst (sub_elam s) body)) with begin
        introduce _ ==> _ with _. begin
          substitution_lemma s t1 v body
        end
      end
    end
  | TyApp #_ #e1 #e2 #t1 h1 h2 ->
    introduce forall (s:subfun g). wb_expr t (subst s (EApp e1 e2)) with begin
      assert (wb_expr t (subst s (EApp e1 e2)) <==> wb_expr t (EApp (subst s e1) (subst s e2)));
      match h1 with
      | TyLam _ #body hbody -> begin
        assert (wb_expr t (EApp (subst s (ELam t1 body)) (subst s e2)) <==>
                wb_expr t (EApp (ELam t1 (subst (sub_elam s) body)) (subst s e2)));
        assume ((** CA: no idea if correct, this is just taking a step. Progress and preservation? **)
          wb_expr t (EApp (ELam t1 (subst (sub_elam s) body)) (subst s e2)) <==>
          wb_expr t (subst (sub_beta (subst s e2)) (subst (sub_elam s) body)));
        assume (wb_value t1 (subst s e2)); (** CA: for this to be true, one would have to step the value too **)
        substitution_lemma s t1 (subst s e2) body;
        fundamental_property_of_logical_relations hbody;
        assert (wb_expr t (subst (subfun_extend s t1 (subst s e2)) body))
      end
      | _ -> begin
        (** CA: I would like to call progress and preservation
                and recursively call this lemma **)
        admit ()
      end
    end
