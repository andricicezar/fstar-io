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


(* Small-step operational semantics; strong / full-beta reduction is
   non-deterministic, so necessarily as inductive relation *)

let is_value (e:exp) : bool = ELam? e || EUnit? e

val step : exp -> Tot (option exp)
let rec step e =
  match e with
  | EApp e1 e2 ->
      if is_value e1 then
        if is_value e2 then
          match e1 with
          | ELam t e' -> Some (subst (sub_beta e2) e')
          | _         -> None
        else
          match (step e2) with
          | Some e2' -> Some (EApp e1 e2')
          | None     -> None
      else
        (match (step e1) with
        | Some e1' -> Some (EApp e1' e2)
        | None     -> None)
  | _ -> None

type steps : exp -> exp -> Type =
| SRefl : e:exp -> steps e e
| STrans : #e0:exp ->
             #e2:exp ->
             squash (Some? (step e0)) ->
             steps (Some?.v (step e0)) e2 ->
             steps e0 e2

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
let safe (e:exp) : Type0 =
  forall e'. steps e e' ==> is_value e' \/ Some? (step e')

let irred (e:exp) : Type0 =
  None? (step e)

let rec wb_value (t:typ) (e:exp) : Tot (Type0) (decreases %[t;0]) =
  match t with
  | TUnit -> e == EUnit
  | TArr t1 t2 ->
      match e with
      | ELam t' e' ->
          t' == t1 /\
          (forall v. wb_value t1 v ==>
            wb_expr t2 (subst (sub_beta v) e'))
      | _ -> False
and wb_expr (t:typ) (e:exp) : Tot Type0 (decreases %[t;1]) =
  forall (e':exp). steps e e' ==> irred e' ==> wb_value t e'
(** definition of wb_expr is based on the fact that evaluation of expressions in the STLC
always terminates **)

(**
let wb_expr_lemma t (e:exp) (e':exp) :
  Lemma
    (requires (steps e e' /\ wb_expr t e'))
    (ensures (wb_expr t e)) =
  assert (wb_expr t e');
  assert (forall e''. steps e' e'' ==> irred e'' ==> wb_value t e'');
  assume (forall e'''. steps e e''' ==> irred e''' ==> wb_value t e''');
  admit ();
  ()
**)

(** substitution function for semantically well-typed expressions **)
let subfun (g:env) =
  s:(sub false){
    forall x. Some? (g x) ==> is_value (s x) /\ wb_value (Some?.v (g x)) (s x)
  }

let sub_beta_extend (v:exp{is_value v}) #b (s:sub b)
  : sub false
  = let f =
      fun (y:var) ->
        if y = 0 then v      (* substitute *)
        else s (y-1)         (* shift -1 *)
    in
    if not (EVar? v)
    then introduce exists (x:var). ~(EVar? (f x))
         with 0 and ();
    f

let subfun_extend (#g:env) (s:subfun g) (t:typ) (v:exp{wb_value t v}) : subfun (extend t g) =
  sub_beta_extend v s

unfold
let sem_typing (g:env) (e:exp) (t:typ) : Type0 =
  forall (s:subfun g). wb_expr t (subst s e)

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
