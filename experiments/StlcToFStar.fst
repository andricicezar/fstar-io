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

module StlcToFStar


open FStar.Tactics
open FStar.Constructive
open FStar.Classical
open FStar.FunctionalExtensionality
open FStar.StrongExcludedMiddle

(* Constructive-style progress and preservation proof for STLC with
   strong reduction, using deBruijn indices and parallel substitution. *)

type typ =
  | TArr  : typ -> typ -> typ
  | TUnit : typ

type var = nat

type exp =
  | EVar  : var -> exp
  | EApp  : exp -> exp -> exp
  | ELam  : typ -> exp -> exp
  | EUnit : exp

(* Parallel substitution operation `subst` *)

(* The termination argument uses a lexicographic ordering composed of:
   0) a bit saying whether the expression is a variable or not;
   1) an _undecidable_ well-founded order on substitutions that
      equates all renamings, equates all non-renamings, and makes
      renamings strictly smaller than non-renamings; we write down a
      non-constructive function is_renaming mapping substitutions
      (infinite objects) to 0 (renaming) or 1 (non-renaming)
   2) the structure of the expression e *)

type sub = var -> Tot exp

type renaming (s:sub) = (forall (x:var). EVar? (s x))

val is_renaming : s:sub -> GTot (n:int{  (renaming s  ==> n=0) /\
                                       (~(renaming s) ==> n=1)})
let is_renaming s = (if strong_excluded_middle (renaming s) then 0 else 1)


val sub_inc : var -> Tot exp
let sub_inc y = EVar (y+1)

val renaming_sub_inc : unit -> Lemma (renaming (sub_inc))
let renaming_sub_inc _ = ()

let is_var (e:exp) : int = if EVar? e then 0 else 1

val sub_elam: s:sub -> var -> Tot (e:exp{renaming s ==> EVar? e})
                                (decreases %[1;is_renaming s; 0; EVar 0])
val subst : s:sub -> e:exp -> Pure exp (requires True)
     (ensures (fun e' -> (renaming s /\ EVar? e) ==> EVar? e'))
     (decreases %[is_var e; is_renaming s; 1; e])
let rec subst s e =
  match e with
  | EVar x -> s x
  | ELam t e1 -> ELam t (subst (sub_elam s) e1)
  | EApp e1 e2 -> EApp (subst s e1) (subst s e2)
  | EUnit -> EUnit

and sub_elam s y = if y=0 then EVar y
                   else subst sub_inc (s (y-1))

val sub_beta : exp -> Tot sub
let sub_beta v = fun y -> if y = 0 then v      (* substitute *)
                          else (EVar (y-1))    (* shift -1 *)

(* Small-step operational semantics; strong / full-beta reduction is
   non-deterministic, so necessarily as inductive relation *)

type step : exp -> exp -> Type =
  | SBeta : t:typ ->
            e1:exp ->
            e2:exp ->
            step (EApp (ELam t e1) e2) (subst (sub_beta e2) e1)
  | SApp1 : #e1:exp ->
             e2:exp ->
            #e1':exp ->
            $hst:step e1 e1' ->
                 step (EApp e1 e2) (EApp e1' e2)
  | SApp2 :  e1:exp ->
            #e2:exp ->
            #e2':exp ->
            $hst:step e2 e2' ->
                 step (EApp e1 e2) (EApp e1 e2')

(* Type system; as inductive relation (not strictly necessary for STLC) *)

type env = var -> Tot (option typ)

val empty : env
let empty _ = None

(* we only need extend at 0 *)
val extend : typ -> env -> Tot env
let extend t g y = if y = 0 then Some t
                   else g (y-1)

noeq type typing : env -> exp -> typ -> Type =
  | TyVar : #g:env ->
             x:var{Some? (g x)} ->
             typing g (EVar x) (Some?.v (g x))
  | TyLam : #g :env ->
             t :typ ->
            #e1:exp ->
            #t':typ ->
            $hbody:typing (extend t g) e1 t' ->
                   typing g (ELam t e1) (TArr t t')
  | TyApp : #g:env ->
            #e1:exp ->
            #e2:exp ->
            #t11:typ ->
            #t12:typ ->
            $h1:typing g e1 (TArr t11 t12) ->
            $h2:typing g e2 t11 ->
                typing g (EApp e1 e2) t12
  | TyUnit : #g:env ->
             typing g EUnit TUnit

open FStar.Ghost
open Compiler.Languages

let rec typ_to_fstar (t:typ) (fl:erased tflag) (pi:policy_spec) (mst:mst) : Type =
  match t with
  | TArr t1 t2 -> (typ_to_fstar t1 fl pi mst) -> MIOpi (typ_to_fstar t2 fl pi mst) fl pi mst
  | TUnit -> FStar.Universe.raise_t unit


type venv (g:env) (fl:erased tflag) (pi:policy_spec) (mst:mst) = x:var{Some? (g x)} -> typ_to_fstar (Some?.v (g x)) fl pi mst

let vextend #t (x:typ_to_fstar t 'f 'p 'm) (#g:env) (ve:venv g 'f 'p 'm) : venv (extend t g) 'f 'p 'm =
  fun y -> if y = 0 then x else ve (y-1)

#push-options "--compat_pre_core 1"

let rec exp_to_fstar (g:env) (e:exp) (t:typ) (h:typing g e t) (ve:venv g 'f 'p 'm)
  : MIOpi (typ_to_fstar t 'f 'p 'm) 'f 'p 'm (decreases e) =
  match e with
  | EUnit -> FStar.Universe.raise_val ()
  | EVar x -> ve x
  | ELam t1 e1 -> 
       let TyLam _ #_ #t2 h1 = h in
       assert (t == TArr t1 t2);
       let w : typ_to_fstar t1 'f 'p 'm -> MIOpi (typ_to_fstar t2 'f 'p 'm) 'f 'p 'm =
         (fun x -> exp_to_fstar (extend t1 g) e1 t2 h1 (vextend x ve)) in
       assume (typ_to_fstar t 'f 'p 'm == (typ_to_fstar t1 'f 'p 'm -> MIOpi (typ_to_fstar t2 'f 'p 'm) 'f 'p 'm));
       w
  | EApp e1 e2 ->
       let TyApp #_ #_ #_ #t1 #t2 h1 h2 = h in
       assert ((typ_to_fstar t 'f 'p 'm) == (typ_to_fstar t2 'f 'p 'm));
       let v1 : typ_to_fstar (TArr t1 t2) 'f 'p 'm = exp_to_fstar g e1 (TArr t1 t2) h1 ve in
       let v2 : typ_to_fstar t1 'f 'p 'm = exp_to_fstar g e2 t1 h2 ve in
       assume (forall h lt1 lt2. enforced_locally 'p h lt1 /\ enforced_locally 'p (List.rev lt1 @ h) lt2 ==>
         enforced_locally 'p h (lt1@lt2));
       v1 v2
