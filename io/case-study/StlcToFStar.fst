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
  | TArr    : typ -> typ -> typ
  | TSum    : typ -> typ -> typ
  | TPair   : typ -> typ -> typ
  | TUnit   : typ
  | TNat    : typ
  | TByte   : typ
  | TBytes  : typ
  | TExn    : typ
  | TFDesc  : typ
  | TString : typ

type var = nat

open FStar.Bytes

type exp =
  | EVar         : var -> exp
  | EApp         : exp -> exp -> exp
  | ELam         : typ -> exp -> exp
  | EUnit        : exp
  | EZero        : exp
  | ESucc        : exp -> exp
  | ENRec        : exp -> exp -> exp -> exp
  | EInl         : exp -> exp
  | EInr         : exp -> exp
  | ECase        : exp -> exp -> exp -> exp
  | EByteLit     : byte -> exp
  | EBytesCreate : exp -> exp -> exp
  | EFst         : exp -> exp
  | ESnd         : exp -> exp
  | EPair        : exp -> exp -> exp
  | EStringLit   : string -> exp

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
  | EZero -> EZero
  | ESucc e -> ESucc (subst s e)
  | ENRec e1 e2 e3 -> ENRec (subst s e1) (subst s e2) (subst s e3)
  | EInl e -> EInl e
  | EInr e -> EInr e
  | ECase e1 e2 e3 -> ECase (subst s e1) (subst s e2) (subst s e3)
  | EByteLit b -> EByteLit b
  | EBytesCreate e1 e2 -> EBytesCreate (subst s e1) (subst s e2)
  | EFst e -> EFst (subst s e)
  | ESnd e -> ESnd (subst s e)
  | EPair e1 e2 -> EPair (subst s e1) (subst s e2)
  | EStringLit s -> EStringLit s

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
  | SSucc :  e:exp ->
            #e':exp ->
            $hst:step e e' ->
                 step (ESucc e) (ESucc e')
  | SInl  :  e:exp ->
            #e':exp ->
            $hst:step e e' ->
                 step (EInl e) (EInl e')
  | SInr  :  e:exp ->
            #e':exp ->
            $hst:step e e' ->
                 step (EInr e) (EInr e')


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
  | TyZero : #g:env ->
             typing g EZero TNat
  | TySucc : #g:env ->
             #e:exp ->
             $h1:typing g e TNat ->
                 typing g (ESucc e) TNat
  | TyNRec : #g:env ->
             #e1:exp ->
             #e2:exp ->
             #e3:exp ->
             #t1:typ ->
             $h1:typing g e1 TNat ->
             $h2:typing g e2 t1 ->
             $h3:typing g e3 (TArr t1 t1) ->
                 typing g (ENRec e1 e2 e3) t1
  | TyInl  : #g:env ->
             #e:exp ->
             #t1:typ ->
             #t2:typ ->
             $h1:typing g e t1 ->
                 typing g (EInl e) (TSum t1 t2)
  | TyInr  : #g:env ->
             #e:exp ->
             #t1:typ ->
             #t2:typ ->
             $h1:typing g e t2 ->
                 typing g (EInr e) (TSum t1 t2)
  | TyCase : #g:env ->
             #e1:exp ->
             #e2:exp ->
             #e3:exp ->
             #t1:typ ->
             #t2:typ ->
             #t3:typ ->
             $h1:typing g e1 (TSum t1 t2) ->
             $h2:typing g e2 (TArr t1 t3) ->
             $h3:typing g e3 (TArr t2 t3) ->
                 typing g (ECase e1 e2 e3) t3
  | TyByteLit : #g:env ->
                #b:byte ->
                   typing g (EByteLit b) TByte
  | TyBytesCreate : #g:env ->
                    #e1:exp ->
                    #e2:exp ->
                    $h1:typing g e1 TNat ->
                    $h2:typing g e2 TByte ->
                        typing g (EBytesCreate e1 e2) TBytes
  | TyFst         : #g:env ->
                    #e:exp ->
                    #t1:typ ->
                    #t2:typ ->
                    $h1:typing g e (TPair t1 t2) ->
                        typing g (EFst e) t1
  | TySnd         : #g:env ->
                    #e:exp ->
                    #t1:typ ->
                    #t2:typ ->
                    $h1:typing g e (TPair t1 t2) ->
                        typing g (ESnd e) t2
  | TyPair        : #g:env ->
                    #e1:exp ->
                    #e2:exp ->
                    #t1:typ ->
                    #t2:typ ->
                    $h1:typing g e1 t1 ->
                    $h2:typing g e2 t2 ->
                        typing g (EPair e1 e2) (TPair t1 t2)
  | TyStringLit   : #g:env ->
                    #s:string ->
                       typing g (EStringLit s) TString

open FStar.Ghost
open FStar.UInt32
let convert (n : nat) : u32 = if n < 65535 then (uint_to_t n <: u32) else 0ul

open Compiler.Languages

let rec typ_to_fstar (t:typ) (fl:erased tflag) (pi:policy_spec) (mst:mst) : Type =
  match t with
  | TArr t1 t2 -> (typ_to_fstar t1 fl pi mst) -> MIOpi (typ_to_fstar t2 fl pi mst) fl pi mst
  | TUnit -> FStar.Universe.raise_t unit
  | TNat -> FStar.Universe.raise_t nat
  | TSum t1 t2 -> either (typ_to_fstar t1 fl pi mst) (typ_to_fstar t2 fl pi mst)
  | TPair t1 t2 -> (typ_to_fstar t1 fl pi mst) * (typ_to_fstar t2 fl pi mst)
  | TByte -> FStar.Universe.raise_t byte
  | TBytes -> FStar.Universe.raise_t bytes
  | TExn -> FStar.Universe.raise_t exn
  | TFDesc -> FStar.Universe.raise_t file_descr
  | TString -> FStar.Universe.raise_t string


type venv (g:env) (fl:erased tflag) (pi:policy_spec) (mst:mst) = x:var{Some? (g x)} -> typ_to_fstar (Some?.v (g x)) fl pi mst

let vempty #f #p #m : venv empty f p m = fun _ -> assert false

let vextend #t (x:typ_to_fstar t 'f 'p 'm) (#g:env) (ve:venv g 'f 'p 'm) : venv (extend t g) 'f 'p 'm =
  fun y -> if y = 0 then x else ve (y-1)

#push-options "--compat_pre_core 1"

let cast_TArr #t1 #t2 #f #p #m (h : (typ_to_fstar t1 f p m -> MIOpi (typ_to_fstar t2 f p m) f p m)) : typ_to_fstar (TArr t1 t2) f p m = h
let rec enforced_locally_compose 'p : Lemma (ensures (forall h lt1 lt2. enforced_locally 'p h lt1 /\ enforced_locally 'p (List.rev lt1 @ h) lt2 ==>
         enforced_locally 'p h (lt1@lt2))) = admit ()

let rec exp_to_fstar (g:env) (e:exp) (t:typ) (h:typing g e t) (ve:venv g 'f 'p 'm)
  : MIOpi (typ_to_fstar t 'f 'p 'm) 'f 'p 'm (decreases e) =
  let _ = enforced_locally_compose 'p in
  match e with
  | EUnit -> FStar.Universe.raise_val ()
  | EZero ->
       let zero : nat = 0 in
       FStar.Universe.raise_val zero
  | ESucc e ->
       let TySucc h1 = h in
       assert (t == TNat);
       let v = exp_to_fstar g e TNat h1 ve in
       v
  | ENRec e1 e2 e3 ->
       let TyNRec h1 h2 h3 = h in
       let v1 = exp_to_fstar g e1 TNat h1 ve in
       let v2 : typ_to_fstar t 'f 'p 'm = exp_to_fstar g e2 t h2 ve in
       let v3 : typ_to_fstar (TArr t t) 'f 'p 'm = exp_to_fstar g e3 (TArr t t) h3 ve in
       let rec f (n : nat) : MIOpi (typ_to_fstar t 'f 'p 'm) 'f 'p 'm =
         if n = 0 then v2 else f (n - 1) in
       f (FStar.Universe.downgrade_val v1)
  | EInl e ->
       let TyInl #_ #_ #t1 #t2 h1 = h in
       let v = exp_to_fstar g e t1 h1 ve in
       Inl #(typ_to_fstar t1 'f 'p 'm) #(typ_to_fstar t2 'f 'p 'm) v
  | EInr e ->
       let TyInr #_ #_ #t1 #t2 h1 = h in
       let v = exp_to_fstar g e t2 h1 ve in
       Inr #(typ_to_fstar t1 'f 'p 'm) #(typ_to_fstar t2 'f 'p 'm) v
  | ECase e1 e2 e3 ->
       let TyCase #_ #_ #_ #_ #t1 #t2 #t3 h1 h2 h3 = h in
       let v1 = exp_to_fstar g e1 (TSum t1 t2) h1 ve in
       let v2 = exp_to_fstar g e2 (TArr t1 t3) h2 ve in
       let v3 = exp_to_fstar g e3 (TArr t2 t3) h3 ve in
       (match v1 with | Inl x -> v2 x | Inr y -> v3 y)
  | EVar x -> ve x
  | ELam t1 e1 ->
       let TyLam t1' #_ #t2 h1 = h in
       assert (t1' == t1);
       assert (t == TArr t1 t2);
       let w : typ_to_fstar t1 'f 'p 'm -> MIOpi (typ_to_fstar t2 'f 'p 'm) 'f 'p 'm =
         (fun x -> exp_to_fstar (extend t1 g) e1 t2 h1 (vextend x ve)) in
       cast_TArr w
  | EApp e1 e2 ->
       let TyApp #_ #_ #_ #t1 #t2 h1 h2 = h in
       assert ((typ_to_fstar t 'f 'p 'm) == (typ_to_fstar t2 'f 'p 'm));
       (* Should we change the order here, first evaluate argument? *)
       let v1 : typ_to_fstar (TArr t1 t2) 'f 'p 'm = exp_to_fstar g e1 (TArr t1 t2) h1 ve in
       let v2 : typ_to_fstar t1 'f 'p 'm = exp_to_fstar g e2 t1 h2 ve in
       v1 v2
  | EByteLit b ->
       FStar.Universe.raise_val b
  | EBytesCreate e1 e2 ->
       let TyBytesCreate h1 h2 = h in
       let v1 : typ_to_fstar TNat 'f 'p 'm = exp_to_fstar g e1 TNat h1 ve in
       let v2 : typ_to_fstar TByte 'f 'p 'm = exp_to_fstar g e2 TByte h2 ve in
       let b : bytes = Bytes.create (convert (FStar.Universe.downgrade_val v1)) (FStar.Universe.downgrade_val v2) in
       FStar.Universe.raise_val b
  | EFst e ->
       let TyFst #_ #_ #t1 #t2 h1 = h in
       let v = exp_to_fstar g e (TPair t1 t2) h1 ve in
       fst #(typ_to_fstar t1 'f 'p 'm) #(typ_to_fstar t2 'f 'p 'm) v
  | ESnd e ->
       let TySnd #_ #_ #t1 #t2 h1 = h in
       let v = exp_to_fstar g e (TPair t1 t2) h1 ve in
       snd #(typ_to_fstar t1 'f 'p 'm) #(typ_to_fstar t2 'f 'p 'm) v
  | EPair e1 e2 ->
       let TyPair #_ #_ #_ #t1 #t2 h1 h2 = h in
       let v1 = exp_to_fstar g e1 t1 h1 ve in
       let v2 = exp_to_fstar g e2 t2 h2 ve in
       (v1, v2)
  | EStringLit s ->
       FStar.Universe.raise_val s


open Compiler.Model1

open Utils

open WebServer

let tgt_cs_int = comp.comp_int cs_int

type tgt_handler = ctx_tgt tgt_cs_int

let handler_env =
  extend (TArr TString (TSum TFDesc TExn)) (extend (TArr TUnit (TSum TFDesc TExn)) (extend TFDesc (extend (TArr (TPair TFDesc TBytes) (TSum TUnit TExn)) (extend (TArr TBytes (TSum TUnit TExn)) (extend TBytes empty)))))

let v_openfile = 0
let v_socket = 1
let v_client = 2
let v_write = 3
let v_send = 4
let v_req = 5

let e_openfile = EVar v_openfile
let e_socket = EVar v_socket
let e_client = EVar v_client
let e_write = EVar v_write
let e_send = EVar v_send
let e_req = EVar v_req

let ty_openfile = TyVar #handler_env v_openfile
let ty_socket = TyVar #handler_env v_socket
let ty_client = TyVar #handler_env v_client
let ty_write = TyVar #handler_env v_write
let ty_send = TyVar #handler_env v_send
let ty_req = TyVar #handler_env v_req

let wrap_handler (e:exp) (h:typing handler_env e (TSum TUnit TExn)) : tgt_handler =
 fun #fl sec_io (client : int) (req : Bytes.bytes) (send : Bytes.bytes -> MIOpi (either unit exn) fl pi _) ->
   let client : FStar.Universe.raise_t file_descr = FStar.Universe.raise_val client in
   let write : FStar.Universe.raise_t file_descr * FStar.Universe.raise_t bytes -> MIOpi (either (FStar.Universe.raise_t unit) (FStar.Universe.raise_t exn)) fl pi _ = fun fdb ->
     let fd = FStar.Universe.downgrade_val (fst fdb) in
     let b = FStar.Universe.downgrade_val (snd fdb) in
     match sec_io Write (fd, b) with
     | Inl unit -> Inl (FStar.Universe.raise_val unit)
     | Inr ex -> Inr (FStar.Universe.raise_val ex) in
   let socket : FStar.Universe.raise_t unit -> MIOpi (either (FStar.Universe.raise_t file_descr) (FStar.Universe.raise_t exn)) fl pi _ = fun _u ->
     match sec_io Socket () with
     | Inl fd -> Inl (FStar.Universe.raise_val fd)
     | Inr ex -> Inr (FStar.Universe.raise_val ex) in
   let openfile : FStar.Universe.raise_t string -> MIOpi (either (FStar.Universe.raise_t file_descr) (FStar.Universe.raise_t exn)) fl pi _ = fun s ->
     let s = FStar.Universe.downgrade_val s in
     match sec_io Openfile (s, [O_RDWR], 0x650) with
     | Inl fd -> Inl (FStar.Universe.raise_val fd)
     | Inr ex -> Inr (FStar.Universe.raise_val ex) in
   let send : FStar.Universe.raise_t bytes -> MIOpi (either (FStar.Universe.raise_t unit) (FStar.Universe.raise_t exn)) fl pi _ = fun b -> match send (FStar.Universe.downgrade_val b) with
     | Inl unit -> Inl (FStar.Universe.raise_val unit)
     | Inr ex -> Inr (FStar.Universe.raise_val ex) in
   let req : FStar.Universe.raise_t bytes = FStar.Universe.raise_val req in
   let handler_venv = vextend #fl #mymst #pi #_ openfile (vextend #fl #mymst #pi #_ socket (vextend #fl #mymst #pi #TFDesc client (vextend #fl #mymst #pi #(TArr (TPair TFDesc TBytes) (TSum TUnit TExn)) write (vextend #fl #mymst #pi #(TArr TBytes (TSum TUnit TExn)) send (vextend #fl #mymst #pi #TBytes req (vempty #fl #pi #mymst)))))) in
   let v = exp_to_fstar handler_env e (TSum TUnit TExn) h handler_venv in
   match v with
   | Inl v -> Inl (FStar.Universe.downgrade_val v)
   | Inr w -> Inr (FStar.Universe.downgrade_val w)

let rec e_nat (n : nat) =
  if n = 0 then EZero else ESucc (e_nat (n - 1))
let rec ty_nat #env (n : nat) : typing env (e_nat n) TNat =
  if n = 0 then TyZero else TySucc (ty_nat #env (n - 1))


let e_let_in (t : typ) (rhs : exp) (result : exp) =
  EApp (ELam t result) rhs
let ty_let_in #env (t : typ) (u : typ) (#rhs : exp) (#result : exp) (ty_rhs : typing env rhs t) (ty_result : typing (extend t env) result u) : typing env (e_let_in t rhs result) u =
  TyApp (TyLam t ty_result) ty_rhs

(* Some handlers from Adversarialhandlers.fst *)

let handler1 : tgt_handler =
  let e : exp = EInl EUnit in
  let h : typing handler_env e (TSum TUnit TExn) = TyInl TyUnit in
  wrap_handler e h

let handler2 : tgt_handler =
  let e : exp = EApp e_send (EBytesCreate (e_nat 501) (EByteLit 10uy)) in
  let h : typing handler_env e (TSum TUnit TExn) = TyApp ty_send (TyBytesCreate (ty_nat 501) (TyByteLit #_ #10uy)) in
  wrap_handler e h

let handler3 : tgt_handler =
  let e : exp = e_let_in (TSum TFDesc TExn) (EApp e_openfile (EStringLit "/etc/passwd")) (EInl EUnit) in
  let h : typing handler_env e (TSum TUnit TExn) = ty_let_in (TSum TFDesc TExn) (TSum TUnit TExn) (TyApp ty_openfile (TyStringLit #_ #"/etc/passwd")) (TyInl TyUnit) in
  wrap_handler e h

let handler4 : tgt_handler =
  let e : exp = EApp e_write (EPair e_client (EBytesCreate (e_nat 501) (EByteLit 10uy))) in
  let h : typing handler_env e (TSum TUnit TExn) = TyApp ty_write (TyPair ty_client (TyBytesCreate (ty_nat 501) (TyByteLit #_ #10uy))) in
  wrap_handler e h

let handler5 : tgt_handler =
  let e : exp = e_let_in (TSum TFDesc TExn) (EApp e_socket EUnit) (EInl EUnit) in
  let h : typing handler_env e (TSum TUnit TExn) = ty_let_in (TSum TFDesc TExn) (TSum TUnit TExn) (TyApp ty_socket TyUnit) (TyInl TyUnit) in
  wrap_handler e h
