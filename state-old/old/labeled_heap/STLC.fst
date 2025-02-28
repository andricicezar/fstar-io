(* Based on file FStar/examples/metatheory/StlcStrongDbParSubst.fst *)

module STLC

open FStar.Tactics
open FStar.Constructive
open FStar.Classical
open FStar.FunctionalExtensionality

(** STLC+Refs (+Linked Lists).
     The type system prevents storing functions on the heap. **)

type unsafe_typ =
| TUnit   : unsafe_typ
| TNat    : unsafe_typ
| TArr    : int:unsafe_typ -> out:unsafe_typ -> unsafe_typ (* TArr is in universe 1 *)
| TSum    : lt:unsafe_typ -> rt:unsafe_typ -> unsafe_typ
| TPair   : unsafe_typ -> unsafe_typ -> unsafe_typ
| TRef    : unsafe_typ -> unsafe_typ                (* TRef is in universe 0 *)
| TLList  : unsafe_typ -> unsafe_typ                (* TLList uses TRef, so also in universe 0 *)

let rec is_univ0 t =
     match t with
     | TUnit -> True
     | TNat -> True
     | TSum t1 t2 -> is_univ0 t1 /\ is_univ0 t2
     | TPair t1 t2 -> is_univ0 t1 /\ is_univ0 t2
     | TRef t -> is_univ0 t
     | TLList t -> is_univ0 t
     | TArr _ _ -> False

type typ0 = t:unsafe_typ{is_univ0 t}

let rec good_univs t =
     match t with
     | TUnit -> True
     | TNat -> True
     | TSum t1 t2 -> good_univs t1 /\ good_univs t2
     | TPair t1 t2 -> good_univs t1 /\ good_univs t2
     | TRef t -> is_univ0 t
     | TLList t -> is_univ0 t
     | TArr t1 t2 -> good_univs t1 /\ good_univs t2

type typ = t:unsafe_typ{good_univs t}

let rec lemma_typ0_is_typ (t:typ0) :
     Lemma
          (requires True)
          (ensures (good_univs t)) 
          [SMTPat (good_univs t)]
= match t with
               | TUnit -> ()
               | TNat -> ()
               | TSum t1 t2 -> (lemma_typ0_is_typ t1; lemma_typ0_is_typ t2)
               | TPair t1 t2 -> (lemma_typ0_is_typ t1; lemma_typ0_is_typ t2)
               | TRef t -> ()
               | TLList t -> ()
               | TArr t1 t2 -> ()

type var = nat
type loc = nat

type exp =
| EUnit        : exp
| EZero        : exp
| ESucc        : v:exp -> exp
| EVar         : var -> exp
| ELoc         : loc -> exp
| EApp         : exp -> exp -> exp
| EAbs         : typ -> exp -> exp
| EInl         : v:exp -> exp
| EInr         : v:exp -> exp
| ECase        : exp -> exp -> exp -> exp
| EFst         : exp -> exp
| ESnd         : exp -> exp
| EPair        : fst:exp -> snd:exp -> exp
| EAlloc       : exp -> exp
| EReadRef     : exp -> exp
| EWriteRef   : exp -> exp -> exp

(* Type system; as inductive relation (not strictly necessary for STLC) *)
type context = var -> Tot (option typ)

val empty : context
let empty _ = None

(* we only need extend at 0 *)
val extend : typ -> context -> Tot context
let extend t g y = if y = 0 then Some t
                   else g (y-1)

noeq type typing : context -> exp -> typ -> Type0 =
| TyVar : #g:context ->
          x:var{Some? (g x)} ->
          typing g (EVar x) (Some?.v (g x))
| TyAbs : #g :context ->
          t :typ ->
          #e1:exp ->
          #t':typ ->
          $hbody:typing (extend t g) e1 t' ->
               typing g (EAbs t e1) (TArr t t')
| TyApp : #g:context ->
          #e1:exp ->
          #e2:exp ->
          #ty1:typ ->
          #ty2:typ ->
          $tyj1:typing g e1 (TArr ty1 ty2) ->
          $tyj2:typing g e2 ty1 ->
               typing g (EApp e1 e2) ty2
| TyUnit : #g:context ->
          typing g EUnit TUnit
| TyZero : #g:context ->
          typing g EZero TNat
| TySucc : #g:context ->
          #e:exp ->
          $h1:typing g e TNat ->
               typing g (ESucc e) TNat
| TyInl : #g:context ->
          #e:exp ->
          #t1:typ ->
          t2:typ ->
          $h1:typing g e t1 ->
               typing g (EInl e) (TSum t1 t2)
| TyInr : #g:context ->
          #e:exp ->
          t1:typ ->
          #t2:typ ->
          $h1:typing g e t2 ->
               typing g (EInr e) (TSum t1 t2)
| TyCaseSum : #g:context ->
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
// | TyCaseNat : #g:context ->
//           #e1:exp ->
//           #e2:exp ->
//           #e3:exp ->
//           #t:typ ->
//           $h1:typing g e1 TNat ->
//           $h2:typing g e2 (TArr TUnit t) ->
//           $h3:typing g e3 (TArr TNat t) ->
//                typing g (ECase e1 e2 e3) t

| TyFst : #g:context ->
          #e:exp ->
          #t1:typ ->
          #t2:typ ->
          $h1:typing g e (TPair t1 t2) ->
               typing g (EFst e) t1
| TySnd : #g:context ->
          #e:exp ->
          #t1:typ ->
          #t2:typ ->
          $h1:typing g e (TPair t1 t2) ->
               typing g (ESnd e) t2
| TyPair :#g:context ->
          #e1:exp ->
          #e2:exp ->
          #t1:typ ->
          #t2:typ ->
          $h1:typing g e1 t1 ->
          $h2:typing g e2 t2 ->
               typing g (EPair e1 e2) (TPair t1 t2)
| TyAllocRef  :#g:context ->
               #e:exp ->
               #t:typ{is_univ0 t} ->
               $h1:typing g e t ->
                    typing g (EAlloc e) (TRef t)
| TyReadRef :#g:context ->
             #e:exp ->
             #t:typ{is_univ0 t} ->
             $h1:typing g e (TRef t) ->
               typing g (EReadRef e) t
| TyWriteRef :#g:context ->
               #e1:exp ->
               #e2:exp ->
               #t:typ{is_univ0 t} ->
               $h1:typing g e1 (TRef t) ->
               $h2:typing g e2 t ->
                 typing g (EWriteRef e1 e2) TUnit

(* Parallel substitution operation `subst` *)

(* The termination argument uses a lexicographic ordering composed of:
   0) a bit saying whether the expression is a variable or not;
   1) an _undecidable_ well-founded order on substitutions that
      equates all renamings, equates all non-renamings, and makes
      renamings strictly smaller than non-renamings; we write down a
      non-constructive function is_renaming mapping substitutions
      (infinite objects) to 0 (renaming) or 1 (non-renaming)
   2) the structure of the expression e *)

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
                     e]) = 
     match e with
     | EVar x -> s x
     | ELoc l -> ELoc l
     | EAbs t e1 -> EAbs t (subst (sub_EAbs s) e1)
     | EApp e1 e2 -> EApp (subst s e1) (subst s e2)
     | EUnit -> EUnit
     | EZero -> EZero
     | ESucc e -> ESucc (subst s e)
     | EInl e -> EInl (subst s e)
     | EInr e -> EInr (subst s e)
     | ECase e1 e2 e3 -> ECase (subst s e1) (subst s e2) (subst s e3)
     | EFst e -> EFst (subst s e)
     | ESnd e -> ESnd (subst s e)
     | EPair e1 e2 -> EPair (subst s e1) (subst s e2)
     | EAlloc e -> EAlloc (subst s e)
     | EReadRef e -> EReadRef (subst s e)
     | EWriteRef e1 e2 -> EWriteRef (subst s e1) (subst s e2)

and sub_EAbs (#r:bool) (s:sub r) 
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


let rec is_closed_exp (e:exp) (g:context) : bool =
     match e with
     | EVar x -> Some? (g x)
     | EAbs t e1 -> is_closed_exp e1 (extend t g)
     | EApp e1 e2 -> is_closed_exp e1 g && is_closed_exp e2 g
     | ESucc e -> is_closed_exp e g
     | EInl e -> is_closed_exp e g
     | EInr e -> is_closed_exp e g
     | ECase e1 e2 e3 -> is_closed_exp e1 g && is_closed_exp e2 g && is_closed_exp e3 g
     | EFst e -> is_closed_exp e g
     | ESnd e -> is_closed_exp e g
     | EPair e1 e2 -> is_closed_exp e1 g && is_closed_exp e2 g
     | EAlloc e1 -> is_closed_exp e1 g
     | EReadRef e1 -> is_closed_exp e1 g
     | EWriteRef e1 e2 -> is_closed_exp e1 g && is_closed_exp e2 g
     | EUnit
     | EZero -> true
     | ELoc _ -> false // TODO: is this ok?

let rec is_closed_value (e:exp) : bool = 
     match e with
     | EUnit
     | EZero -> true
     | ESucc e -> is_closed_value e
     | ELoc _ -> false
     | EInl e -> is_closed_value e
     | EInr e -> is_closed_value e 
     | EPair e1 e2 -> is_closed_value e1 && is_closed_value e2
     | EAbs t _ -> is_closed_exp e (extend t empty)
     | _ -> false


(* Small-step operational semantics; strong / full-beta reduction is
   non-deterministic, so necessarily as inductive relation *)

type pure_step : exp -> exp -> Type =
| SBeta : t:typ ->
          e1:exp ->
          e2:exp ->
          pure_step (EApp (EAbs t e1) e2) (subst (sub_beta e2) e1)
| SApp1 : #e1:exp ->
          e2:exp ->
          #e1':exp ->
          $hst:pure_step e1 e1' ->
               pure_step (EApp e1 e2) (EApp e1' e2)
| SApp2 :   e1:exp ->
          #e2:exp ->
          #e2':exp ->
          $hst:pure_step e2 e2' ->
               pure_step (EApp e1 e2) (EApp e1 e2')
| SSucc :    e:exp ->
          #e':exp ->
          $hst:pure_step e e' ->
               pure_step (ESucc e) (ESucc e')
| SInl  : e:exp ->
          #e':exp ->
          $hst:pure_step e e' ->
               pure_step (EInl e) (EInl e')
| SInr  : e:exp ->
          #e':exp ->
          $hst:pure_step e e' ->
               pure_step (EInr e) (EInr e')
| SCase : #e1:exp ->
          #e1':exp ->
          e2:exp ->
          e3:exp ->
          $hst:pure_step e1 e1' ->
               pure_step (ECase e1 e2 e3) (ECase e1' e2 e3)
| SCaseInl :   v:exp ->
               e2:exp ->
               e3:exp ->
                    pure_step (ECase (EInl v) e2 e3) (EApp e2 v)
| SCaseInr :   v:exp ->
               e2:exp ->
               e3:exp ->
                    pure_step (ECase (EInr v) e2 e3) (EApp e3 v)
| SCaseZero :  e2:exp ->
               e3:exp ->
                    pure_step (ECase EZero e2 e3) (EApp e2 EUnit)
| SCaseSucc :  v:exp ->
               e2:exp ->
               e3:exp ->
                    pure_step (ECase (ESucc v) e2 e3) (EApp e3 v)
| SFst0 : #e:exp ->
          #e':exp ->
          $hst:pure_step e e' ->
               pure_step (EFst e) (EFst e')
| SFst :  e1:exp ->
          e2:exp ->
          pure_step (EFst (EPair e1 e2)) e1
| SSnd0 : #e:exp ->
          #e':exp ->
          $hst:pure_step e e' ->
               pure_step (ESnd e) (ESnd e')
| SSnd :  e1:exp ->
          e2:exp ->
          pure_step (ESnd (EPair e1 e2)) e2
| SPair1 :#e1:exp ->
          #e1':exp ->
          $hst:pure_step e1 e1' ->
          e2:exp ->
               pure_step (EPair e1 e2) (EPair e1' e2)
| SPair2 : e1:exp ->
          #e2:exp ->
          #e2':exp ->
          $hst:pure_step e2 e2' ->
               pure_step (EPair e1 e2) (EPair e1 e2')
| SAllocPure : #e:exp ->
               #e':exp ->
               $hst:pure_step e e' ->
                    pure_step (EAlloc e) (EAlloc e')
| SReadRefPure : #e:exp ->
               #e':exp ->
               $hst:pure_step e e' ->
                    pure_step (EReadRef e) (EReadRef e')
| SUpdateRefPure0 : #e1:exp ->
               #e1':exp ->
               $hst:pure_step e1 e1' ->
               e2:exp ->
                    pure_step (EWriteRef e1 e2) (EWriteRef e1' e2)
| SUpdateRefPure1 : e1:exp ->
               #e2:exp ->
               #e2':exp ->
               $hst:pure_step e2 e2' ->
                    pure_step (EWriteRef e1 e2) (EWriteRef e1 e2')

let store = loc -> option (e:exp{is_closed_value e})
let empty_store : store = fun _ -> None
let salloc (s:store) (l:loc) (v:exp{is_closed_value v}) : store = 
     fun l' -> if l' = l then Some v else s l'

noeq
type step  : store -> exp -> store -> exp -> Type =
| SPure : s:store ->
          #e1:exp ->
          #e2:exp ->
          $hst:pure_step e1 e2 ->
          step s e1 s e2
| SAlloc :s:store ->
          #l:loc ->
          squash (s l = None) ->
          #v:exp ->
          squash (is_closed_value v) ->
          step s (EAlloc v) (salloc s l v) (ELoc l)
| SReadRef :s:store ->
          #l:loc ->
          squash (Some? (s l)) ->
          step s (EReadRef (ELoc l)) s (Some?.v (s l))
| SUpdateRef :s:store ->
          #l:loc ->
          squash (Some? (s l)) ->
          #v:exp ->
          squash (is_closed_value v) ->
          step s (EWriteRef (ELoc l) v) (salloc s l v) EUnit


noeq
type steps : store -> exp -> store -> exp -> Type =
| Srefl : s:store ->
          e:exp ->
          steps s e s e
| SMany : #s1:store ->
          #s2:store ->
          #s3:store ->
          #e1:exp ->
          #e2:exp ->
          #e3:exp ->
          $hst:step s1 e1 s2 e2 ->
          $hsts:steps s2 e2 s3 e3 ->
          steps s1 e1 s3 e3

(** Examples **)
let e:exp = EAlloc (EAlloc EZero)
let tyj:typing empty e (TRef (TRef TNat)) = TyAllocRef (TyAllocRef TyZero)

let e':exp = EReadRef (EAlloc EZero)
let tyj':typing empty e' TNat = TyReadRef (TyAllocRef TyZero)

let e'':exp = EWriteRef (EAlloc EZero) (ESucc EZero)
let tyj'':typing empty e'' TUnit = TyWriteRef (TyAllocRef TyZero) (TySucc TyZero)

let e''':exp = EAbs (TRef TNat) (EWriteRef (EVar 0) (ESucc (EReadRef (EVar 0))))
let tyj''':typing empty e''' (TArr (TRef TNat) TUnit) = TyAbs (TRef TNat) (TyWriteRef (TyVar 0) (TySucc (TyReadRef (TyVar 0))))

let ctx_update_ref_test : typing empty _ (TArr (TRef TNat) TUnit) =
     TyAbs (TRef TNat) (TyWriteRef (TyVar 0) (TySucc (TyReadRef (TyVar 0))))

let ctx_update_multiple_refs_test : typing empty _ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit)) =
     TyAbs (TRef (TRef TNat)) 
          (TyAbs (TRef TNat) (
               TyApp (TyAbs TUnit (TyWriteRef (TyVar 2) (TyVar 1)))
                     (TyWriteRef (TyVar 0) (TySucc (TyReadRef (TyVar 0))))))

let ctx_identity : typing empty _ (TArr (TRef TNat) (TRef TNat)) =
     TyAbs (TRef TNat) (TyVar 0)

let ctx_dynamic_alloc_test : typing empty _ (TArr TNat (TRef TNat)) =
     TyAbs TNat (TyAllocRef (TyVar 0))

let ctx_returns_callback_test : typing empty _ (TArr TUnit (TArr TUnit TUnit)) =
     TyAbs TUnit 
          (TyApp (TyAbs (TRef TNat) (TyAbs TUnit (TyWriteRef (TyVar 1) (TySucc (TyReadRef (TyVar 1))))))
                 (TyAllocRef TyZero))

(** Cezar: landins knot should not be possible to type check in the current system **)
(**
let landins_knot : exp =
     EApp
          (EAbs (TRef (TArr TUnit TUnit)) (* r *)
               (EApp
                 (EAbs (TArr TUnit TUnit) (* f *)
                    (EApp
                         (EAbs TUnit (EApp (EVar 1) EUnit)) (* f () *)  
                         (EWriteRef (EVar 1) (EVar 0)) (* r := f *)
                    ))
                 (EAbs TUnit (EApp (EReadRef (EVar 1)) EUnit)))) (* f = fun () -> r () *)
          (EAlloc (EAbs TUnit (EVar 0))) (* alloc r (fun () -> ()) *)

let ty_landins_knot : typing empty landins_knot TUnit =
     TyApp (TyAbs (TRef (TArr TUnit TUnit))
                  (TyApp (TyAbs (TArr TUnit TUnit) 
                               (TyApp (TyAbs TUnit (TyApp (TyVar 1) TyUnit))
                                       (TyWriteRef (TyVar 1) (TyVar 0))))
                         (TyAbs TUnit (TyApp (TyReadRef (TyVar 1)) TyUnit))))
           (TyAllocRef (TyAbs TUnit (TyVar 0)))
**)

open FStar.ST 

let landins_knot_fs () : St nat = 
  let id : nat -> St nat = fun x -> x in
  let r : ref (nat -> St nat) = alloc id in
  let f : nat -> St nat = (fun x -> !r x) in
  r := f;
  f 0
