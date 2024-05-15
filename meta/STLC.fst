(* Based on file FStar/examples/metatheory/StlcStrongDbParSubst.fst *)

module STLC

open FStar.Tactics
open FStar.Constructive
open FStar.Classical
open FStar.FunctionalExtensionality

(* Constructive-style progress and preservation proof for STLC with
   strong reduction, using deBruijn indices and parallel substitution. *)

type typ =
| TArr    : int:typ -> out:typ -> typ
| TSum    : lt:typ -> rt:typ -> typ
| TPair   : typ -> typ -> typ
| TUnit   : typ
| TNat    : typ

let rec is_fo_typ (t:typ) =
     match t with
     | TUnit -> True
     | TNat -> True
     | TPair t1 t2 -> is_fo_typ t1 /\ is_fo_typ t2
     | TSum t1 t2 -> is_fo_typ t1 /\ is_fo_typ t2
     | TArr _ _ -> False

type fo_typ = t:typ{is_fo_typ t}

type var = nat

// type pat =
// | P_ : pat 
// | PUnit : pat
// | PZero : pat
// | PSucc : pat
// | PInl : pat -> pat           // handles nested 
// | PInr : pat -> pat
// | PPair : pat -> pat -> pat

// type pattern_matches : typ -> pat -> Type0 =
// | PM_ : #t:typ -> pattern_matches t P_
// | PMUnit : pattern_matches TUnit PUnit
// | PMZero : pattern_matches TNat PZero
// | PMSucc : pattern_matches TNat PSucc
// | PMInl : #lt:typ -> #rt:typ -> #p:pat -> $h:pattern_matches lt p -> pattern_matches (TSum lt rt) (PInl p)
// | PMInr : #lt:typ -> #rt:typ -> #p:pat -> $h:pattern_matches rt p -> pattern_matches (TSum lt rt) (PInr p)
// | PMPair : #t1:typ -> #t2:typ -> #p1:pat -> #p2:pat -> $h1:pattern_matches t1 p1 -> $h2:pattern_matches t2 p2 -> pattern_matches (TPair t1 t2) (PPair p1 p2)

type exp =
| EVar         : var -> exp
| EApp         : exp -> exp -> exp
| EAbs         : typ -> exp -> exp
| EUnit        : exp
| EZero        : exp
| ESucc        : v:exp -> exp
| ENRec        : exp -> exp -> exp -> exp
| EInl         : v:exp -> exp
| EInr         : v:exp -> exp
| ECase        : exp -> exp -> exp -> exp
| EFst         : exp -> exp
| ESnd         : exp -> exp
| EPair        : fst:exp -> snd:exp -> exp

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
| TyNRec :#g:context ->
          #e1:exp ->
          #e2:exp ->
          #e3:exp ->
          #t1:typ ->
          $h1:typing g e1 TNat ->
          $h2:typing g e2 t1 ->
          $h3:typing g e3 (TArr t1 t1) ->
               typing g (ENRec e1 e2 e3) t1
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
| TyCaseNat : #g:context ->
          #e1:exp ->
          #e2:exp ->
          #e3:exp ->
          #t:typ ->
          $h1:typing g e1 TNat ->
          $h2:typing g e2 (TArr TUnit t) ->
          $h3:typing g e3 (TArr TNat t) ->
               typing g (ECase e1 e2 e3) t

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
     | EAbs t e1 -> EAbs t (subst (sub_EAbs s) e1)
     | EApp e1 e2 -> EApp (subst s e1) (subst s e2)
     | EUnit -> EUnit
     | EZero -> EZero
     | ESucc e -> ESucc (subst s e)
     | ENRec e1 e2 e3 -> ENRec (subst s e1) (subst s e2) (subst s e3)
     | EInl e -> EInl (subst s e)
     | EInr e -> EInr (subst s e)
     | ECase e1 e2 e3 -> ECase (subst s e1) (subst s e2) (subst s e3)
     | EFst e -> EFst (subst s e)
     | ESnd e -> ESnd (subst s e)
     | EPair e1 e2 -> EPair (subst s e1) (subst s e2)

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
| SNRecV :#e1:exp ->
          #e1':exp ->
          e2:exp ->
          e3:exp ->
          $hst:pure_step e1 e1' ->
               pure_step (ENRec e1 e2 e3) (ENRec e1' e2 e3)
//   | SNRecX :   e1:exp ->
//                e2:exp ->
//              #e2':exp ->
//                e3:exp ->
//              $hst:pure_step e2 e2' ->
//                  pure_step (ENRec e1 e2 e3) (ENRec e1 e2' e3)                 
| SNRec0 : e2:exp ->
          e3:exp ->
               pure_step (ENRec EZero e2 e3) e2
| SNRecIter :  v:exp ->
               e2:exp ->
               e3:exp ->
               pure_step (ENRec (ESucc v) e2 e3) (ENRec v (EApp e3 e2) e3)
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

type step = pure_step

type pure_steps : exp -> exp -> Type =
| PSrefl: e:exp ->
          pure_steps e e
| PSMany: #e1:exp ->
          #e2:exp ->
          #e3:exp ->
          $hst:pure_step e1 e2 ->
          $hsts:pure_steps e2 e3 ->
          pure_steps e1 e3

type steps : exp -> exp -> Type =
| Srefl : e:exp ->
          steps e e
| SMany : #e1:exp ->
          #e2:exp ->
          #e3:exp ->
          $hst:step e1 e2 ->
          $hsts:steps e2 e3 ->
          steps e1 e3

let rec is_value (e:exp) : bool = 
     match e with
     | EAbs _  _
     | EUnit
     | EZero -> true
     | ESucc e -> is_value e
     | EInl e -> is_value e
     | EInr e -> is_value e 
     | EPair e1 e2 -> is_value e1 && is_value e2
     | _ -> false


let rec progress (#e:exp { ~(is_value e) })
                 (#t:typ)
                 (h:typing empty e t)
  : e':exp & step e e'
  =  match h with
     | TyApp #g #e1 #e2 #t11 #t12 h1 h2 -> 
     begin
          match e1 with
          | EAbs t e1' -> (| subst (sub_beta e2) e1', SBeta t e1' e2 |)
          | _          -> let (| e1', h1' |) = progress h1 in
                              (| EApp e1' e2, SApp1 e2 h1'|) (** TODO: call-by-name **)
     end
     | TySucc #g #e h1 ->
          let (| e', h1' |) = progress h1 in
          (| ESucc e', SSucc e h1'|)
     | TyNRec #g #e1 #e2 #e3 #t1 h1 h2 h3 -> begin
          match e1 with
          | EZero -> (| e2, SNRec0 e2 e3 |)
          | ESucc v -> (| ENRec v (EApp e3 e2) e3, SNRecIter v e2 e3 |)
          | _ -> let (| e1', h1' |) = progress h1 in
                 (| ENRec e1' e2 e3, SNRecV e2 e3 h1' |)
     end
     | TyInl #g #e #t1 #t2 h1 -> 
          let (| e', h1' |) = progress h1 in
          (| EInl e', SInl e h1'|)
     | TyInr #g #e #t1 #t2 h1 -> 
          let (| e', h1' |) = progress h1 in
          (| EInr e', SInr e h1'|)
     | TyCaseSum #g #e1 #e2 #e3 #t1 #t2 #t3 h1 h2 h3 -> begin
          match e1 with
          | EInl v -> (| EApp e2 v, SCaseInl v e2 e3 |)
          | EInr v -> (| EApp e3 v, SCaseInr v e2 e3 |)
          | _ ->
               let (| e1', h1' |) = progress h1 in
               (| ECase e1' e2 e3, SCase e2 e3 h1' |)
     end
     | TyCaseNat #g #e1 #e2 #e3 #t h1 h2 h3 -> begin
          match e1 with
          | EZero -> (| EApp e2 EUnit, SCaseZero e2 e3 |)
          | ESucc v -> (| EApp e3 v, SCaseSucc v e2 e3 |)
          | _ -> let (| e1', h1' |) = progress h1 in
                 (| ECase e1' e2 e3, SCase e2 e3 h1' |)
     end
     | TyFst #g #e #t1 #t2 h1 -> begin
          match e with
          | EPair e1 e2 -> (| e1, SFst e1 e2 |)
          | _ -> let (| e', h1' |) = progress h1 in
                 (| EFst e', SFst0 h1' |)
     end
     | TySnd #g #e #t1 #t2 h1 -> begin
          match e with
          | EPair e1 e2 -> (| e2, SSnd e1 e2 |)
          | _ -> let (| e', h1' |) = progress h1 in
                 (| ESnd e', SSnd0 h1' |)
     end
     | TyPair #g #e1 #e2 #t1 #t2 h1 h2 -> begin
          if is_value e1 then
               let (| e2', h2' |) = progress h2 in
               (| EPair e1 e2', SPair2 e1 h2' |)
          else 
               let (| e1', h1' |) = progress h1 in
               (| EPair e1' e2, SPair1 h1' e2 |)
     end


(* Typing of substitutions (very easy, actually) *)
let subst_typing #r (s:sub r) (g1:context) (g2:context) =
    x:var{Some? (g1 x)} -> typing g2 (s x) (Some?.v (g1 x))

(* Substitution preserves typing
   Strongest possible statement; suggested by Steven Schäfer *)
let rec substitution (#g1:context) 
                     (#e:exp)
                     (#t:typ)
                     (#r:bool)
                     (s:sub r)
                     (#g2:context)
                     (h1:typing g1 e t)
                     (hs:subst_typing s g1 g2)
   : Tot (typing g2 (subst s e) t)
         (decreases %[bool_order (EVar? e); bool_order r; e])
   = match h1 with
   | TyVar x -> hs x
   | TyAbs tlam hbody ->
     let hs'' : subst_typing (sub_inc) g2 (extend tlam g2) =
       fun x -> TyVar (x+1) in
     let hs' : subst_typing (sub_EAbs s) (extend tlam g1) (extend tlam g2) =
       fun y -> if y = 0 then TyVar y
             else substitution sub_inc (hs (y - 1)) hs''
     in TyAbs tlam (substitution (sub_EAbs s) hbody hs')
      | TyApp hfun harg -> TyApp (substitution s hfun hs) (substitution s harg hs)
   | TyUnit -> TyUnit
   | TyZero -> TyZero
   | TySucc h1 -> TySucc (substitution s h1 hs)
   | TyNRec h1 h2 h3 -> TyNRec (substitution s h1 hs) (substitution s h2 hs) (substitution s h3 hs)
   | TyInl t2 h1 -> 
     let EInl e' = e in
     let hs' : typing g2 (EInl (subst s e')) t = TyInl t2 (substitution s h1 hs) in
     assert (subst s e == EInl (subst s e'));
     hs'
   | TyInr t1 h1 -> 
     let EInr e' = e in
     let hs' : typing g2 (EInr (subst s e')) t = TyInr t1 (substitution s h1 hs) in
     assert (subst s e == EInr (subst s e'));
     hs'
   | TyCaseSum h1 h2 h3 -> TyCaseSum (substitution s h1 hs) (substitution s h2 hs) (substitution s h3 hs)
   | TyCaseNat h1 h2 h3 -> TyCaseNat (substitution s h1 hs) (substitution s h2 hs) (substitution s h3 hs)
   | TyFst h1 -> TyFst (substitution s h1 hs)
   | TySnd h1 -> TySnd (substitution s h1 hs)
   | TyPair h1 h2 -> TyPair (substitution s h1 hs) (substitution s h2 hs)


(* Substitution for beta reduction
   Now just a special case of substitution lemma *)
let substitution_beta #e #v #t_x #t #g 
                      (h1:typing g v t_x)
                      (h2:typing (extend t_x g) e t)
  : typing g (subst (sub_beta v) e) t
  = let hs : subst_typing (sub_beta v) (extend t_x g) g =
        fun y -> if y = 0 then h1 else TyVar (y-1) in
    substitution (sub_beta v) h2 hs


(* Type preservation *)
let rec preservation_step #e #e' #g #t (ht:typing g e t) (hs:step e e') 
  : typing g e' t
  =  match hs with
     | SBeta tx e1' e2' -> 
          let TyApp h1 h2 = ht in
          substitution_beta h2 (TyAbs?.hbody h1)
     | SApp1 e2' hs1   -> 
          let TyApp h1 h2 = ht in
          TyApp (preservation_step h1 hs1) h2
     | SApp2 e1' hs2   -> 
          let TyApp h1 h2 = ht in
          TyApp h1 (preservation_step h2 hs2)
     | SSucc e' hs1    -> 
          let TySucc h1 = ht in
          TySucc (preservation_step h1 hs1)
     | SNRecV _ _ hs1 ->
          let TyNRec h1 h2 h3 = ht in
          TyNRec (preservation_step h1 hs1) h2 h3
     | SNRec0 _ _ ->
          let TyNRec h1 h2 h3 = ht in
          h2
     | SNRecIter _ _ _ ->
          // assert (e == ENRec (ESucc v) e2' e3');
          // assert (e' == ENRec v (EApp e3' e2') e3');
          let TyNRec h1 h2 h3 = ht in
          let TySucc h1' = h1 in
          TyNRec h1' (TyApp h3 h2) h3
     | SInl _ hs1     -> 
          let TyInl t2 h1 = ht in
          TyInl t2 (preservation_step h1 hs1)
     | SInr _ hs1     -> 
          let TyInr t1 h1 = ht in
          TyInr t1 (preservation_step h1 hs1)
     | SCase _ _ hs1 -> begin
          match ht with
          | TyCaseSum h1 h2 h3 -> TyCaseSum (preservation_step h1 hs1) h2 h3
          | TyCaseNat h1 h2 h3 -> TyCaseNat (preservation_step h1 hs1) h2 h3
     end
     | SCaseInl _ _ _ -> 
          let TyCaseSum h1 h2 h3 = ht in
          let TyInl _ h1' = h1 in
          TyApp h2 h1'
     | SCaseInr _ _ _ -> 
          let TyCaseSum h1 h2 h3 = ht in
          let TyInr _ h1' = h1 in
          TyApp h3 h1'
     | SCaseZero _ _ ->
          let TyCaseNat h1 h2 h3 = ht in
          TyApp h2 TyUnit
     | SCaseSucc _ _ _ ->
          let TyCaseNat h1 h2 h3 = ht in
          let TySucc h1' = h1 in
          TyApp h3 h1'
     | SFst0 hs1 -> 
          let TyFst h1 = ht in
          TyFst (preservation_step h1 hs1)
     | SFst _ _ -> 
          let TyFst h1 = ht in
          let TyPair h1' _ = h1 in
          h1'
     | SSnd0 hs1 -> 
          let TySnd h1 = ht in
          TySnd (preservation_step h1 hs1)
     | SSnd _ _ -> 
          let TySnd h1 = ht in
          let TyPair _ h1' = h1 in
          h1'
     | SPair1 hs1 _ ->
          let TyPair h1 h2 = ht in
          TyPair (preservation_step h1 hs1) h2
     | SPair2 _ hs2 ->
          let TyPair h1 h2 = ht in
          TyPair h1 (preservation_step h2 hs2)


(** Phil Wadler: Progress + Preservation = Evaluation. **)
let eval_step #e #t 
              (ht:typing empty e t) 
  : either (squash (is_value e))
           (e':exp & step e e' & typing empty e' t)
  = if is_value e then Inl ()
    else let (| e', s |) = progress ht in
         let ht' = preservation_step ht s in
         Inr (| e', s, ht' |)

let rec eval (#e:exp) (#t:typ) (ht:typing empty e t)
  : Tot (e':exp{is_value e'} & typing empty e' t)
  = match eval_step ht with
    | Inl _ -> (| e, ht |)
    | Inr (| _, _, ht' |) -> 
          admit (); (** TODO: proof of termination required, see Software Foundations - the proof that norm halts using a logical relation **)
          eval ht'

(** *** Elaboration of types and expressions to F* *)
let rec elab_typ (t:typ) : Type =
  match t with
  | TArr t1 t2 -> (elab_typ t1) -> Tot (elab_typ t2)
  | TUnit -> unit
  | TNat -> nat
  | TSum t1 t2 -> either (elab_typ t1) (elab_typ t2)
  | TPair t1 t2 -> (elab_typ t1) * (elab_typ t2)


type vcontext (g:context) = x:var{Some? (g x)} -> elab_typ (Some?.v (g x))

let vempty : vcontext empty = fun _ -> assert false

let vextend #t (x:elab_typ t) (#g:context) (ve:vcontext g) : vcontext (extend t g) =
  fun y -> if y = 0 then x else ve (y-1)

let cast_TArr #t1 #t2 (h : (elab_typ t1 -> Tot (elab_typ t2))) : elab_typ (TArr t1 t2) = h

open FStar.List.Tot

let rec fnrec (#a:Type) (n:nat) (acc:a) (iter:a -> a): Tot a =
     if n = 0 then acc else fnrec (n-1) (iter acc) iter

let rec elab_exp (#g:context) (#e:exp) (#t:typ) (h:typing g e t) (ve:vcontext g)
  : Tot (elab_typ t) (decreases e) =
     match h with
     | TyUnit -> ()
     | TyZero -> 0
     | TySucc hs ->
          1 + (elab_exp hs ve)
     | TyNRec h1 h2 h3 ->
          let v1 = elab_exp h1 ve in
          let v2 : elab_typ t = elab_exp h2 ve in
          let v3 : elab_typ (TArr t t) = elab_exp h3 ve in
          fnrec #(elab_typ t) v1 v2 v3
     | TyInl #_ #_ #t1 #t2 h1 ->
          let v = elab_exp h1 ve in
          Inl #(elab_typ t1) #(elab_typ t2) v
     | TyInr #_ #_ #t1 #t2 h1 ->
          let v = elab_exp h1 ve in
          Inr #(elab_typ t1) #(elab_typ t2) v
     | TyCaseSum h1 h2 h3 ->
          let v1 = elab_exp h1 ve in
          let v2 = elab_exp h2 ve in
          let v3 = elab_exp h3 ve in
          (match v1 with | Inl x -> v2 x | Inr y -> v3 y)
     | TyCaseNat h1 h2 h3 ->
          let v1 = elab_exp h1 ve in
          let v2 = elab_exp h2 ve in
          let v3 = elab_exp h3 ve in
          (match v1 with | 0 -> v2 () | _ -> v3 (v1-1))
     | TyVar x -> ve x
     | TyAbs t1 #_ #t2 h1 ->
          assert (t == TArr t1 t2);
          let w : elab_typ t1 -> Tot (elab_typ t2) =
          (fun x -> elab_exp h1 (vextend x ve)) in
          cast_TArr w
     | TyApp #_ #_ #_ #t1 #t2 h1 h2 ->
          assert ((elab_typ t) == (elab_typ t2));
          (* TODO: Should we change the order here, first evaluate argument? *)
          let v1 : elab_typ (TArr t1 t2) = elab_exp h1 ve in
          let v2 : elab_typ t1 = elab_exp h2 ve in
          v1 v2
     | TyFst #_ #_ #t1 #t2 h1 ->
          let v = elab_exp h1 ve in
          fst #(elab_typ t1) #(elab_typ t2) v
     | TySnd #_ #_ #t1 #t2 h1 ->
          let v = elab_exp h1 ve in
          snd #(elab_typ t1) #(elab_typ t2) v
     | TyPair h1 h2 ->
          let v1 = elab_exp h1 ve in
          let v2 = elab_exp h2 ve in
          (v1, v2)

(** ** Properties of eval elab **)

let rec eval_esucc_commute (#e:exp) (ht:typing empty e TNat)
  : Lemma (ensures (
    let ht : typing empty e TNat = ht in
    let (| e', ht' |) = eval ht in
    let (| e'', ht'' |) = eval (TySucc ht) in
    ESucc e' == e'' /\
    TySucc ht' == ht''
  )) (decreases ht) =
     if is_value e then ()
     else begin
          calc (==) {
               eval #(ESucc e) (TySucc ht);
               == {}
               (let (| e', s |) = progress ht in
               eval #(ESucc e') (TySucc (preservation_step ht s)));
          };
     let (| e', s |) = progress ht in
     let ht' = preservation_step ht s in
     assume (ht' << ht); (** TODO: proof of termination **)
     eval_esucc_commute ht'
     end

let rec elab_invariant_to_eval #e #t (ht:typing empty e t)
  : Lemma (elab_exp ht vempty == elab_exp (dsnd (eval ht)) vempty) =
     match ht with
     | TyUnit -> ()
     | TyZero -> ()
     | TySucc hts ->
          calc (==) {
          elab_exp (TySucc hts) vempty;
          == { }
          1 + elab_exp hts vempty;
          == {  elab_invariant_to_eval hts }
          1 + elab_exp (dsnd (eval hts)) vempty;
          == { } 
          elab_exp (TySucc (dsnd (eval hts))) vempty;
          == { eval_esucc_commute hts }
          elab_exp (dsnd (eval (TySucc hts))) vempty;
          }
     | _ -> admit ()

(** ** Helpers **)
let thunk #g #e #t #t' (ht:typing g e t) : (typing g (EAbs t' (subst sub_inc e)) (TArr t' t)) =
     let st : subst_typing (sub_inc) g (extend t' g) = fun x -> TyVar (x+1) in
     let ht' : typing (extend t' g) _ t = substitution sub_inc ht st in
     TyAbs t' ht'

type closed_term =
  (e:exp & t:typ & typing empty e t)

type open_term (g:context) =
  (e:exp & t:typ & typing g e t)

val abstract_term :
  (#g:context) ->
  (#t:typ) ->
  open_term (extend t g) ->
  open_term g
let abstract_term s =
  let (| _, _, s_tyj |) = s in
  (| _, _, TyAbs _ s_tyj |)

val instantiate_newest_binder :
  (#g:context) ->
  s:open_term g ->
  open_term (extend (Mkdtuple3?._2 s) g) ->
  open_term g
let instantiate_newest_binder s t =
  let (| _, _, s_tyj |) = s in
  let (| _, _, t_tyj |) = t in
  (| _, _, TyApp (TyAbs _ t_tyj) s_tyj |)

let term_case_sum
     #g
     (sc:open_term g)
     (lc:open_term g)
     (rc:open_term g)
     : Pure (open_term g)
          (requires TSum? (Mkdtuple3?._2 sc) /\
                    TArr? (Mkdtuple3?._2 lc) /\
                    TArr? (Mkdtuple3?._2 rc) /\
                    TSum?.lt (Mkdtuple3?._2 sc) == TArr?.int (Mkdtuple3?._2 lc) /\
                    TSum?.rt (Mkdtuple3?._2 sc) == TArr?.int (Mkdtuple3?._2 rc) /\
                    TArr?.out (Mkdtuple3?._2 lc) == TArr?.out (Mkdtuple3?._2 rc))
          (ensures (fun _ -> True)) =
  let (| _, TSum lt rt, sc_tyj |) = sc in
  let (| _, TArr _ t, lc_tyj |) = lc in
  let (| _, _, rc_tyj |) = rc in
  (| _, _, TyCaseSum #g #_ #_ #_ #lt #rt #t sc_tyj lc_tyj rc_tyj |)

let tbool = TSum TUnit TUnit
let etrue = EInl EUnit
let efalse = EInr EUnit
let tyjtrue #g : typing g etrue tbool = TyInl TUnit TyUnit
let tyjfalse #g : typing g efalse tbool = TyInr TUnit TyUnit

let eif c ift iff = ECase c (EAbs TUnit (subst sub_inc ift)) (EAbs TUnit (subst sub_inc iff))
let tyjif #g #c #ift #iff #t (tyjc:typing g c tbool) (tyjift:typing g ift t) (tyjiff:typing g iff t) : typing g (eif c ift iff) t =
     TyCaseSum tyjc (thunk tyjift) (thunk tyjiff)

let op_neg : exp = EAbs tbool (eif (EVar 0) efalse etrue)
let op_neg_ty : STLC.typ = TArr tbool tbool
let op_neg_tyj : typing empty op_neg op_neg_ty = 
     TyAbs (TSum TUnit TUnit) (tyjif (TyVar 0) tyjfalse tyjtrue)

let op_and : exp = EAbs tbool (EAbs tbool (eif (EVar 1) (EVar 0) efalse))
let op_and_ty : STLC.typ = TArr tbool (TArr tbool tbool)
let op_and_tyj : typing empty op_and op_and_ty = TyAbs tbool (TyAbs tbool (tyjif (TyVar 1) (TyVar 0) tyjfalse))

let op_or : exp = EAbs tbool (EAbs tbool (eif (EVar 1) etrue (EVar 0)))
let op_or_ty : STLC.typ = TArr tbool (TArr tbool tbool)
let op_or_tyj : typing empty op_or op_or_ty = TyAbs tbool (TyAbs tbool (tyjif (TyVar 1) tyjtrue (TyVar 0)))

let op_add : exp = EAbs TNat (EAbs TNat (ENRec (EVar 1) (EVar 0) (EAbs TNat (ESucc (EVar 0)))))
let op_add_ty : STLC.typ = TArr TNat (TArr TNat TNat)
let op_add_tyj : typing empty op_add op_add_ty = 
     TyAbs TNat (TyAbs TNat (TyNRec (TyVar 1) (TyVar 0) (TyAbs TNat (TySucc (TyVar 0)))))

let op_mul' : exp = EAbs TNat (EAbs TNat (ENRec (EVar 1) EZero (EApp (EVar 2) (EVar 0))))
let op_mul_ty' : STLC.typ = TArr TNat (TArr TNat TNat)
let op_mul_tyj' : typing (fun x -> if x = 0 then Some op_add_ty else None) op_mul' op_mul_ty' = 
     TyAbs TNat (TyAbs TNat (TyNRec (TyVar 1) TyZero (TyApp (TyVar 2) (TyVar 0))))

let helper_substitution_beta #e #v #t_x #t #g 
                      (h1:typing g v t_x)
                      (h2:typing (extend t_x g) e t)
  : (e':exp & t':typ & typing g e' t')
  = (| _, _, substitution_beta h1 h2 |)

let op_mul_dtriple = helper_substitution_beta op_add_tyj op_mul_tyj'
let op_mul = Mkdtuple3?._1 op_mul_dtriple
let op_mul_ty = Mkdtuple3?._2 op_mul_dtriple
let op_mul_tyj = Mkdtuple3?._3 op_mul_dtriple

let op_sub : exp = EAbs TNat (EAbs TNat (ENRec (EVar 0) (EVar 1) (EAbs TNat (ECase (EVar 0) (EAbs TUnit EZero) (EAbs TNat (EVar 0))))))
let op_sub_ty : STLC.typ = TArr TNat (TArr TNat TNat)
let op_sub_tyj : typing empty op_sub op_sub_ty = 
     TyAbs TNat (TyAbs TNat (TyNRec (TyVar 0) (TyVar 1) (TyAbs TNat (TyCaseNat (TyVar 0) (TyAbs TUnit TyZero) (TyAbs TNat (TyVar 0))))))

let op_lte' : exp = EAbs TNat (EAbs TNat (ECase (EApp (EApp (EVar 2) (EVar 1)) (EVar 0)) (EAbs TUnit etrue) (EAbs TNat efalse)))
let op_lte_ty' : STLC.typ = TArr TNat (TArr TNat tbool)
let op_lte_tyj' : typing (fun x -> if x = 0 then Some op_sub_ty else None) op_lte' op_lte_ty' = 
     TyAbs TNat (TyAbs TNat (TyCaseNat (TyApp (TyApp (TyVar 2) (TyVar 1)) (TyVar 0)) (thunk tyjtrue) (thunk tyjfalse)))

let op_lte_dtriple = helper_substitution_beta op_sub_tyj op_lte_tyj'
let op_lte = Mkdtuple3?._1 op_lte_dtriple
let op_lte_ty = Mkdtuple3?._2 op_lte_dtriple
let op_lte_tyj = Mkdtuple3?._3 op_lte_dtriple