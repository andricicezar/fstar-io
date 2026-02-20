module Backtranslation

open STLC
open QTyp
open QExp
open IO
open LogRelSourceTarget
open LogRelTargetSource

module C1 = LogRelTargetSource.CompatibilityLemmas
module C2 = LogRelSourceTarget.CompatibilityLemmas

// the environment is non-standard, more fancy
// also over qType instead of syntactic types (typ)
noeq
type typing : typ_env -> exp -> qType -> Type =
| TyUnit : #g:typ_env ->
           typing g EUnit qUnit
| TyTrue : #g:typ_env ->
           typing g ETrue qBool
| TyFalse : #g:typ_env ->
            typing g EFalse qBool
| TyString : #g:typ_env ->
             #s:string ->
             typing g (EString s) qString
| TyIf : #g:typ_env ->
         #e1:exp ->
         #e2:exp ->
         #e3:exp ->
         #t:qType ->
         $h1:typing g e1 qBool ->
         $h2:typing g e2 t ->
         $h3:typing g e3 t ->
         typing g (EIf e1 e2 e3) t
| TyVar : #g:typ_env ->
          x:var{Some? (g x)} ->
          typing g (EVar x) (Some?.v (g x))
| TyLam : #t1:qType ->
          #t2:qType ->
          #body:exp ->
          #g:typ_env ->
          $hbody:typing (extend t1 g) body t2 ->
          typing g (ELam body) (t1 ^->!@ t2)
| TyApp : #t1:qType ->
          #t2:qType ->
          #e1:exp ->
          #e2:exp ->
          #g:typ_env ->
          $h1:typing g e1 (t1 ^->!@ t2) ->
          $h2:typing g e2 t1 ->
          typing g (EApp e1 e2) t2
| TyPair : #g:typ_env ->
          #e1:exp ->
          #e2:exp ->
          #t1:qType ->
          #t2:qType ->
          $h1:typing g e1 t1 ->
          $h2:typing g e2 t2 ->
          typing g (EPair e1 e2) (t1 ^* t2)
| TyFst : #t1:qType ->
          #t2:qType ->
          #e:exp ->
          #g:typ_env ->
          $h1:typing g e (t1 ^* t2) ->
          typing g (EFst e) t1
| TySnd : #t2:qType ->
          #t1:qType ->
          #e:exp ->
          #g:typ_env ->
          $h1:typing g e (t1 ^* t2) ->
          typing g (ESnd e) t2
| TyInl : #t1:qType ->
          t2:qType ->
          #e:exp ->
          #g:typ_env ->
          $h:typing g e t1 ->
          typing g (EInl e) (t1 ^+ t2)
| TyInr :
          t1:qType ->
          #t2:qType ->
          #e:exp ->
          #g:typ_env ->
          $h:typing g e t2 ->
          typing g (EInr e) (t1 ^+ t2)
| TyCase : #t1:qType ->
           #t2:qType ->
           #t3:qType ->
           #cond:exp ->
           #inlc:exp ->
           #inrc:exp ->
           #g:typ_env ->
           $h1:typing g cond (t1 ^+ t2) ->
           $h2:typing (extend t1 g) inlc t3 ->
           $h3:typing (extend t2 g) inrc t3 ->
           typing g (ECase cond inlc inrc) t3
| TyFileDescr :
           #g:typ_env ->
           fd:file_descr ->
           typing g (EFileDescr fd) qFileDescr
| TyOpenfile :
           #g:typ_env ->
           #e1:exp ->
           $h1:typing g e1 qString ->
           typing g (EOpen e1) (qResexn qFileDescr)
| TyRead :
           #g:typ_env ->
           #e1:exp ->
           $h1:typing g e1 qFileDescr ->
           typing g (ERead e1) (qResexn qString)
| TyWrite :
           #g:typ_env ->
           #e1:exp ->
           #e2:exp ->
           $h1:typing g e1 qFileDescr ->
           $h2:typing g e2 qString ->
           typing g (EWrite e1 e2) (qResexn qUnit)
| TyClose :
           #g:typ_env ->
           #e1:exp ->
           $h1:typing g e1 qFileDescr ->
           typing g (EClose e1) (qResexn qUnit)
| TyStringEq :
           #g:typ_env ->
           #e1:exp ->
           #e2:exp ->
           $h1:typing g e1 qString ->
           $h2:typing g e2 qString ->
           typing g (EStringEq e1 e2) qBool

val backtranslate_exp (#g:typ_env) (#e:exp) (#t:qType) (h:typing g e t) : fs_oprod g t
let rec backtranslate_exp #g #e #t h : Tot (fs_oprod g t) =
  match e with
  | EUnit -> fs_oprod_return_val g t ()
  | ETrue -> fs_oprod_return_val g t true
  | EFalse -> fs_oprod_return_val g t false
  | EString s -> fs_oprod_return_val g t s
  | EIf _ _ _ ->
    let TyIf h1 h2 h3 = h in
    let h1 : typing g _ qBool = h1 in
    let h2 : typing g _ t = h2 in
    let h3 : typing g _ t = h3 in
    fs_oprod_if (backtranslate_exp h1) (backtranslate_exp h2) (backtranslate_exp h3)
  | EVar x -> fs_oprod_var g x
  | ELam _ ->
    let TyLam #t1 #t2 hbody = h in
    let hbody : typing (extend t1 g) _ t2 = hbody in
    fs_oprod_lambda (backtranslate_exp hbody)
  | EApp _ _ ->
    let TyApp #t1 #t2 h1 h2 = h in
    let h1 : typing g _ (t1 ^->!@ t2) = h1 in
    let h2 : typing g _ t1 = h2 in
    fs_oprod_app (backtranslate_exp h1) (backtranslate_exp h2)

  | EPair _ _ ->
    let TyPair #_ #_ #_ #t1 #t2 h1 h2 = h in
    let h1 : typing g _ t1 = h1 in
    let h2 : typing g _ t2 = h2 in
    fs_oprod_pair (backtranslate_exp h1) (backtranslate_exp h2)
  | EFst _ ->
    let TyFst #t1 #t2 h1 = h in
    let h1 : typing g _ (t1 ^* t2) = h1 in
    fs_oprod_fmap #_ #(t1 ^* t2) (backtranslate_exp h1) fst
  | ESnd _ ->
    let TySnd #t2 #t1 h1 = h in
    let h1 : typing g _ (t1 ^* t2) = h1 in
    fs_oprod_fmap #_ #(t1 ^* t2) (backtranslate_exp h1) snd

  | EInl _ ->
    let TyInl #t1 t2 h1 = h in
    let h1 : typing g _ t1 = h1 in
    fs_oprod_fmap #_ #_ #(t1 ^+ t2) (backtranslate_exp h1) Inl
  | EInr _ ->
    let TyInr t1 #t2 h1 = h in
    let h1 : typing g _ t2 = h1 in
    fs_oprod_fmap #_ #_ #(t1 ^+ t2) (backtranslate_exp h1) Inr
  | ECase _ _ _ ->
    let TyCase #t1 #t2 #t3 h1 h2 h3 = h in
    let h1 : typing g _ (t1 ^+ t2) = h1 in
    let h2 : typing (extend t1 g) _ t3 = h2 in
    let h3 : typing (extend t2 g) _ t3 = h3 in
    fs_oprod_case (backtranslate_exp h1) (backtranslate_exp h2) (backtranslate_exp h3)
  | EFileDescr _ ->
    let TyFileDescr fd = h in
    fs_oprod_return_val g qFileDescr fd
  | EOpen _ ->
    let TyOpenfile h' = h in
    let h' : typing g _ qString = h' in
    fs_oprod_openfile (backtranslate_exp h')
  | ERead _ ->
    let TyRead h' = h in
    let h' : typing g _ qFileDescr = h' in
    fs_oprod_read (backtranslate_exp h')
  | EWrite _ _ ->
    let TyWrite h1 h2 = h in
    let h1 : typing g _ qFileDescr = h1 in
    let h2 : typing g _ qString = h2 in
    fs_oprod_write (backtranslate_exp h1) (backtranslate_exp h2)
  | EClose _ ->
    let TyClose h' = h in
    let h' : typing g _ qFileDescr = h' in
    fs_oprod_close (backtranslate_exp h')
  | EStringEq _ _ ->
    let TyStringEq h1 h2 = h in
    let h1 : typing g _ qString = h1 in
    let h2 : typing g _ qString = h2 in
    fs_oprod_string_eq (backtranslate_exp h1) (backtranslate_exp h2)

let rec lem_backtranslate_superset_exp #g #e #t (h:typing g e t) : Lemma (backtranslate_exp h ⊒ e) =
   match e with
  | EUnit -> C1.compat_oprod_unit g
  | ETrue -> C1.compat_oprod_true g
  | EFalse -> C1.compat_oprod_false g
  | EString s -> C1.compat_oprod_string g s
  | EIf _ _ _ ->
    let TyIf #_ #e1 #e2 #e3 h1 h2 h3 = h in
    lem_backtranslate_superset_exp h1;
    lem_backtranslate_superset_exp h2;
    lem_backtranslate_superset_exp h3;
    C1.compat_oprod_if (backtranslate_exp h1) (backtranslate_exp h2) (backtranslate_exp h3) e1 e2 e3
  | EVar x -> C1.compat_oprod_var g x
  | EApp _ _ ->
    let TyApp #t1 #t2 #e1 #e2 h1 h2 = h in
    lem_backtranslate_superset_exp h1;
    lem_backtranslate_superset_exp h2;
    C1.compat_oprod_app (backtranslate_exp h1) (backtranslate_exp h2) e1 e2
  | ELam _ ->
    let TyLam #t1 #t2 #body hbody = h in
    lem_backtranslate_superset_exp hbody;
    C1.compat_oprod_lambda (backtranslate_exp hbody) body
  | EPair _ _ ->
    let TyPair #_ #e1 #e2 #t1 #t2 h1 h2 = h in
    lem_backtranslate_superset_exp h1;
    lem_backtranslate_superset_exp h2;
    C1.compat_oprod_pair (backtranslate_exp h1) (backtranslate_exp h2) e1 e2
  | EFst _ ->
    let TyFst #t1 #t2 #e' h' = h in
    lem_backtranslate_superset_exp h';
    C1.compat_oprod_fst (backtranslate_exp h') e'
  | ESnd _ ->
    let TySnd #t2 #t1 #e' h' = h in
    lem_backtranslate_superset_exp h';
    C1.compat_oprod_snd (backtranslate_exp h') e'
  | EInl _ ->
    let TyInl #t1 t2 #e' h' = h in
    lem_backtranslate_superset_exp h';
    C1.compat_oprod_inl t1 t2 (backtranslate_exp h') e'
  | EInr _ ->
    let TyInr t1 #t2 #e' h' = h in
    lem_backtranslate_superset_exp h';
    C1.compat_oprod_inr t1 t2 (backtranslate_exp h') e'
  | ECase _ _ _ ->
    let TyCase #t1 #t2 #t3 #e1 #e2 #e3 h1 h2 h3 = h in
    lem_backtranslate_superset_exp h1;
    lem_backtranslate_superset_exp h2;
    lem_backtranslate_superset_exp h3;
    C1.compat_oprod_case (backtranslate_exp h1) (backtranslate_exp h2) (backtranslate_exp h3) e1 e2 e3
  | EFileDescr fd -> C1.compat_oprod_file_descr g fd
  | EOpen _ ->
    let TyOpenfile #_ #e' h' = h in
    lem_backtranslate_superset_exp h';
    C1.compat_oprod_openfile (backtranslate_exp h') e'
  | ERead _ ->
    let TyRead #_ #e' h' = h in
    lem_backtranslate_superset_exp h';
    C1.compat_oprod_read (backtranslate_exp h') e'
  | EWrite _ _ ->
    let TyWrite #_ #e1 #e2 h1 h2 = h in
    lem_backtranslate_superset_exp h1;
    lem_backtranslate_superset_exp h2;
    C1.compat_oprod_write (backtranslate_exp h1) (backtranslate_exp h2) e1 e2
  | EClose _ ->
    let TyClose #_ #e' h' = h in
    lem_backtranslate_superset_exp h';
    C1.compat_oprod_close (backtranslate_exp h') e'
  | EStringEq _ _ ->
    let TyStringEq #_ #e1 #e2 h1 h2 = h in
    lem_backtranslate_superset_exp h1;
    lem_backtranslate_superset_exp h2;
    C1.compat_oprod_string_eq (backtranslate_exp h1) (backtranslate_exp h2) e1 e2

let rec lem_backtranslate_subset_exp #g #e #t (h:typing g e t) : Lemma (backtranslate_exp h ⊑ e) =
   match e with
  | EUnit -> C2.compat_oprod_unit g
  | ETrue -> C2.compat_oprod_true g
  | EFalse -> C2.compat_oprod_false g
  | EString s -> C2.compat_oprod_string g s
  | EIf _ _ _ ->
    let TyIf #_ #e1 #e2 #e3 h1 h2 h3 = h in
    lem_backtranslate_subset_exp h1;
    lem_backtranslate_subset_exp h2;
    lem_backtranslate_subset_exp h3;
    C2.compat_oprod_if (backtranslate_exp h1) (backtranslate_exp h2) (backtranslate_exp h3) e1 e2 e3
  | EVar x -> C2.compat_oprod_var g x
  | EApp _ _ ->
    let TyApp #t1 #t2 #e1 #e2 h1 h2 = h in
    lem_backtranslate_subset_exp h1;
    lem_backtranslate_subset_exp h2;
    C2.compat_oprod_app (backtranslate_exp h1) (backtranslate_exp h2) e1 e2
  | ELam _ ->
    let TyLam #t1 #t2 #body hbody = h in
    lem_backtranslate_subset_exp hbody;
    C2.compat_oprod_lambda (backtranslate_exp hbody) body
  | EPair _ _ ->
    let TyPair #_ #e1 #e2 #t1 #t2 h1 h2 = h in
    lem_backtranslate_subset_exp h1;
    lem_backtranslate_subset_exp h2;
    C2.compat_oprod_pair (backtranslate_exp h1) (backtranslate_exp h2) e1 e2
  | EFst _ ->
    let TyFst #t1 #t2 #e' h' = h in
    lem_backtranslate_subset_exp h';
    C2.compat_oprod_fst (backtranslate_exp h') e'
  | ESnd _ ->
    let TySnd #t2 #t1 #e' h' = h in
    lem_backtranslate_subset_exp h';
    C2.compat_oprod_snd (backtranslate_exp h') e'
  | EInl _ ->
    let TyInl #t1 t2 #e' h' = h in
    lem_backtranslate_subset_exp h';
    C2.compat_oprod_inl t1 t2 (backtranslate_exp h') e'
  | EInr _ ->
    let TyInr t1 #t2 #e' h' = h in
    lem_backtranslate_subset_exp h';
    C2.compat_oprod_inr t1 t2 (backtranslate_exp h') e'
  | ECase _ _ _ ->
    let TyCase #t1 #t2 #t3 #e1 #e2 #e3 h1 h2 h3 = h in
    lem_backtranslate_subset_exp h1;
    lem_backtranslate_subset_exp h2;
    lem_backtranslate_subset_exp h3;
    C2.compat_oprod_case (backtranslate_exp h1) (backtranslate_exp h2) (backtranslate_exp h3) e1 e2 e3
  | EFileDescr fd -> C2.compat_oprod_file_descr g fd
  | EOpen _ ->
    let TyOpenfile #_ #e' h' = h in
    lem_backtranslate_subset_exp h';
    C2.compat_oprod_openfile (backtranslate_exp h') e'
  | ERead _ ->
    let TyRead #_ #e' h' = h in
    lem_backtranslate_subset_exp h';
    C2.compat_oprod_read (backtranslate_exp h') e'
  | EWrite _ _ ->
    let TyWrite #_ #e1 #e2 h1 h2 = h in
    lem_backtranslate_subset_exp h1;
    lem_backtranslate_subset_exp h2;
    C2.compat_oprod_write (backtranslate_exp h1) (backtranslate_exp h2) e1 e2
  | EClose _ ->
    let TyClose #_ #e' h' = h in
    lem_backtranslate_subset_exp h';
    C2.compat_oprod_close (backtranslate_exp h') e'
  | EStringEq _ _ ->
    let TyStringEq #_ #e1 #e2 h1 h2 = h in
    lem_backtranslate_subset_exp h1;
    lem_backtranslate_subset_exp h2;
    C2.compat_oprod_string_eq (backtranslate_exp h1) (backtranslate_exp h2) e1 e2

let rec backtranslate (#e:value) (#t:qType) (h:typing empty e t) : fs_val t =
  match e with
  | EUnit -> ()
  | ETrue -> true
  | EFalse -> false
  | EString s -> s
  | ELam _ ->
    let TyLam #t1 #t2 hbody = h in
    let hbody : typing (extend t1 empty) _ t2 = hbody in
    fun x -> (backtranslate_exp hbody) (stack empty_eval x)
  | EPair _ _ ->
    let TyPair #_ #_ #_ #t1 #t2 h1 h2 = h in
    let h1 : typing empty _ t1 = h1 in
    let h2 : typing empty _ t2 = h2 in
    fs_val_pair (backtranslate h1) (backtranslate h2)
  | EInl _ ->
    let TyInl #t1 t2 h1 = h in
    let h1 : typing empty _ t1 = h1 in
    Inl #(get_Type t1) #(get_Type t2) (backtranslate h1)
  | EInr _ ->
    let TyInr t1 #t2 h1 = h in
    let h1 : typing empty _ t2 = h1 in
    Inr #(get_Type t1) #(get_Type t2) (backtranslate h1)
  | EFileDescr _ ->
    let TyFileDescr fd = h in
    fd

let rec lem_backtranslate_valid_contains (#e:value) #t (h:typing empty e t) : Lemma (valid_contains #t (backtranslate h) e) =
  match e with
  | EUnit
  | ETrue
  | EFalse
  | EString _
  | EFileDescr _ -> ()
  | ELam _ ->
    let TyLam #t1 #t2 #body hbody = h in
    lem_backtranslate_superset_exp hbody;
    C1.compat_oval_lambda_oprod (backtranslate_exp hbody) body;
    let f' : fs_oval empty (t1 ^->!@ t2) = (fun fsG x -> (backtranslate_exp hbody) (stack fsG x)) in
    lem_value_superset_valid_contains (t1 ^->!@ t2) f' e;
    assert (valid_contains #(t1 ^->!@ t2) (f' empty_eval) e)
  | EPair _ _ ->
    let TyPair #_ #e1 #e2 #t1 #t2 h1 h2 = h in
    lem_backtranslate_valid_contains h1;
    lem_backtranslate_valid_contains h2
  | EInl _ ->
    let TyInl #t1 t2 #e' h' = h in
    lem_backtranslate_valid_contains h'
  | EInr _ ->
    let TyInr t1 #t2 #e' h' = h in
    lem_backtranslate_valid_contains h'

let rec lem_backtranslate_valid_member_of (#e:value) #t (h:typing empty e t) : Lemma (valid_member_of #t (backtranslate h) e) =
  match e with
  | EUnit
  | ETrue
  | EFalse
  | EString _
  | EFileDescr _ -> ()
  | ELam _ ->
    let TyLam #t1 #t2 #body hbody = h in
    lem_backtranslate_subset_exp hbody;
    C2.compat_oval_lambda_oprod (backtranslate_exp hbody) body;
    let f' : fs_oval empty (t1 ^->!@ t2) = (fun fsG x -> (backtranslate_exp hbody) (stack fsG x)) in
    lem_value_subset_valid_member_of (t1 ^->!@ t2) f' e;
    assert (valid_member_of #(t1 ^->!@ t2) (f' empty_eval) e)
  | EPair _ _ ->
    let TyPair #_ #e1 #e2 #t1 #t2 h1 h2 = h in
    lem_backtranslate_valid_member_of h1;
    lem_backtranslate_valid_member_of h2
  | EInl _ ->
    let TyInl #t1 t2 #e' h' = h in
    lem_backtranslate_valid_member_of h'
  | EInr _ ->
    let TyInr t1 #t2 #e' h' = h in
    lem_backtranslate_valid_member_of h'

let lem_backtranslate (#e:value) #t (h:typing empty e t) =
  lem_backtranslate_valid_contains h;
  lem_backtranslate_valid_member_of h
