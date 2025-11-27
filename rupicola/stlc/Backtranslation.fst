module Backtranslation

open STLC
open QTyp
open QExp
open ExpRel

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
          typing g (ELam body) (t1 ^-> t2)
| TyApp : #t1:qType ->
          #t2:qType ->
          #e1:exp ->
          #e2:exp ->
          #g:typ_env ->
          $h1:typing g e1 (t1 ^-> t2) ->
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

let rec backtranslate (#g:typ_env) (#e:exp) (#t:qType) (h:typing g e t) (fs_g:eval_env g) : (get_Type t) =
  match e with
  | EUnit -> ()
  | ETrue -> true
  | EFalse -> false
  | EIf _ _ _ ->
    let TyIf h1 h2 h3 = h in
    if backtranslate h1 fs_g
    then backtranslate h2 fs_g
    else backtranslate h3 fs_g
  | EVar x -> index fs_g x
  | ELam _ ->
    let TyLam #t1 #t2 hbody = h in
    assert (t == (t1 ^-> t2));
    let w : (get_Type t1) -> (get_Type t2) =
      (fun x -> backtranslate hbody (stack fs_g x)) in
    w
  | EApp _ _ ->
    let TyApp #t1 #t2 h1 h2 = h in
    assert ((get_Type t) == (get_Type t2));
    let v1 : get_Type (t1 ^-> t2) = backtranslate h1 fs_g in
    let v2 : get_Type t1 = backtranslate h2 fs_g in
    v1 v2
  | EPair _ _ ->
    let TyPair h1 h2 = h in
    let v1 = backtranslate h1 fs_g in
    let v2 = backtranslate h2 fs_g in
    (v1, v2)
  | EFst _ ->
    let TyFst #t1 h1 = h in
    fst #(get_Type t1) (backtranslate h1 fs_g)
  | ESnd _ ->
    let TySnd #t2 h1 = h in
    snd #_ #(get_Type t2) (backtranslate h1 fs_g)
  | EInl _ ->
    let TyInl t2 h = h in
    Inl #_ #(get_Type t2) (backtranslate h fs_g)
  | EInr _ ->
    let TyInr t1 h = h in
    Inr #(get_Type t1) (backtranslate h fs_g)
  | ECase _ _ _ ->
    let TyCase hcond hinlc hinrc = h in
    match backtranslate hcond fs_g with
    | Inl x -> backtranslate hinlc (stack fs_g x)
    | Inr x -> backtranslate hinrc (stack fs_g x)

open FStar.Tactics

#push-options "--split_queries always"
let rec lem_backtranslate #g #e #t (h:typing g e t) =
   match e with
  | EUnit -> equiv_unit g
  | EVar x -> equiv_var g x
  | EApp e1 e2 ->
    let TyApp h1 h2 = h in
    lem_app_fv_in_env g e1 e2;
    lem_backtranslate h1;
    lem_backtranslate h2;
    let fs_e1 = backtranslate h1 in
    let fs_e2 = backtranslate h2 in
    equiv_app fs_e1 fs_e2 e1 e2
  | ELam _ -> 
    let TyLam #t1 #t2 #body hbody = h in
    lem_lam_fv_in_env g body t1;
    lem_backtranslate hbody;
    let w : fs_oval g (t1 ^-> t2) = (fun fsG x -> backtranslate hbody (stack fsG x)) in
    equiv_lam w body
  | ETrue -> equiv_true g
  | EFalse -> equiv_false g
  | EIf e1 e2 e3 ->
    let TyIf h1 h2 h3 = h in
    lem_if_fv_in_env g e1 e2 e3;
    lem_backtranslate h1;
    lem_backtranslate h2;
    lem_backtranslate h3;
    let fs_e1 = (backtranslate h1) in
    let fs_e2 = (backtranslate h2) in
    let fs_e3 = (backtranslate h3) in
    equiv_if fs_e1 fs_e2 fs_e3 e1 e2 e3
  | EPair e1 e2 ->
    let TyPair h1 h2 = h in
    lem_pair_fv_in_env g e1 e2;
    lem_backtranslate h1;
    lem_backtranslate h2;
    let fs_e1 = (backtranslate h1) in
    let fs_e2 = (backtranslate h2) in
    equiv_pair fs_e1 fs_e2 e1 e2
  | EFst e12 ->
    let TyFst h1 = h in
    lem_fst_fv_in_env g e12;
    lem_backtranslate h1;
    let fs_e12 = (backtranslate h1) in
    equiv_pair_fst_app fs_e12 e12
  | ESnd e12 ->
    let TySnd h1 = h in
    lem_snd_fv_in_env g e12;
    lem_backtranslate h1;
    let fs_e12 = (backtranslate h1) in
    equiv_pair_snd_app fs_e12 e12
  | EInl e' ->
    let TyInl t2 h' = h in
    assume (fv_in_env g e');
    lem_backtranslate h';
    let fs_e' = backtranslate h' in
    admit ()
  | EInr e' ->
    let TyInr t1 h' = h in
    assume (fv_in_env g e');
    lem_backtranslate h';
    let fs_e' = backtranslate h' in
    admit ()
  | ECase cond inlc inrc ->
    let TyCase #t1 #t2 hcond hinlc hinrc = h in
    assume (fv_in_env g cond);
    assume (fv_in_env (extend t1 g) inlc);
    assume (fv_in_env (extend t2 g) inrc);
    lem_backtranslate hcond;
    lem_backtranslate hinlc;
    lem_backtranslate hinrc;
    let fs_cond = backtranslate hcond in
    let fs_inlc = backtranslate hinlc in
    let fs_inrc = backtranslate hinrc in
    admit ()
#pop-options
