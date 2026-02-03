module Backtranslation

open STLC
open QTyp
open QExp
open ExpRel
open IO

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


open FStar.Tactics.V1

val backtranslate' (#g:typ_env) (#e:exp) (#t:qType) (h:typing g e t) : fs_oprod g t
let rec backtranslate' #g #e #t h : Tot (fs_oprod g t) =
  match e with
  | EUnit -> fs_oprod_return_val g t ()
  | ETrue -> fs_oprod_return_val g t true
  | EFalse -> fs_oprod_return_val g t false
  | EIf _ _ _ ->
    let TyIf h1 h2 h3 = h in
    let h1 : typing g _ qBool = h1 in
    let h2 : typing g _ t = h2 in
    let h3 : typing g _ t = h3 in
    fs_oprod_if (backtranslate' h1) (backtranslate' h2) (backtranslate' h3)
  | EVar x -> fs_oprod_var g x
  | ELam _ ->
    let TyLam #t1 #t2 hbody = h in
    let hbody : typing (extend t1 g) _ t2 = hbody in
    fs_oprod_lambda (backtranslate' hbody)
  | EApp _ _ ->
    let TyApp #t1 #t2 h1 h2 = h in
    let h1 : typing g _ (t1 ^->!@ t2) = h1 in
    let h2 : typing g _ t1 = h2 in
    fs_oprod_app (backtranslate' h1) (backtranslate' h2)

  | EPair _ _ ->
    let TyPair #_ #_ #_ #t1 #t2 h1 h2 = h in
    let h1 : typing g _ t1 = h1 in
    let h2 : typing g _ t2 = h2 in
    fs_oprod_pair (backtranslate' h1) (backtranslate' h2)
  | EFst _ ->
    let TyFst #t1 #t2 h1 = h in
    let h1 : typing g _ (t1 ^* t2) = h1 in
    fs_oprod_fmap #_ #(t1 ^* t2) (backtranslate' h1) fst
  | ESnd _ ->
    let TySnd #t2 #t1 h1 = h in
    let h1 : typing g _ (t1 ^* t2) = h1 in
    fs_oprod_fmap #_ #(t1 ^* t2) (backtranslate' h1) snd

  | EInl _ ->
    let TyInl #t1 t2 h1 = h in
    let h1 : typing g _ t1 = h1 in
    fs_oprod_fmap #_ #_ #(t1 ^+ t2)(backtranslate' h1) Inl
  | EInr _ ->
    let TyInr t1 #t2 h1 = h in
    let h1 : typing g _ t2 = h1 in
    fs_oprod_fmap #_ #_ #(t1 ^+ t2) (backtranslate' h1) Inr
  | ECase _ _ _ ->
    let TyCase #t1 #t2 #t3 h1 h2 h3 = h in
    let h1 : typing g _ (t1 ^+ t2) = h1 in
    let h2 : typing (extend t1 g) _ t3 = h2 in
    let h3 : typing (extend t2 g) _ t3 = h3 in
    fs_oprod_case (backtranslate' h1) (backtranslate' h2) (backtranslate' h3)

let rec lem_backtranslate' #g #e #t (h:typing g e t) : Lemma (backtranslate' h ≋ e)=
   match e with
  | EUnit -> equiv_oprod_unit g
  | ETrue -> equiv_oprod_true g
  | EFalse -> equiv_oprod_false g
  | EIf _ _ _ ->
    let TyIf #_ #e1 #e2 #e3 h1 h2 h3 = h in
    lem_backtranslate' h1;
    lem_backtranslate' h2;
    lem_backtranslate' h3;
    equiv_oprod_if (backtranslate' h1) (backtranslate' h2) (backtranslate' h3) e1 e2 e3
  | EFileDescr fd -> equiv_oprod_file_descr g fd
  | EVar x -> equiv_oprod_var g x
  | EApp _ _ ->
    let TyApp #t1 #t2 #e1 #e2 h1 h2 = h in
    lem_backtranslate' h1;
    lem_backtranslate' h2;
    equiv_oprod_app (backtranslate' h1) (backtranslate' h2) e1 e2
  | ELam _ ->
    let TyLam #t1 #t2 #body hbody = h in
    lem_backtranslate' hbody;
    equiv_oprod_lambda (backtranslate' hbody) body
  | EPair _ _ ->
    let TyPair #_ #e1 #e2 #t1 #t2 h1 h2 = h in
    lem_backtranslate' h1;
    lem_backtranslate' h2;
    equiv_oprod_pair (backtranslate' h1) (backtranslate' h2) e1 e2
  | EFst _ ->
    let TyFst #t1 #t2 #e' h' = h in
    lem_backtranslate' h';
    equiv_oprod_fst (backtranslate' h') e'
  | ESnd _ ->
    let TySnd #t2 #t1 #e' h' = h in
    lem_backtranslate' h';
    equiv_oprod_snd (backtranslate' h') e'
  | EInl _ ->
    let TyInl #t1 t2 #e' h' = h in
    lem_backtranslate' h';
    equiv_oprod_inl t1 t2 (backtranslate' h') e'
  | EInr _ ->
    let TyInr t1 #t2 #e' h' = h in
    lem_backtranslate' h';
    equiv_oprod_inr t1 t2 (backtranslate' h') e'
  | ECase _ _ _ ->
    let TyCase #t1 #t2 #t3 #e1 #e2 #e3 h1 h2 h3 = h in
    lem_backtranslate' h1;
    lem_backtranslate' h2;
    lem_backtranslate' h3;
    equiv_oprod_case (backtranslate' h1) (backtranslate' h2) (backtranslate' h3) e1 e2 e3

let rec lem_backtranslate_value_no_io (#g:typ_env) (#e:value) (#t:qType) (h:typing g e t) (fsG:eval_env g) :
  Pure (fs_val t) True (fun v -> return v == backtranslate' h fsG) =
  let r = backtranslate' h fsG in
  match e with
  | EUnit
  | ETrue
  | EVar _
  | EFalse -> extract_v_from_io_return r

  | EInl e' ->
    let TyInl #t1 t2 h' = h in
    let r : fs_prod (t1 ^+ t2) = r in
    assert (r == io_bind (backtranslate' h' fsG) (fun x -> return (Inl #_ #(get_Type t2) x))) by (
      rewrite_eqs_from_context ();
      norm [delta_once [`%backtranslate';`%(let!@)];zeta;iota]);

    let r' = lem_backtranslate_value_no_io h' fsG in
    assert (
      io_bind (backtranslate' h' fsG) (fun x -> return (Inl #_ #(get_Type t2) x))
      == io_bind (return r') (fun x -> return (Inl #_ #(get_Type t2) x)));
    assume (io_bind (return r') (fun x -> return (Inl #_ #(get_Type t2) x)) ==
      return (Inl #_ #(get_Type t2) r'));
    assume (r == return (Inl #_ #(get_Type t2) r'));
    extract_v_from_io_return r
  | EInr e' -> admit ()
  | EPair _ _ -> admit ()
  | ELam _ -> admit ()

  | EIf _ _ _
  | EApp _ _
  | EFst _
  | ESnd _
  | ECase _ _ _ -> assert False
