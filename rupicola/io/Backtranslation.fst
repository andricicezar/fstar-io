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

let equiv_val_are_equiv_prods (#g:typ_env) (#t:qType) (fs_v:fs_oval g t) (e:exp) :
  Lemma
    (requires (fs_v ≈ e))
    (ensures (helper_return_prod fs_v ≋ e))
  [SMTPat (fs_v ≈ e)] =
  equiv_oprod_return fs_v e


let rec lem_backtranslate' #g #e #t (h:typing g e t) : Lemma (backtranslate' h ≋ e)=
   match e with
  | EUnit ->
    equiv_unit g;
    let r = lem_backtranslate_value_no_io h in
    equiv_oprod_return r e
  | EVar x ->
    equiv_var g x;
    equiv_oprod_return #g #_ (fun (fsG:eval_env g) -> index fsG x) e
  | EApp e1 e2 ->
    let TyApp #t1 #t2 #_ #_ #g h1 h2 = h in
    assert (t == t2);
    lem_fv_in_env_app g e1 e2;
    let fs_e1 : fs_oprod g (t1 ^->!@ t2) = backtranslate' h1 in
    lem_backtranslate' h1;
    assert (fs_e1 ≋ e1);
    let fs_e2 : fs_oprod g t1 = backtranslate' h2 in
    lem_backtranslate' h2;
    assert (fs_e2 ≋ e2);
//    let fs_e = (fun fsG ->
//      let!@ f' = fs_e1 fsG in
//      let!@ x' = fs_e2 fsG in
//      f' x') in
 //   equiv_oprod_bind #_ #t1 #t2 fs_e2 fs_e1 e2 e1;
    equiv_oprod_app' fs_e1 fs_e2 e1 e2;
    assert (backtranslate' h == (fun fsG ->
      let!@ f' = fs_e1 fsG in
      let!@ x' = fs_e2 fsG in
      f' x')) by (
        rewrite_eqs_from_context ();
        norm [delta_once [`%backtranslate'];iota];
        tadmit ())
  | _ -> admit ()

let _ = ()
(**
  | ELam _ ->
    let TyLam #t1 #t2 #body hbody = h in
    lem_fv_in_env_lam g t1 body;
    lem_backtranslate' hbody;
    equiv_lam_prod (backtranslate' hbody) body
  | ETrue -> equiv_true g
  | EFalse -> equiv_false g
  | EIf e1 e2 e3 ->
    let TyIf h1 h2 h3 = h in
    lem_fv_in_env_if g e1 e2 e3;
    lem_backtranslate' h1;
    lem_backtranslate' h2;
    lem_backtranslate' h3;
    let fs_e1 = (backtranslate' h1) in
    let fs_e2 = (backtranslate' h2) in
    let fs_e3 = (backtranslate' h3) in
    equiv_oprod_if fs_e1 fs_e2 fs_e3 e1 e2 e3
  | EPair e1 e2 ->
    let TyPair #_ #_ #_ #t1 #t2 h1 h2 = h in
    lem_fv_in_env_pair g e1 e2;
    lem_backtranslate' h1;
    lem_backtranslate' h2;
    let fs_e1 = (backtranslate' h1) in
    let fs_e2 = (backtranslate' h2) in
    equiv_pair #_ #t1 #t2 fs_e1 fs_e2 e1 e2
  | EFst e12 ->
    let TyFst #t1 #t2 h1 = h in
    lem_fv_in_env_fst g e12;
    lem_backtranslate' h1;
    let fs_e12 = (backtranslate' h1) in
    equiv_pair_fst_app #_ #t1 #t2 fs_e12 e12
  | ESnd e12 ->
    let TySnd #t1 #t2 h1 = h in
    lem_fv_in_env_snd g e12;
    lem_backtranslate' h1;
    let fs_e12 = (backtranslate' h1) in
    equiv_pair_snd_app #_ #t1 #t2 fs_e12 e12
  | EInl e' ->
    let TyInl #t1 t2 h' = h in
    lem_fv_in_env_inl g e';
    lem_backtranslate' h';
    let fs_e' = backtranslate' h' in
    equiv_inl #_ #t1 t2 fs_e' e'
  | EInr e' ->
    let TyInr t1 #t2 h' = h in
    lem_fv_in_env_inr g e';
    lem_backtranslate' h';
    let fs_e' = backtranslate' h' in
    equiv_inr t1 #t2 fs_e' e'
  | ECase cond inlc inrc ->
    let TyCase #t1 #t2 #t3 hcond hinlc hinrc = h in
    lem_fv_in_env_case g t1 t2 cond inlc inrc;
    lem_backtranslate' hcond;
    lem_backtranslate' hinlc;
    lem_backtranslate' hinrc;
    let fs_cond = backtranslate' hcond in
    let fs_inlc = backtranslate' hinlc in
    let fs_inrc = backtranslate' hinrc in
    equiv_oprod_case #_ #t1 #t2 #t3 fs_cond fs_inlc fs_inrc cond inlc inrc
 **)
