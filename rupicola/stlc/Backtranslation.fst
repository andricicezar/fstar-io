module Backtranslation

open STLC
open QTyp
open QExp
open ExpRel

// the environment is non-standard, more fancy
// also over qType instead of syntactic types (typ)
noeq type typing : typ_env -> exp -> qType -> Type =
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
  | TyLam : #g:typ_env ->
            #body:exp ->
            #t1:qType ->
            #t2:qType ->
            $hbody:typing (extend t1 g) body t2 ->
              typing g (ELam body) (t1 ^-> t2)
  | TyApp : #g:typ_env ->
            #e1:exp ->
            #e2:exp ->
            #t1:qType ->
            #t2:qType ->
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
  | TyFst : #g:typ_env ->
            #e:exp ->
            #t1:qType ->
            #t2:qType ->
            $h1:typing g e (t1 ^* t2) ->
              typing g (EFst e) t1
  | TySnd : #g:typ_env ->
            #e:exp ->
            #t1:qType ->
            #t2:qType ->
            $h1:typing g e (t1 ^* t2) ->
              typing g (ESnd e) t2

let rec backtranslate (g:typ_env) (e:exp) (t:qType) (h:typing g e t) (fs_g:eval_env g) : (get_Type t) =
  match e with
  | EUnit -> ()
  | ETrue -> true
  | EFalse -> false
  | EIf e1 e2 e3 ->
    let TyIf #_ #_ #_ #_ #t h1 h2 h3 = h in
    let b : bool = backtranslate g e1 qBool h1 fs_g in
    let v1 = backtranslate g e2 t h2 fs_g in
    let v2 = backtranslate g e3 t h3 fs_g in
    if b then v1 else v2
  | EVar x -> index fs_g x
  | ELam body ->
    let TyLam #_ #_ #t1 #t2 hbody = h in
    assert (t == (t1 ^-> t2));
    let w : (get_Type t1) -> (get_Type t2) =
      (fun x -> backtranslate (extend t1 g) body t2 hbody (stack fs_g x)) in
    w
  | EApp e1 e2 ->
    let TyApp #_ #_ #_ #t1 #t2 h1 h2 = h in
    assert ((get_Type t) == (get_Type t2));
    let v1 : get_Type (t1 ^-> t2) = backtranslate g e1 (t1 ^-> t2) h1 fs_g in
    let v2 : get_Type t1 = backtranslate g e2 t1 h2 fs_g in
    v1 v2
  | EPair e1 e2 ->
    let TyPair #_ #_ #_ #t1 #t2 h1 h2 = h in
    let v1 = backtranslate g e1 t1 h1 fs_g in
    let v2 = backtranslate g e2 t2 h2 fs_g in
    (v1, v2)
  | EFst e ->
    let TyFst #_ #_ #t1 #t2 h1 = h in
    let v = backtranslate g e (t1 ^* t2) h1 fs_g in
    fst #(get_Type t1) #(get_Type t2) v
  | ESnd e ->
    let TySnd #_ #_ #t1 #t2 h1 = h in
    let v = backtranslate g e (t1 ^* t2) h1 fs_g in
    snd #(get_Type t1) #(get_Type t2) v

#push-options "--split_queries always"
val lem_backtranslate g (e:exp{fv_in_env g e}) t (h:typing g e t) : Lemma
(equiv t (backtranslate g e t h) e)
let rec lem_backtranslate g e t (h:typing g e t) =
   match e with
  | EUnit -> equiv_unit g
  | EVar x -> equiv_var g x
  | EApp e1 e2 ->
    let TyApp #_ #_ #_ #t1 #t2 h1 h2 = h in
    lem_app_fv_in_env g e1 e2;
    lem_backtranslate g e1 (t1 ^-> t2) h1;
    lem_backtranslate g e2 t1 h2;
    let fs_e1 = (backtranslate g e1 (t1 ^-> t2) h1) in
    let fs_e2 = (backtranslate g e2 t1 h2) in
    equiv_app fs_e1 fs_e2 e1 e2
  | ELam body ->
    let TyLam #_ #body #t1 #t2 hbody = h in
    lem_lam_fv_in_env g body t1;
    lem_backtranslate (extend t1 g) body t2 hbody;
    assert (equiv t2 (backtranslate (extend t1 g) body t2 hbody) body);
    assert (forall b (s:gsub (extend t1 g) b) (fsG:eval_env (extend t1 g)). fsG ∽ s ==> t2 ⦂ ((backtranslate (extend t1 g) body t2 hbody) fsG, gsubst s body));
    let g' = extend t1 g in
    introduce forall b (s:gsub g b) (fsG:eval_env g). fsG ∽ s ==> (t1 ^-> t2) ⦂ ((fun x -> backtranslate (extend t1 g) body t2 hbody (stack fsG x)), gsubst s (ELam body)) with
      begin
      let f : (get_Type t1) -> (get_Type t2) = (fun x -> backtranslate (extend t1 g) body t2 hbody (stack fsG x)) in
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce  fsG ∽ s ==> (t1 ^-> t2) ⦂ (f, ELam body') with _.
        begin
        introduce forall (e':closed_exp). steps (ELam body') e' /\ irred e' ==> (t1 ^-> t2) ∋ (f, e') with
          begin
          introduce _ ==> (t1 ^-> t2) ∋ (f, e') with h.
            begin
            lem_value_is_irred (ELam body');
            lem_steps_irred_e_irred_e'_implies_e_e' (ELam body') e';
            assert ((ELam body') == e');
            let QArr #s1 #s2 r1 r2 = get_rel (t1 ^-> t2) in
            introduce forall (v:value) (fs_v:get_Type t1). t1 ∋ (fs_v, v) ==> t2 ⦂ (f fs_v, subst_beta v body') with
              begin
              introduce  t1 ∋ (fs_v, v) ==> _ with _.
                begin
                let s' = gsub_extend s t1 v in
                let fsG' = stack fsG fs_v in
                lem_substitution s t1 v body;
                assert (t2 ⦂ (f fs_v, gsubst s' body))
                end
              end;
              assert ((t1 ^-> t2) ∋ (f, gsubst s (ELam body)));
              lem_values_are_expressions (t1 ^-> t2) f (gsubst s (ELam body));
              assert ((t1 ^-> t2) ⦂ (f, gsubst s (ELam body)))
            end
          end
        end
      end
  | ETrue -> equiv_true g
  | EFalse -> equiv_false g
  | EIf e1 e2 e3 ->
    let TyIf #_ #_ #_ #_ #t h1 h2 h3 = h in
    lem_if_fv_in_env g e1 e2 e3;
    lem_backtranslate g e1 qBool h1;
    lem_backtranslate g e2 t h2;
    lem_backtranslate g e3 t h3;
    let fs_e1 = (backtranslate g e1 qBool h1) in
    let fs_e2 = (backtranslate g e2 t h2) in
    let fs_e3 = (backtranslate g e3 t h3) in
    equiv_if fs_e1 fs_e2 fs_e3 e1 e2 e3
  | EPair e1 e2 ->
    let TyPair #_ #_ #_ #t1 #t2 h1 h2 = h in
    lem_pair_fv_in_env g e1 e2;
    lem_backtranslate g e1 t1 h1;
    lem_backtranslate g e2 t2 h2;
    let fs_e1 = (backtranslate g e1 t1 h1) in
    let fs_e2 = (backtranslate g e2 t2 h2) in
    equiv_pair fs_e1 fs_e2 e1 e2
  | EFst e12 ->
    let TyFst #_ #_ #t1 #t2 h1 = h in
    lem_fst_fv_in_env g e12;
    lem_backtranslate g e12 (t1 ^* t2) h1;
    let fs_e12 = (backtranslate g e12 (t1 ^* t2) h1) in
    equiv_pair_fst_app fs_e12 e12
  | ESnd e12 ->
    let TySnd #_ #_ #t1 #t2 h1 = h in
    lem_snd_fv_in_env g e12;
    lem_backtranslate g e12 (t1 ^* t2) h1;
    let fs_e12 = (backtranslate g e12 (t1 ^* t2) h1) in
    equiv_pair_snd_app fs_e12 e12
#pop-options
