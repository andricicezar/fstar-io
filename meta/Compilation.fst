module Compilation

open HelperTactics

let object_eq2_refl (x:'a) : Lemma (x == x) = ()

let eq2_refl (g:env) (ty:term) (t:term)
  : TacP unit
         (requires squash (tot_typing g t ty))
         (ensures fun _ -> valid g (mk_eq2 ty t t))
  = (* currently this just calls the typechecker/solver, but it could
    be done statically from the type of Refl *)
    let goal = mk_squash (mk_eq2 ty t t) in
    let tok = must <| core_check_term g (`()) goal E_Total in
    let _ : valid g (mk_eq2 ty t t) = 
        Squash.return_squash (T_Token _ _ _ (Squash.return_squash tok)) in
    assert (valid g (mk_eq2 ty t t));
    ()

let eq2_trans (g:env) (ty:term) (t0 t1 t2:term)
  : TacP unit
         (requires valid g (mk_eq2 ty t0 t1) /\ valid g (mk_eq2 ty t1 t2))
         (ensures fun _ -> valid g (mk_eq2 ty t0 t2))
= admit() // could prove, it's a lift of the eq2_trans object-level lemma

let mk_rel (stlc_ty fs_exp stlc_exp stlc_ht : term) : Tot term =
  mk_app (`Criteria.op_u8781) [(stlc_ty, Q_Implicit); (fs_exp, Q_Explicit); (stlc_exp, Q_Implicit); (stlc_ht, Q_Explicit)]	

let rel_subst (g:env) stlc_ty (fs_exp fs_exp' stlc_exp:term) stlc_ht
  : TacP unit
         (requires valid g (mk_eq2 (`(STLC.elab_typ (`#stlc_ty))) fs_exp fs_exp') /\
                   valid g (mk_rel stlc_ty fs_exp' stlc_exp stlc_ht))
         (ensures fun _ -> valid g (mk_rel stlc_ty fs_exp stlc_exp stlc_ht))
= admit()

let rec make_stlc_nat (g:env) (n:nat)
  : TacP (term * term)
      (requires True)
      (ensures fun (stlc_exp, stlc_ht) -> 
        tot_typing g stlc_exp (`STLC.exp) /\
        tot_typing g stlc_ht (`(STLC.typing STLC.empty (`#stlc_exp) STLC.TNat)) /\
        valid g (mk_rel (`STLC.TNat) (pack (Tv_Const (C_Int n))) stlc_exp stlc_ht)) =
  match n with
  | 0 -> begin 
    let stlc_exp = (`STLC.EZero) in
    let stlc_ht = (`(STLC.TyZero #STLC.empty)) in
    type_dynamically g stlc_exp (`STLC.exp);
    type_dynamically g stlc_ht (`(STLC.typing STLC.empty (`#stlc_exp) STLC.TNat));
    assert_dynamically g (mk_rel (`STLC.TNat) (pack (Tv_Const (C_Int n))) stlc_exp stlc_ht);
    (stlc_exp, stlc_ht)
  end
  | _ -> begin
    assert (n > 0);
    admit ();
    let (stlc_exp, stlc_ht) = make_stlc_nat g (n-1) in
    let stlc_exp' = (`STLC.ESucc (`#stlc_exp)) in
    type_dynamically g stlc_exp' (`STLC.exp);
    let stlc_ht' = (`(STLC.TySucc #STLC.empty #(`#stlc_exp) (`#stlc_ht))) in
    type_dynamically g stlc_ht' (`(STLC.typing STLC.empty (`#stlc_exp') STLC.TNat));
    assert_dynamically g (mk_rel (`STLC.TNat) (pack (Tv_Const (C_Int n))) stlc_exp' stlc_ht');
    (stlc_exp', stlc_ht')
  end

let rec term_translation
  (g:env)
  (qty:term) (** Quoted STLC type **)
  (qfs:term)
  : TacP (term * term)
      (requires tot_typing g qty (`STLC.typ) /\
                tot_typing g qfs (`(STLC.elab_typ (`#qty))))   // this is just a typecheck, not a judgement.
                                                               // we cannot match on tot_typing because it can be a Token, aka typed by using the SMT
      (ensures fun (qstlc, qstlc_tyj) -> 
        tot_typing g qstlc (`STLC.exp) /\                                         // STLC exp
        tot_typing g qstlc_tyj (`(STLC.typing STLC.empty (`#qstlc) (`#qty))) /\ // well typed STLC exp
        valid g (mk_rel qty qfs qstlc qstlc_tyj))                            // equivalent semantics
= 
  match inspect qfs with
  | Tv_FVar _ ->
    (* inline the top-level definition *)
    let fs_exp' = typed_norm_term_env (`(STLC.elab_typ (`#qty))) g [delta] qfs in
    let (stlc_exp, stlc_ht) = term_translation g qty fs_exp' in
    rel_subst g qty qfs fs_exp' stlc_exp stlc_ht;
    (stlc_exp, stlc_ht)
  
  | Tv_Const (C_Int x) ->
    if (x < 0) then fail ("not supporting ints, only nats") else
    type_dynamically g qfs (`nat); // inversion law
    assert_dynamically g (mk_eq2 (`STLC.typ) (`STLC.TNat) qty); // should follow from above and pre
    let (qstlc, qstlc_tyj) = make_stlc_nat g x in
    // from the post of make_stlc_nat we have:
    //   tot_typing g stlc_exp (`STLC.exp) /\
    //   tot_typing g stlc_ht (`(STLC.typing STLC.empty (`#stlc_exp) STLC.TNat)) /\
    //   valid g (mk_rel (`STLC.TNat) (pack (Tv_Const (C_Int x))) stlc_exp stlc_ht)
    type_dynamically g qstlc_tyj (`(STLC.typing STLC.empty (`#qstlc) (`#qty))); // in previous assumption substititute STLC.TNat for stlc_ty
    assert_dynamically g (mk_rel qty qfs qstlc qstlc_tyj); // in previous assumption substititute (pack ...) for fs_exp
    (qstlc, qstlc_tyj)
  | _ -> fail ("not implemented")


let specialize (nm':string) (qstlc_ty:term) (qfs:term) : dsl_tac_t = fun g ->
  let qstlc_ty_tyj : tot_typing g qstlc_ty (`STLC.typ) = dyn_typing () in
  FStar.Squash.return_squash qstlc_ty_tyj;
  let qfs_tyj : tot_typing g qfs (`(STLC.elab_typ (`#qstlc_ty))) = dyn_typing () in
  FStar.Squash.return_squash qfs_tyj;
  let (qstlc, qstlc_tyj) = term_translation g qstlc_ty qfs in
  let phi = mk_rel qstlc_ty qfs qstlc qstlc_tyj in
  valid_wtf g phi;
  [
   mk_checked_let g nm' qstlc (`STLC.exp);
   mk_checked_let g (nm'^"_ht") qstlc_tyj (`(STLC.typing STLC.empty (`#qstlc) (`#qstlc_ty)));
   mk_checked_let g (nm'^"_pf")
                    (`())
                    (mk_squash phi);
  ]
  
let src1 : nat = 4

#set-options "--timing"
let crep () = specialize "tgt1" (`STLC.TNat) (`src1)

%splice_t[tgt1;tgt1_ht;tgt1_pf] (specialize "tgt1" (`STLC.TNat) (`src1))

let stlc_sem (#e:STLC.exp) (#t:STLC.typ) (ht:STLC.typing STLC.empty e t) : STLC.elab_typ t = 
  let (| _, ht' |) = STLC.eval ht in
  STLC.elab_exp ht' STLC.vempty

let _ = 
  assert (tgt1 == STLC.ESucc (STLC.ESucc (STLC.ESucc (STLC.ESucc STLC.EZero))));
  assert (stlc_sem tgt1_ht == src1)
