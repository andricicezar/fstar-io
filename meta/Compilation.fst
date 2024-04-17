module Compilation

open FStar.Tactics.V2
open FStar.Reflection.Typing

let must (x : ret_t 'a) : Tac 'a =
  match x with
  | Some v, _ -> v
  | None, [] ->
    fail ("must failed, no issues?")
  | None, i::_ ->
    fail ("must failed: " ^ FStar.Issue.render_issue i)

let mk_squash (phi:term) : Tot term = pack (Tv_App (`squash) (phi, Q_Explicit))

let t_unit = `()

let valid (g:env) (phi:term) : prop =
  squash (tot_typing g t_unit (mk_squash phi))

let dyn_typing (#g #ty #t : _) () : Tac (tot_typing g t ty) =
  let tok = must <| core_check_term g t ty E_Total in
  T_Token _ _ _ (Squash.return_squash tok)

let same_typing (t0 t1 : term) : prop =
  forall g c typ. typing g t0 (c, typ) ==> typing g t1 (c, typ)

let same_valid (t0 t1 : term) : prop =
  forall g. valid g t0 ==> valid g t1

let mk_eq2 (ty t1 t2 : term) : Tot term =
  mk_app (`Prims.eq2) [(ty, Q_Implicit); (t1, Q_Explicit); (t2, Q_Explicit)]	

val norm_term_env :
  ty:typ ->
  g:env ->
  list norm_step ->
  t0:term{tot_typing g t0 ty} ->
  Tac (t1:term{same_typing t0 t1 /\ valid g (mk_eq2 ty t0 t1)})
let norm_term_env ty g steps t0 =
  let t1 = norm_term_env g steps t0 in
  admit(); // can't prove this, we should strengthen norm_term_env in F* library
  t1

(* Metaprograms with partial correctness *)
effect TacP (a:Type) (pre:prop) (post : a -> prop) =
  TacH a (requires (fun _ -> pre))
         (ensures (fun _ps r ->
           match r with
           | FStar.Stubs.Tactics.Result.Success v ps -> post v
           | _ -> True))


let type_dynamically g ty t : TacP unit (requires True) (ensures fun _ -> squash (tot_typing g ty t)) =
  let ht : tot_typing g ty t = dyn_typing () in
  Squash.return_squash ht

let assert_dynamically g phi : TacP unit (requires True) (ensures fun _ -> squash (valid g phi)) =
  let ht : tot_typing g t_unit (mk_squash phi) = dyn_typing () in
  Squash.return_squash ht

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
    let (stlc_exp, stlc_ht) = make_stlc_nat g (n-1) in
    let stlc_exp' = (`STLC.ESucc (`#stlc_exp)) in
    type_dynamically g stlc_exp' (`STLC.exp);
    let stlc_ht' = (`(STLC.TySucc #STLC.empty #(`#stlc_exp) (`#stlc_ht))) in
    type_dynamically g stlc_ht' (`(STLC.typing STLC.empty (`#stlc_exp') STLC.TNat));
    assert_dynamically g (mk_rel (`STLC.TNat) (pack (Tv_Const (C_Int n))) stlc_exp' stlc_ht');
    (stlc_exp', stlc_ht')
  end

let rec compile_to_stlc
  (g:env)
  (stlc_ty:term)
  (fs_exp:term)
  : TacP (term * term)
      (requires tot_typing g stlc_ty (`STLC.typ) /\
                tot_typing g fs_exp (`(STLC.elab_typ (`#stlc_ty))))   // this is just a typecheck, not a judgement
                                                                      // also, we cannot match on tot_typing becaut it can be a Token, aka typed by using the SMT
      (ensures fun (stlc_exp, stlc_ht) -> 
        tot_typing g stlc_exp (`STLC.exp) /\                                         // STLC exp
        tot_typing g stlc_ht (`(STLC.typing STLC.empty (`#stlc_exp) (`#stlc_ty))) /\ // well typed STLC exp
        valid g (mk_rel stlc_ty fs_exp stlc_exp stlc_ht))                            // equivalent semantics
= 
  match inspect fs_exp with
  | Tv_FVar _ ->
    (* inline the top-level definition *)
    let fs_exp' = norm_term_env (`(STLC.elab_typ (`#stlc_ty))) g [delta] fs_exp in
    let (stlc_exp, stlc_ht) = compile_to_stlc g stlc_ty fs_exp' in
    rel_subst g stlc_ty fs_exp fs_exp' stlc_exp stlc_ht;
    (stlc_exp, stlc_ht)
  
  | Tv_Const (C_Int x) ->
    if (x < 0) then fail ("not supporting ints, only nats") else
    type_dynamically g fs_exp (`nat); // inversion law
    assert_dynamically g (mk_eq2 (`STLC.typ) (`STLC.TNat) stlc_ty); // should follow from above and pre
    let (stlc_exp, stlc_ht) = make_stlc_nat g x in
    // from the post of make_stlc_nat we have:
    //   tot_typing g stlc_exp (`STLC.exp) /\
    //   tot_typing g stlc_ht (`(STLC.typing STLC.empty (`#stlc_exp) STLC.TNat)) /\
    //   valid g (mk_rel (`STLC.TNat) (pack (Tv_Const (C_Int x))) stlc_exp stlc_ht)
    type_dynamically g stlc_ht (`(STLC.typing STLC.empty (`#stlc_exp) (`#stlc_ty))); // in previous assumption substititute STLC.TNat for stlc_ty
    assert_dynamically g (mk_rel stlc_ty fs_exp stlc_exp stlc_ht); // in previous assumption substititute (pack ...) for fs_exp
    (stlc_exp, stlc_ht)
  | _ -> fail ("not implemented")


let valid_wtf (g:env) (phi:term) 
  : Lemma (requires valid g phi)
          (ensures squash (tot_typing g t_unit (mk_squash phi)))
  = let goal = squash (tot_typing g t_unit (mk_squash phi)) in
    assert (valid g phi ==> goal) by (compute ()); /// WHY????
    () // ????

let specialize (nm':string) (stlc_ty:term) (fs_exp:term) : dsl_tac_t = fun g ->
  let stlc_ty_ht : tot_typing g stlc_ty (`STLC.typ) = dyn_typing () in
  FStar.Squash.return_squash stlc_ty_ht;
  let fs_ht : tot_typing g fs_exp (`(STLC.elab_typ (`#stlc_ty))) = dyn_typing () in
  FStar.Squash.return_squash fs_ht;
  let (stlc_exp, stlc_ht) = compile_to_stlc g stlc_ty fs_exp in
  let phi = mk_rel stlc_ty fs_exp stlc_exp stlc_ht in
  valid_wtf g phi;
  [
   mk_checked_let g nm' stlc_exp (`STLC.exp);
   mk_checked_let g (nm'^"_ht") stlc_ht (`(STLC.typing STLC.empty (`#stlc_exp) (`#stlc_ty)));
   mk_checked_let g (nm'^"_pf")
                    (`())
                    (mk_squash phi);
  ]
  
let src1 : nat = 4

#set-options "--timing"
let crep () = specialize "tgt1" (`STLC.TNat) (`src1)

%splice_t[tgt1;tgt1_ht;tgt1_pf] (specialize "tgt1" (`STLC.TNat) (`src1))

let _ = 
  assert (tgt1 == STLC.ESucc (STLC.ESucc (STLC.ESucc (STLC.ESucc STLC.EZero))));
  assert (STLC.sem tgt1_ht == src1)
