module VerifiedTransformSTLC

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
  mk_app (`CriteriaStatic.STLC.op_u8781) [(stlc_ty, Q_Implicit); (fs_exp, Q_Explicit); (stlc_exp, Q_Implicit); (stlc_ht, Q_Explicit)]	

let rel_subst (g:env) (fs_exp fs_exp' stlc_exp:term) stlc_ht
  : TacP unit
         (requires valid g (mk_eq2 (`nat) fs_exp fs_exp') /\ 
                   valid g (mk_rel (`STLC.TNat) fs_exp' stlc_exp stlc_ht))
         (ensures fun _ -> valid g (mk_rel (`STLC.TNat) fs_exp stlc_exp stlc_ht))
= admit()

let rec compile_to_stlc (g:env) (fs_exp:term{tot_typing g fs_exp (`nat)})
  : TacP (term * term)
      (requires True)
      (ensures fun (stlc_exp, stlc_ht) -> 
        tot_typing g stlc_exp (`STLC.exp) /\                                  // STLC exp
        tot_typing g stlc_ht (`(STLC.typing STLC.empty (`#stlc_exp) STLC.TNat)) /\  // well typed STLC exp
        valid g (mk_rel (`STLC.TNat) fs_exp stlc_exp stlc_ht))                    // equivalent semantics
= 
  match inspect fs_exp with
  | Tv_FVar _ ->
    (* inline the top-level definition *)
    let fs_exp' = norm_term_env (`nat) g [delta] fs_exp in
    let (stlc_exp, stlc_ht) = compile_to_stlc g fs_exp' in
    rel_subst g fs_exp fs_exp' stlc_exp stlc_ht;
    assert (valid g (mk_rel (`STLC.TNat) fs_exp stlc_exp stlc_ht));
    (stlc_exp, stlc_ht)
  
  // | Tv_Const (C_Int x) ->
    // let t1 = mk_ec_int g x in
    // assume (valid g (mk_eq2 (`int) t0 (`(sem (`#t1)))));
    // t0

  | _ -> fail ("not implemented")


let valid_wtf (g:env) (phi:term) 
  : Lemma (requires valid g phi)
          (ensures squash (tot_typing g t_unit (mk_squash phi)))
  = let goal = squash (tot_typing g t_unit (mk_squash phi)) in
    assert (valid g phi ==> goal) by (compute ()); /// WHY????
    () // ????

let specialize (nm':string) (fs_exp:term) : dsl_tac_t = fun g ->
  let fs_ht : tot_typing g fs_exp (`nat) = dyn_typing () in
  FStar.Squash.return_squash fs_ht;
  let (stlc_exp, stlc_ht) = compile_to_stlc g fs_exp in
  let phi = mk_rel (`STLC.TNat) fs_exp stlc_exp stlc_ht in
  valid_wtf g phi;
  [
   mk_checked_let g nm' stlc_exp (`STLC.exp);
   mk_checked_let g (nm'^"_pf")
                    (`())
                    (mk_squash phi);
  ]
  
let src1 : nat = 4

%splice_t[tgt1;tgt1_pf] (specialize "tgt1" (`src1))
