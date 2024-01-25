module VerifiedTransform

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

let valid_wtf (g:env) (phi:term) 
  : Lemma (requires valid g phi)
          (ensures squash (tot_typing g t_unit (mk_squash phi)))
  = let goal = squash (tot_typing g t_unit (mk_squash phi)) in
    assert (valid g phi ==> goal) by (compute ()); /// WHY????
    () // ????

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

let dyn_typing (#g #ty #t : _) () : Tac (tot_typing g t ty) =
  let tok = must <| core_check_term g t ty E_Total in
  T_Token _ _ _ (Squash.return_squash tok)

let c_int_typing (g:env) (x : int) : Tac (tot_typing g (pack (Tv_Const (C_Int x))) (`int)) =
  dyn_typing ()

let fold_addition_lemma
  (g:env)
  (n m:int)
  : Lemma (valid g (mk_eq2 (`int)
                           (pack
                             (Tv_App (Tv_App (`Prims.op_Addition) (pack (Tv_Const (C_Int n)), Q_Explicit))
                                          (pack (Tv_Const (C_Int m)), Q_Explicit)))
                           (pack (Tv_Const (C_Int (n+m))))))
  = admit() // unsure if we can prove it statically, but could just call norm_term_env

let rec cfold (g:env) (t0:term) (ty:term)
  : TacP term (requires squash (tot_typing g t0 ty))
              (ensures fun t1 -> tot_typing g t1 ty /\ valid g (mk_eq2 ty t0 t1))
= 
  let fallback ()
    : TacP term
        (requires True)
        (ensures fun t1 -> tot_typing g t1 ty /\ valid g (mk_eq2 ty t0 t1))
  =
    let _ = eq2_refl g ty t0 in
    assert (tot_typing g t0 ty);
    assert (valid g (mk_eq2 ty t0 t0));
    t0
  in

  match inspect t0 with
  | Tv_FVar _ ->
    (* unfold *)
    let t1 = norm_term_env ty g [delta] t0 in
    let t2 = cfold g t1 ty in
    assert (tot_typing g t2 ty);
    eq2_trans g ty t0 t1 t2;
    t2
    
  (* detect ((op_Plus a) b) *)
  | Tv_App hd (a1, Q_Explicit) ->
    begin match inspect hd with
      | Tv_App op (a2, Q_Explicit) ->
        begin match inspect op with
        | Tv_FVar fv ->
          if inspect_fv fv = ["Prims"; "op_Addition"]
          then
            match inspect a1, inspect a2 with
            | Tv_Const (C_Int n), Tv_Const (C_Int m) ->
              assume (ty == `int); // need inversion lemma
              let res = pack (Tv_Const (C_Int (n+m))) in
              let d : tot_typing g res (`int) = c_int_typing g (n+m) in
              Squash.return_squash d;
              fold_addition_lemma g n m;
              assert (tot_typing g res (`int));
              // stupid assume, need to call pack/inspect lemma
              assume (t0 == (pack
                             (Tv_App (Tv_App (`Prims.op_Addition) (pack (Tv_Const (C_Int n)), Q_Explicit))
                                          (pack (Tv_Const (C_Int m)), Q_Explicit))));
              assert (valid g (mk_eq2 (`int) t0 res));
              res
            | _ -> fallback ()
          else
            fallback()
        | _ -> fallback()
        end
      | _ -> fallback()
    end

  | _ -> 
    (* return same term *)
    fallback()

let specialize (nm':string) (t0:term) : dsl_tac_t = fun g ->
  let c, ty = must <| core_compute_term_type g t0 in
  if c <> E_Total then fail "specialize: not total";
  let d : typing g t0 (c, ty) = T_Token _ _ _ () in
  let t1 = cfold g t0 ty in
  let phi = mk_eq2 ty t0 t1 in
  valid_wtf g phi;
  [
   mk_checked_let g nm' t1 ty;
   mk_checked_let g (nm'^"_pf")
                    (`())
                    (mk_squash phi);
  ]
  
let src1 : int = 1 + 2

%splice_t[tgt1; tgt1_pf] (specialize "tgt1" (`src1))

// tgt1 is defined to 3,
// tgt1_pf proved (src1 == 3)
