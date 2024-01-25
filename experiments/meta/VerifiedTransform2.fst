module VerifiedTransform2

open FStar.Tactics.V2
open FStar.Reflection.V2
open FStar.Reflection.Typing
include VerifiedTransform

let src1 : int = 1 + 2 + 3

val is_nat_ctrct : int -> option nat
let is_nat_ctrct x =
  if x > 0 then Some x
  else None

val is_nat_pred : int -> option nat -> Type0
let is_nat_pred x y = x > 0 <==> Some? y

// let forall_pred (p:'a -> Type0) = forall x. p x

val forall_ex_pred : ('a -> 'b) -> ('a -> 'b -> Type0) -> Type0
// let forall_ex_pred f p = forall_pred (fun x -> p x (f x))
let forall_ex_pred f p = forall x. p x (f x)

let _ = assert (forall_ex_pred is_nat_ctrct is_nat_pred)

let _ = assert (is_nat_pred src1 (is_nat_ctrct src1))

(**
    Goal: prove that 
        valid g (Tv_App is_nat_ctrct src1) (mk_is_nat_pred src1 (is_nat_ctrct src1))
**)

let mk_arrow (dom:term) (codom:term) : typ =
  pack_ln (Tv_Arrow (binder_of_t_q dom Q_Explicit) (pack_comp (C_Total codom)))

// let mk_forall_pred (p:term) : term = pack_ln (Tv_App (`forall_pred) (p, Q_Explicit))

let mk_forall_ex_pred (f_t:term) (p_t:term) : typ =
  pack_ln (
    Tv_App
        (pack_ln (Tv_App (`forall_ex_pred) (f_t, Q_Explicit)))
        (p_t, Q_Explicit))

let mk_wit_ex_pred (p_t:term) (x_t:term) (y_t:term) : typ =
  pack_ln
    (Tv_App
      (pack_ln (Tv_App p_t (x_t, Q_Explicit)))
      (y_t, Q_Explicit))

// val univ_instan : (#a:Type) -> p:(a -> Type0) -> (pa : squash (forall_pred p)) -> (x:a) -> squash (p x)
// let univ_instan p pa x = assert (p x)

// let univ_instan_t (g:env) (p:term) (x1:term)
//   : Lemma
//     (requires (valid g (mk_forall_pred p)))
//     (ensures  (valid g (pack_ln (Tv_App p (x1, Q_Explicit)))))
//   =
//     admit ()

let t_app_lemma
  (#dom:term)
  (#codom:term)
  (g:env)
  (f_t:term)
  (x_t:term)
  (f_tyj:tot_typing g f_t (mk_arrow dom codom))
  (x_tyj:tot_typing g x_t dom)
  : Lemma (
    tot_typing g (pack_ln (Tv_App f_t (x_t, Q_Explicit))) (open_with codom x_t))
  = FStar.Squash.return_squash (
      T_App g f_t x_t (binder_of_t_q dom Q_Explicit) codom E_Total f_tyj x_tyj)

(** syntactic application, but proving that extrinsic properties are preserved **)
let syntactic_app #ty_a #ty_b (g:env) (f_t:term) (p_t:term) (x_t:term)
  : Pure (term * term)
      (requires 
        tot_typing g f_t (mk_arrow ty_a ty_b) /\
        tot_typing g x_t ty_a /\
        tot_typing g p_t (mk_arrow ty_a (mk_arrow ty_b (`Type0))) /\
        valid g (mk_forall_ex_pred f_t p_t))     // object level: forall x. p x (f x)
      (ensures fun (fx_t, fx_ty) -> 
        tot_typing g fx_t fx_ty /\
        valid g (mk_wit_ex_pred p_t x_t fx_t))   // object level: p t0 t1
  = 
    let fx_t:term = pack_ln (Tv_App f_t (x_t, Q_Explicit)) in
    
    // proving first conjunct
    assert (valid g (mk_forall_ex_pred f_t p_t));  
    // squash (tot_typing g t_unit (mk_squash (mk_forall_ex_pred f_t p_t)))
    // <==> unfold mk_forall_ex_pred
    // squash (tot_typing g t_unit (mk_squash (`(forall x. p x (f x)))))
    // ==> instantiate with t0
    // squash (tot_typing g t_unit (mk_squash (`(p t0 (f t0)))))
    // <==> t1 == Tv_App f_t (t0, Q_Explicit)
    // squash (tot_typing g t_unit (mk_squash (`(p t0 t1))))
    // <==> unfold mk_with_pred
    // squash (tot_typing g t_unit (mk_squash (mk_wit_ex_pred p_t t0 t1)))
    assume (valid g (mk_wit_ex_pred p_t x_t fx_t));

    // proving second conjuct
    FStar.Classical.forall_intro_2 (t_app_lemma #ty_a #ty_b g f_t x_t);
    assert (tot_typing g f_t (mk_arrow ty_a ty_b));
    assert (tot_typing g x_t ty_a);
    assert (tot_typing g fx_t (open_with ty_b x_t)) by ();

    // return
    fx_t, open_with ty_b x_t


(**
  Here, I want to write a function that applies and unfolds the contract.

  Should I also do the wrapping here? Or should I just normalize?
  > I suppose just normalizing would be enough, since it may be difficult to do.
  Is enough for normalization to promise equality, or do we want something more like: forall p. p t0 ==> p (norm [..] t0)?
  > I expect equality to be enough...
  This function seems "easy" to write because it seems that we only need to normalize. In future we want to
  deal with type classes too, which usually are a pain to unfold.
**)


let evaluate_fv (g:env) (fv:string) (e0:term) (ty:term)
  : TacP term (requires squash (tot_typing g e0 ty))
              (ensures fun e1 -> tot_typing g e1 ty /\ valid g (mk_eq2 ty e0 e1))
= let e1 = norm_term_env ty g [delta_only [fv]] e0 in
  assert (tot_typing g e1 ty);
  assert (valid g (mk_eq2 ty e0 e1));
  e1

let apply_step_1 (g:env) (e0:term)
  : TacP term
      (requires tot_typing g e0 (`int) /\
                tot_typing g (`is_nat_ctrct) (mk_arrow (`int) (`option nat)) /\
                tot_typing g (`is_nat_pred) (mk_arrow (`int) (mk_arrow (`option nat) (`Type0))) /\
                valid g (mk_forall_ex_pred (`is_nat_ctrct) (`is_nat_pred)))
      (ensures fun e1 -> tot_typing g e1 (open_with (`option nat) e0) /\ // TODO: can the open_with be unfolded?
                         valid g (mk_wit_ex_pred (`is_nat_pred) e0 e1))
= 
  let e1, e1_ty = syntactic_app #(`int) #(`option nat) g (`is_nat_ctrct) (`is_nat_pred) e0 in
  assert (valid g (mk_wit_ex_pred (`is_nat_pred) e0 e1));
  let e1' = evaluate_fv g (`%is_nat_ctrct) e1 e1_ty in
  e1

// TODO: instantiate apply_step_1 and get the result + proof


let compile (nm':string) (e0:term) : dsl_tac_t = fun g ->
  // TODO: why is this not working. why does it have to be dynamic?
  //    assert (tot_typing g e0 (`int));
  // basically the following 4 lines are preconditions
  let typ0 : tot_typing g e0 (`int) = dyn_typing () in
  // TODO: fails to check that is_nat_ctrct is an arrow
  let typ1 : tot_typing g (`is_nat_ctrct) (mk_arrow (`int) (`option nat)) = dyn_typing () in
  dump "H";
  let typ2 : tot_typing g (`is_nat_pred) (mk_arrow (`int) (mk_arrow (`option nat) (`Type0))) = dyn_typing () in
  let typ3 : tot_typing g t_unit (mk_squash (mk_forall_ex_pred (`is_nat_ctrct) (`is_nat_pred))) = dyn_typing () in
  FStar.Squash.return_squash typ0;
  FStar.Squash.return_squash typ1;
  FStar.Squash.return_squash typ2;
  FStar.Squash.return_squash typ3;
  let e1 = apply_step_1 g e0 in
  let phi = mk_wit_ex_pred (`is_nat_pred) e0 e1 in
  valid_wtf g phi;
  [
   mk_checked_let g nm' e1 (open_with (`option nat) e0);
   mk_checked_let g (nm'^"_pf")
                    (`())
                    (mk_squash phi);
  ]

%splice_t[tgt1; tgt1_pf] (compile "tgt1" (`src1))


