module Metaprogram

open HelperTactics

open FStar.Tactics.Typeclasses
open FStar.Tactics.V2
open FStar.Reflection.Typing
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data

open QExp

let mk_qunit : term = mk_app (`QTyp.qUnit) []
let mk_qbool : term = mk_app (`QTyp.qBool) []
let mk_qarr (t1 t2:term) : term = mk_app (`QTyp.op_Hat_Subtraction_Greater) [(t1, Q_Explicit); (t2, Q_Explicit)]
let mk_qarrio (t1 t2:term) : term = mk_app (`QTyp.op_Hat_Subtraction_Greater_Bang_At) [(t1, Q_Explicit); (t2, Q_Explicit)]
let mk_qpair (t1 t2:term) : term = mk_app (`QTyp.op_Hat_Star) [(t1, Q_Explicit); (t2, Q_Explicit)]
let mk_qsum (t1 t2:term) : term = mk_app (`QTyp.op_Hat_Plus) [(t1, Q_Explicit); (t2, Q_Explicit)]

let rec typ_translation (qt:term) : Tac term = 
  match inspect_ln qt with
  | Tv_FVar fv -> begin
    match fv_to_string fv with
    | "Prims.unit" -> mk_qunit
    | "Prims.bool" -> mk_qbool
    | _ -> fail ("Type " ^ fv_to_string fv ^ " not supported")
  end

  | Tv_Arrow b c ->  begin
    let tbv = typ_translation (binder_sort b) in
    match inspect_comp c with
    | C_Total ret -> 
      let tc = typ_translation ret in
      mk_qarr tbv tc
    | _ -> fail ("not a total function type")
  end

  (** erase refinement **)
  | Tv_Refine b _ -> 
    let b = inspect_binder b in
    typ_translation b.sort

  | Tv_Unknown -> fail ("an underscore was found in the term")
  | Tv_Unsupp -> fail ("unsupported by F* terms")

  | _ -> fail ("not implemented: " ^ tag_of qt)


let mk_tyj (ty t : term) : Tot term =
  let t = mk_app (`helper_oval) [(ty, Q_Implicit); (t, Q_Explicit)] in
  mk_app (`oval_quotation) [(ty, Q_Implicit); ((`QTyp.empty), Q_Explicit); (t, Q_Explicit)]

let mk_qtt : term = mk_app (`Qtt) []
let mk_qfd (t:term) = mk_app (`QFd) [(t, Q_Explicit)]
let mk_qtrue : term = mk_app (`QTrue) []

let mk_qfalse : term = mk_app (`QFalse) []

let mk_qvar0 : term = mk_app (`QVar0) []

let mk_qvars (t:term) : term = mk_app (`QVarS) [(t, Q_Explicit)]

let rec mk_qvarI (n:nat) : term =
  if n = 0 then mk_qvar0
  else mk_qvars (mk_qvarI (n-1))

let mk_qlambda (body:term) : term = mk_app (`QLambda) [(body, Q_Explicit)]

let mk_qapp (f arg : term) : term = mk_app (`QApp) [(f, Q_Explicit); (arg, Q_Explicit)]

noeq
type fs_var =
| FVar : fv -> fs_var
| BVar : var -> fs_var

type mapping =
  fs_var -> option nat

let empty_mapping : mapping = fun _ -> None

let incr_option (x:option nat) : option nat =
  match x with
  | Some n -> Some (n+1)
  | None -> None

let extend_gmap_binder (gmap:mapping)
  : mapping =
  (fun x -> match x with
      | BVar v -> if v = 0 then Some 0 else incr_option (gmap (BVar (v-1))) //Some v
      | _ -> incr_option (gmap x))

let extend_gmap (gmap:mapping) (b:string) : mapping =
  (fun x -> match x with
      | FVar v -> if fv_to_string v = b then Some 0 else (incr_option (gmap x))
      | _ -> (incr_option (gmap x)))

let rec exp_translation
  g
  (gmap:mapping)
  (qfs:term)
  : Tac term =
  print ("      in exp translation: " ^ tag_of qfs);
  match inspect_ln qfs with
  // | Tv_FVar fv -> begin
  //   let fnm = fv_to_string fv in
  //   print ("    def: " ^ fnm ^ "\n");
  //   let qdef' = norm_term_env g [delta_only [fnm]; zeta] qfs in
  //   match inspect_ln qdef' with
  //   | Tv_FVar fv' ->
  //     if fnm = fv_to_string fv' then fail (fnm ^ " does not unfold!")
  //     else exp_translation g gmap qdef'
  //   | _ -> exp_translation g gmap qdef'
  //   // print ("        looking for fvar: " ^ fv_to_string fv);
  //   // match gmap (FVar fv) with
  //   // | Some v -> mk_qvarI v
  //   // | None -> fail (fv_to_string fv ^ " not defined")
  // end

  | Tv_BVar v -> begin
    let i = (inspect_bv v).index in
    match gmap (BVar i) with
    | Some i' -> mk_qvarI i'
    | None -> fail (print_nat i ^ " not defined")
  end

  | Tv_Abs bin body -> mk_qlambda (exp_translation g (extend_gmap_binder gmap) body)
  | Tv_App hd (a, _) -> mk_qapp (exp_translation g gmap hd) (exp_translation g gmap a)

  | Tv_Const C_Unit -> mk_qtt
  | Tv_Const C_True -> mk_qtrue
  | Tv_Const C_False -> mk_qfalse

  | Tv_AscribedC t c _ _ -> begin
    match inspect_comp c with
    | C_Total _ -> exp_translation g gmap t
    | _ -> fail ("not a total function type")
  end

  | _ -> fail ("not implemented: " ^ tag_of qfs)

let rec def_translation g (gmap:mapping) (qdef:term) : Tac (string * term) =
  print "  in def translation\n";
  match inspect_ln qdef with
  | Tv_FVar fv -> begin
    let fnm = fv_to_string fv in
    print ("    def: " ^ fnm ^ "\n");
    let qdef' = norm_term_env g [delta_only [fnm]; zeta] qdef in
    match inspect_ln qdef' with
    | Tv_FVar fv' ->
      if fnm = fv_to_string fv' then fail (fnm ^ " does not unfold!")
      else def_translation g gmap qdef'
    | _ -> (fnm, exp_translation g gmap qdef')
  end
  | _ -> fail ("not top-level definition")

let token_as_typing (g:env) (e:term) (eff:tot_or_ghost) (ty:typ)
  : Lemma
    (requires typing_token g e (eff, ty))
    (ensures typing g e (eff, ty)) =
    assert (typing_token g e (eff, ty));
    Squash.return_squash (T_Token _ _ _ (Squash.get_proof (typing_token g e (eff, ty))))
    // (fst r, snd (snd r))

let check_if_ovals_are_equal (g:env) (t:typ) (desired_t:typ) : Tac (squash (sub_typing g t desired_t)) =
  let goal_ty = mk_app (`(Prims.eq2 u#2)) [((`Type u#1), Q_Implicit); (t, Q_Explicit); (desired_t, Q_Explicit)] in
  let goal_ty = simplify_qType_g g goal_ty in (* manual unfoldings and simplifications using norm *)
  let u = must <| universe_of g goal_ty in
  let w : (w:term{typing_token g w (E_Total, goal_ty)}) = must <| call_subtac g (fun () -> 
    // l_to_r_fsG (); 
    trefl ()) u goal_ty in (** funny that trefl works better than using the check_subtyping **)
  // w is proof that t == desired_t, but I have a typing_token and not sub_typing
  assume (sub_typing g t desired_t)

let lem_retype_expression g e (t:typ{tot_typing g e t}) (desired_t:typ) :
  Lemma (requires tot_typing g e t /\ sub_typing g t desired_t)
        (ensures tot_typing g e desired_t) =
  Squash.bind_squash #(typing g e (E_Total, t)) () (fun d_typing ->
    Squash.bind_squash #(sub_typing g t desired_t) () (fun d_sub ->
      let d_sub_comp = Relc_typ g t desired_t E_Total R_Sub d_sub in
      let d_res = T_Sub g e (E_Total, t) (E_Total, desired_t) d_typing d_sub_comp in
      Squash.return_squash d_res))

let translation g (qprog:term) (qtyp:term) : Tac (r:(term & term){tot_typing g (fst r) (snd r) }) =
  let desired_qtyp_derivation = mk_tyj qtyp qprog in
  let (_, qderivation) = def_translation g empty_mapping qprog in

  let (_, qderivation, desired_qtyp_derivation) = must <| instantiate_implicits g qderivation (Some desired_qtyp_derivation) true in
  let (qderivation, (eff, qtyp_derivation)) = must <| tc_term g qderivation in
  if E_Ghost? eff then fail "not a total function type"
  else begin
    check_if_ovals_are_equal g qtyp_derivation desired_qtyp_derivation;

    token_as_typing g qderivation eff qtyp_derivation;
    lem_retype_expression g qderivation qtyp_derivation desired_qtyp_derivation;

    (qderivation, desired_qtyp_derivation)
  end

open FStar.Tactics.Typeclasses

let meta_translation (nm:string) (qprog:term) : dsl_tac_t = fun (g, expected_t) ->
  match expected_t with
  | Some t -> fail ("expected type " ^ tag_of t ^ " not supported")
  | None -> begin
    let (qprog, (eff, qtyp)) = must <| tc_term g qprog in (** one has to dynamically retype the term to get its type **)
    let (qderivation, qtyp_derivation) = translation g qprog (typ_translation qtyp) in
    ([], mk_checked_let g (cur_module ()) nm qderivation qtyp_derivation, [])
  end

open QTyp


#push-options "--no_smt"

%splice_t[tgt1] (meta_translation "tgt1" (`Examples.ut_unit))
let _ = assert (tgt1 == test_ut_unit) by (trefl ())

%splice_t[tgt2] (meta_translation "tgt2" (`Examples.ut_true))
let _ = assert (tgt2 == test_ut_true) by (trefl ())

%splice_t[tgt3] (meta_translation "tgt3" (`Examples.ut_false))
let _ = assert (tgt3 == test_ut_false) by (trefl ())



%splice_t[tgt4] (meta_translation "tgt4" (`Examples.constant))

let _ = assert (tgt4 == test_constant) by (trefl ())

%splice_t[tgt5] (meta_translation "tgt5" (`Examples.identity))
let _ = assert (tgt5 == test_identity) by (trefl ())

%splice_t[tgt6] (meta_translation "tgt6" (`Examples.thunked_id))
let _ = assert (tgt6 == test_thunked_id) by (trefl ())

%splice_t[tgt7] (meta_translation "tgt7" (`Examples.proj1))
let _ = assert (tgt7 == test_proj1) by (trefl ())
%splice_t[tgt8] (meta_translation "tgt8" (`Examples.proj2))
let _ = assert (tgt8 == test_proj2) by (trefl ())
%splice_t[tgt9] (meta_translation "tgt9" (`Examples.proj3))
let _ = assert (tgt9 == test_proj3) by (trefl ())

%splice_t[tgt10] (meta_translation "tgt10" (`Examples.apply_arg))
let _ = assert (tgt10 == test_apply_arg) by (trefl ())



%splice_t[tgt11] (meta_translation "tgt11" (`Examples.apply_arg2))
let _ = assert (tgt11 == test_apply_arg2 ()) by (trefl ())


%splice_t[tgt12] (meta_translation "tgt12" (`Examples.papply_arg2))
let _ = assert (tgt12 == test_papply_arg2 ()) by (trefl ())
