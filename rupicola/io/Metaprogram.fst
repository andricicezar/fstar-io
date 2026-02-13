module Metaprogram

open HelperTactics

open FStar.Tactics.V2
open FStar.Reflection.Typing
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data

open QExp

(** Quotation of types **)

let mk_qunit : term = mk_app (`QTyp.qUnit) []
let mk_qbool : term = mk_app (`QTyp.qBool) []
let mk_qfiledescr : term = mk_app (`QTyp.qFileDescr) []
let mk_qresexn (t:term) : term = mk_app (`QTyp.qResexn) [(t, Q_Explicit)]
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
    | "BaseTypes.file_descr" -> mk_qfiledescr
    | _ -> fail ("Type " ^ fv_to_string fv ^ " not supported")
  end

  | Tv_App l (r, _) -> begin
    let (head, app_args) = collect_app qt in
    let fv_opt =
      match inspect_ln head with
      | Tv_FVar fv -> Some fv
      | Tv_UInst fv _ -> Some fv
      | _ -> None
    in
    match fv_opt with
    | Some fv -> begin
        match fv_to_string fv, app_args with
        | "FStar.Pervasives.Native.tuple2", [(v1, _); (v2, _)] ->
          mk_qpair (typ_translation v1) (typ_translation v2)
        | "FStar.Pervasives.either", [(v1, _); (v2, _)] ->
           mk_qsum (typ_translation v1) (typ_translation v2)
        | "BaseTypes.resexn", [(v, _)] ->
           mk_qresexn (typ_translation v)
        | fnm, _ -> fail ("Type application not supported: "^ fnm ^ " - " ^ term_to_string qt)
    end
    | _ -> fail ("Type application not supported: " ^ term_to_string qt)
  end

  | Tv_Arrow b c ->  begin
    let tbv = typ_translation (binder_sort b) in
    match inspect_comp c with
    | C_Total ret -> 
      let maybe_io = 
        match inspect_ln ret with
        | Tv_App l (r, _) ->
           (match inspect_ln l with
            | Tv_FVar fv -> if fv_to_string fv = "IO.io" then Some r else None
            | _ -> None)
        | _ -> None
      in
      (match maybe_io with
       | Some r -> mk_qarrio tbv (typ_translation r)
       | None -> mk_qarr tbv (typ_translation ret))
    | _ -> fail ("not a total function type")
  end

  (** erase refinement **)
  | Tv_Refine b _ -> 
    let b = inspect_binder b in
    typ_translation b.sort

  | Tv_Unknown -> fail ("an underscore was found in the term")
  | Tv_Unsupp -> fail ("unsupported by F* terms")

  | _ -> fail ("not implemented in types: " ^ tag_of qt)

(** Quotation of expressions **)

let mk_tyj (ty t : term) : Tot term =
  let t = mk_app (`helper_oval) [(ty, Q_Implicit); (t, Q_Explicit)] in
  mk_app (`oval_quotation) [(ty, Q_Implicit); ((`QTyp.empty), Q_Explicit); (t, Q_Explicit)]
  (** environment is fixed                    ^^^^^^^^^^^^^^ **) 
let mk_qtt : term = mk_app (`Qtt) []
let mk_qfd (t:term) = mk_app (`QFd) [(t, Q_Explicit)]

let mk_qtrue : term = mk_app (`QTrue) []
let mk_qfalse : term = mk_app (`QFalse) []
let mk_qif (b:term) (t1:term) (t2:term) : term =
  mk_app (`QIf) [(b, Q_Explicit); (t1, Q_Explicit); (t2, Q_Explicit)]

let mk_qmkpair (t1:term) (t2:term) : term =
  mk_app (`QMkpair) [(t1, Q_Explicit); (t2, Q_Explicit)]
let mk_qfst (t:term) : term = mk_app (`QFst) [(t, Q_Explicit)]
let mk_qsnd (t:term) : term = mk_app (`QSnd) [(t, Q_Explicit)]

let mk_qinl (t:term) : term = mk_app (`QInl) [(t, Q_Explicit)]
let mk_qinr (t:term) : term = mk_app (`QInr) [(t, Q_Explicit)]
let mk_qcase (t:term) (x1:term) (x2:term) : term =
  mk_app (`QCase) [(t, Q_Explicit); (x1, Q_Explicit); (x2, Q_Explicit)]

let mk_qvar0 : term = mk_app (`QVar0) []
let mk_qvars (t:term) : term = mk_app (`QVarS) [(t, Q_Explicit)]
let rec mk_qvarI (n:int) : term =
  if n <= 0 then mk_qvar0
  else mk_qvars (mk_qvarI (n-1))
let mk_qlambda (body:term) : term = mk_app (`QLambda) [(body, Q_Explicit)]
let mk_qapp (f arg : term) : term = mk_app (`QApp) [(f, Q_Explicit); (arg, Q_Explicit)]

(** Map between de Brujin F* variables and LambdaIO variables **)
type db_mapping = int -> option int
let empty_mapping : db_mapping = fun _ -> None
let incr_option (x:option int) : option int =
  match x with
  | Some n -> Some (n+1)
  | None -> None
let extend_dbmap_binder (dbmap:db_mapping) : db_mapping =
  fun x -> if x = 0 then Some 0 else incr_option (dbmap (x-1))
let skip_dbmap_binder (dbmap:db_mapping) : db_mapping = fun x -> dbmap (x-1)

type fv_mapping = string -> option term
let empty_fv_mapping : fv_mapping = fun _ -> None
let extend_fv_mapping (m:fv_mapping) (nm:string) (t:term) : fv_mapping =
  fun s -> if s = nm then Some t else m s

(** Map between free F* variable F* and uninstantiated derivations **)
let rec create_derivation (dbmap:db_mapping) (fvmap:fv_mapping) (qfs:term) : Tac term =
  print ("      in exp translation: " ^ tag_of qfs);
  match inspect_ln qfs with
  | Tv_FVar fv -> begin
    print ("        looking for fvar: " ^ fv_to_string fv);
    match fvmap (fv_to_string fv) with
    | Some t -> t
    | None -> fail (fv_to_string fv ^ " not defined")
  end

  | Tv_BVar v -> begin
    let i = (inspect_bv v).index in
    match dbmap i with
    | Some i' -> mk_qvarI i'
    | None -> fail (print_nat i ^ " not defined")
  end

  | Tv_Abs bin body -> mk_qlambda (create_derivation (extend_dbmap_binder dbmap) fvmap body)
  | Tv_App hd (a, _) -> begin
    let (head, args) = collect_app qfs in
    let fv_opt =
      match inspect_ln head with
      | Tv_FVar fv -> Some fv
      | Tv_UInst fv _ -> Some fv
      | _ -> None
    in
    match fv_opt with
    | Some fv -> begin
      match fv_to_string fv, args with
      | "FStar.Pervasives.Native.Mktuple2", [_; _; (v1, _); (v2, _)] ->
        mk_qmkpair (create_derivation dbmap fvmap v1) (create_derivation dbmap fvmap v2)
      | "FStar.Pervasives.Native.fst", [_; _; (v1, _)] ->
        mk_qfst (create_derivation dbmap fvmap v1)
      | "FStar.Pervasives.Native.snd", [_; _; (v1, _)] ->
        mk_qsnd (create_derivation dbmap fvmap v1)
      | "FStar.Pervasives.Inl", [_; _; (v1, _)] ->
        mk_qinl (create_derivation dbmap fvmap v1)
      | "FStar.Pervasives.Inr", [_; _; (v1, _)] ->
        mk_qinr (create_derivation dbmap fvmap v1)
      | _ -> mk_qapp (create_derivation dbmap fvmap hd) (create_derivation dbmap fvmap a)
    end
    | _ -> mk_qapp (create_derivation dbmap fvmap hd) (create_derivation dbmap fvmap a)
  end

  | Tv_Const C_Unit -> mk_qtt
  | Tv_Const C_True -> mk_qtrue
  | Tv_Const C_False -> mk_qfalse

  | Tv_Match b _ brs -> begin
      if List.length brs <> 2 then fail ("only supporting matches with 2 branches") else ();
      print ("Got: " ^ (branches_to_string brs));
      match brs with
      | [(Pat_Constant C_True, t1); (Pat_Var _ _, t2)] -> (** if **)
      mk_qif (create_derivation dbmap fvmap b) (create_derivation dbmap fvmap t1) (create_derivation (skip_dbmap_binder dbmap) fvmap t2)
      | [(Pat_Cons fv1 _ _, t1); (Pat_Cons _ _ _, t2)] ->
        let fnm1 = fv_to_string fv1 in
        if fnm1 = "FStar.Pervasives.Inl"
        then mk_qcase (create_derivation dbmap fvmap b) (create_derivation (extend_dbmap_binder dbmap) fvmap t1) (create_derivation (extend_dbmap_binder dbmap) fvmap t2)
        else fail ("only supporting matches on inl and inr for now (in this order). Got: " ^ fnm1)
      | _ -> fail ("Only boolean matches (if-then-else) are supported. Got: " ^ (branches_to_string brs))  end


  | Tv_AscribedC t c _ _ -> begin
    match inspect_comp c with
    | C_Total _ -> create_derivation dbmap fvmap t
    | _ -> fail ("not a total function type")
  end

  | Tv_AscribedT e t _ _ -> create_derivation dbmap fvmap e
  | Tv_UInst v _ -> fail ("unexpected universe instantiation in expression: " ^ fv_to_string v)

  | _ -> fail ("not implemented in expressions: " ^ tag_of qfs)

let check_if_derivation_types_are_equal (g:env) (t:typ) (desired_t:typ) : Tac (squash (sub_typing g t desired_t)) =
  let goal_ty = mk_app (`(Prims.eq2 u#2)) [((`Type u#1), Q_Implicit); (t, Q_Explicit); (desired_t, Q_Explicit)] in
  let goal_ty = simplify_qType_g g goal_ty in (* manual unfoldings and simplifications using norm *)
  // let goal_ty = norm_term_env g [delta_qualifier ["unfold"]; zeta; iota; simplify] goal_ty in
  let u = must <| universe_of g goal_ty in
  let w : (w:term{typing_token g w (E_Total, goal_ty)}) = must <| call_subtac g (fun () -> 
    // l_to_r_fsG (); 
    trefl ()) u goal_ty in

  // we dynamically check that the types are equal (thus, extraction would fail if they are not)
  // w is proof that t == desired_t, but it is a typing_token and not a sub_typing token
  // how to go from one to the other?
  assume (sub_typing g t desired_t)

let type_check_derivation g (qderivation:term) (desired_qtyp:term)  : Tac (r:(term & term){tot_typing g (fst r) (snd r)}) =
  let (_, qderivation, desired_qtyp) = must <| instantiate_implicits g qderivation (Some desired_qtyp) true in
  let (qderivation, (eff, qtyp)) = must <| tc_term g qderivation in (** type check the derivation, it gets its own type **)
  if E_Ghost? eff then fail "derivation is not a total type. impossible!"
  else begin
    check_if_derivation_types_are_equal g qtyp desired_qtyp;

    token_as_typing g qderivation eff qtyp;
    lem_retype_expression g qderivation qtyp desired_qtyp;

    (qderivation, desired_qtyp)
  end

let create_and_type_check_derivation g (dbmap:db_mapping) (fvmap:fv_mapping) (qprog:term) (desired_qtyp:term) : Tac (term & r:(term & term){tot_typing g (fst r) (snd r)}) =
  let qderivation = create_derivation dbmap fvmap qprog in
  qderivation, type_check_derivation g qderivation desired_qtyp

let top_level_def_translation g (dbmap:db_mapping) (fvmap:fv_mapping) (qprog:term) : Tac (string & (term & r:(term & term){tot_typing g (fst r) (snd r)})) =
  print "  in top_level_def_translation\n";
  let (qprog, (_, qtyp)) = must <| tc_term g qprog in (** one has to dynamically retype the term to get its type **)
  let derivation_typ = mk_tyj (typ_translation qtyp) qprog in
  match inspect_ln qprog with
  | Tv_FVar fv -> begin
    let fnm = fv_to_string fv in
    print ("    def: " ^ fnm ^ "\n");
    let qprog' = norm_term_env g [delta_only [fnm]; zeta] qprog in
    match inspect_ln qprog' with
    | Tv_FVar fv' ->
      if fnm = fv_to_string fv' then fail (fnm ^ " does not unfold!")
      else (fnm, create_and_type_check_derivation g dbmap fvmap qprog' derivation_typ)
    | _ -> (fnm, create_and_type_check_derivation g dbmap fvmap qprog' derivation_typ)
  end
  | _ -> fail ("not top-level definition")

let rec translate_list_of_qprogs g dbmap (fvmap:fv_mapping) (qprogs:(list term){List.length qprogs > 0}) : Tac (r:(term & term){tot_typing g (fst r) (snd r)}) =
  match qprogs with
  | qprog :: [] -> 
      let (_, (_, qderiv)) = top_level_def_translation g dbmap fvmap qprog in
      qderiv
  | qprog :: tl -> 
    let (fnm, (uni_qderiv, (qderiv, _))) = top_level_def_translation g dbmap fvmap qprog in
    print ("Translated " ^ fnm ^ "\n");
    translate_list_of_qprogs g dbmap (extend_fv_mapping fvmap fnm uni_qderiv) tl

let meta_translation (nm:string) (qprogs:(list term){List.length qprogs > 0}) : dsl_tac_t = fun (g, expected_t) ->
  match expected_t with
  | Some t -> fail ("expected type " ^ tag_of t ^ " not supported")
  | None -> begin
    let (qderivation, qtyp_derivation) = translate_list_of_qprogs g empty_mapping empty_fv_mapping qprogs in
    dump (term_to_string qderivation ^ " : " ^ term_to_string qtyp_derivation);
    ([], mk_checked_let g (cur_module ()) nm qderivation qtyp_derivation, [])
  end

(** Unit tests **)

// #push-options "--no_smt"

%splice_t[tgt1] (meta_translation "tgt1" [(`Examples.ut_unit)])
let _ = assert (tgt1 == test_ut_unit) by (trefl ())

%splice_t[tgt2] (meta_translation "tgt2" [`Examples.ut_true])
let _ = assert (tgt2 == test_ut_true) by (trefl ())

%splice_t[tgt3] (meta_translation "tgt3" [`Examples.ut_false])
let _ = assert (tgt3 == test_ut_false) by (trefl ())



%splice_t[tgt4] (meta_translation "tgt4" [`Examples.constant])

let _ = assert (tgt4 == test_constant) by (trefl ())

%splice_t[tgt5] (meta_translation "tgt5" [`Examples.identity])
let _ = assert (tgt5 == test_identity) by (trefl ())

%splice_t[tgt6] (meta_translation "tgt6" [`Examples.thunked_id])
let _ = assert (tgt6 == test_thunked_id) by (trefl ())

%splice_t[tgt7] (meta_translation "tgt7" [`Examples.proj1])
let _ = assert (tgt7 == test_proj1) by (trefl ())
%splice_t[tgt8] (meta_translation "tgt8" [`Examples.proj2])
let _ = assert (tgt8 == test_proj2) by (trefl ())
%splice_t[tgt9] (meta_translation "tgt9" [`Examples.proj3])
let _ = assert (tgt9 == test_proj3) by (trefl ())

%splice_t[tgt10] (meta_translation "tgt10" [`Examples.apply_arg])
let _ = assert (tgt10 == test_apply_arg) by (trefl ())


%splice_t[tgt11] (meta_translation "tgt11" [`Examples.apply_arg2])
let _ = assert (tgt11 == test_apply_arg2 ()) by (trefl ())


%splice_t[tgt12] (meta_translation "tgt12" [`Examples.papply_arg2])
let _ = assert (tgt12 == test_papply_arg2 ()) by (trefl ())

%splice_t[tgt13] (meta_translation "tgt13" [`Examples.negb])
let _ = assert (tgt13 == test_negb) by (trefl ())

%splice_t[tgt14] (meta_translation "tgt14" [`Examples.if2])
let _ = assert (tgt14 == test_if2 ()) by (trefl ())

%splice_t[tgt15] (meta_translation "tgt15" [`Examples.callback_return])
let _ = assert (tgt15 == test_callback_return ()) by (trefl ())


%splice_t[tgt_make_pair] (meta_translation "tgt_make_pair" [`Examples.make_pair])
let _ = assert (tgt_make_pair == test_make_pair) by (trefl ())

%splice_t[tgt_fst_pair] (meta_translation "tgt_fst_pair" [`Examples.fst_pair])
let _ = assert (tgt_fst_pair == test_fst_pair) by (trefl ())

%splice_t[tgt_wrap_fst] (meta_translation "tgt_wrap_fst" [`Examples.wrap_fst])
let _ = assert (tgt_wrap_fst == test_wrap_fst) by (trefl ())

%splice_t[tgt_snd_pair] (meta_translation "tgt_snd_pair" [`Examples.snd_pair])
let _ = assert (tgt_snd_pair == test_snd_pair) by (trefl ())

%splice_t[tgt_wrap_snd] (meta_translation "tgt_wrap_snd" [`Examples.wrap_snd])
let _ = assert (tgt_wrap_snd == test_wrap_snd) by (trefl ())

%splice_t[tgt_a_few_lets] (meta_translation "tgt_a_few_lets" [`Examples.a_few_lets])
let _ = assert (tgt_a_few_lets == QLambda Qtt) by (trefl ())

%splice_t[tgt_inl_true] (meta_translation "tgt_inl_true" [`Examples.inl_true])
let _ = assert (tgt_inl_true == test_inl_true) by (trefl ())

%splice_t[tgt_inr_unit] (meta_translation "tgt_inr_unit" [`Examples.inr_unit])
let _ = assert (tgt_inr_unit == test_inr_unit) by (trefl ())

%splice_t[tgt_return_either] (meta_translation "tgt_return_either" [`Examples.return_either])
let _ = assert (tgt_return_either == test_return_either ()) by (trefl ())

%splice_t[tgt_match_either] (meta_translation "tgt_match_either" [`Examples.match_either])
let _ = assert (tgt_match_either == test_match_either ()) by (trefl ())


%splice_t[tgt_match_either_arg] (meta_translation "tgt_match_either_arg" [`Examples.match_either_arg])
let _ = assert (tgt_match_either_arg == test_match_either_arg ()) by (trefl ())


%splice_t[tgt_apply_top_level_def] (meta_translation "tgt_apply_top_level_def" [(`Examples.thunked_id);(`Examples.apply_top_level_def)])

%splice_t[tgt_apply_top_level_def'] (meta_translation "tgt_apply_top_level_def'" [`Examples.thunked_id;`Examples.apply_top_level_def'])

%splice_t[tgt_papply_top_level_def] (meta_translation "tgt_papply_top_level_def" [`Examples.thunked_id;`Examples.papply__top_level_def])

%splice_t[tgt16] (meta_translation "tgt16" [`Examples.identity;`Examples.callback_return'])
let _ = assert (tgt16 == test_callback_return' ()) by (trefl ())

%splice_t[tgt_pair_of_functions] (meta_translation "tgt_pair_of_functions" [`Examples.negb;`Examples.pair_of_functions])

[@@ (preprocess_with simplify_qType)]
let test () = assert (tgt_pair_of_functions == test_pair_of_functions ()) by (trefl ())
