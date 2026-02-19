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
let mk_qstring : term = mk_app (`QTyp.qString) []
let mk_qstringlit (s:term) : term = mk_app (`QStringLit) [(s, Q_Explicit)]
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
    | "Prims.string" -> mk_qstring
    | _ -> fail ("Type " ^ fv_to_string fv ^ " not supported")
  end

  | Tv_App l (r, _) -> begin
    let (head, app_args) = collect_app qt in
    match get_fv head with
    | Some fv -> begin
        match fv, app_args with
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
        | Tv_App l (r, _) -> begin
          match get_fv l with
          | Some "IO.io" -> Some r
          | _ -> None
        end
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

let mk_qeq_string (v1 v2 : term) : term =
  mk_app (`QStringEq) [(v1, Q_Explicit); (v2, Q_Explicit)]

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

let mk_qlambdaprod (body:term) : term = mk_app (`QLambdaProd) [(body, Q_Explicit)]
let mk_qappprod (f arg : term) : term = mk_app (`QAppProd) [(f, Q_Explicit); (arg, Q_Explicit)]
let mk_qopenfile (fd:term) : term = mk_app (`QOpenfile) [(fd, Q_Explicit)]
let mk_qread (fd:term) : term = mk_app (`QRead) [(fd, Q_Explicit)]
let mk_qwrite (fd:term) (b:term) : term = mk_app (`QWrite) [(fd, Q_Explicit); (b, Q_Explicit)]
let mk_qclose (fd:term) : term = mk_app (`QClose) [(fd, Q_Explicit)]
let mk_qreturn (t:term) : term = mk_app (`QReturn) [(t, Q_Explicit)]
let mk_qbind (e:term) (f:term) : term = mk_app (`QBindProd) [(e, Q_Explicit); (f, Q_Explicit)]
let mk_qifprod (b:term) (t1:term) (t2:term) : term =
  mk_app (`QIfProd) [(b, Q_Explicit); (t1, Q_Explicit); (t2, Q_Explicit)]
let mk_qcaseprod (t:term) (x1:term) (x2:term) : term =
  mk_app (`QCaseProd) [(t, Q_Explicit); (x1, Q_Explicit); (x2, Q_Explicit)]

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

(** Map between de Brujin F* variables and their F* types **)
type bt_mapping = int -> option typ
let empty_btmap : bt_mapping = fun _ -> None
let extend_btmap (btmap:bt_mapping) (bt:typ) : bt_mapping =
  fun x -> if x = 0 then Some bt else btmap (x-1)
let extend_btmap_unknown (btmap:bt_mapping) : bt_mapping =
  fun x -> if x = 0 then None else btmap (x-1)
let skip_btmap (btmap:bt_mapping) : bt_mapping = fun x -> btmap (x-1)

(** Resolve the F* type of a subterm using the binder type map **)
let rec resolve_term_type (g:env) (btmap:bt_mapping) (t:term) : Tac (option typ) =
  match inspect_ln t with
  | Tv_BVar v -> btmap (inspect_bv v).index
  | Tv_FVar _ | Tv_UInst _ _ ->
    (match tc_term g t with
     | Some (_, (_, ty)), _ -> Some ty
     | _ -> None)
  | Tv_App hd (a, _) ->
    (match resolve_term_type g btmap hd with
     | Some hd_ty ->
       (match inspect_ln hd_ty with
        | Tv_Arrow _ c ->
          (match inspect_comp c with
           | C_Total ret -> Some ret
           | _ -> None)
        | _ -> None)
     | None -> None)
  | _ -> None

(** Check if applying one argument to hd produces an IO type **)
let app_result_is_io (g:env) (btmap:bt_mapping) (hd:term) : Tac bool =
  match resolve_term_type g btmap hd with
  | Some hd_ty ->
    (match inspect_ln hd_ty with
     | Tv_Arrow _ c ->
       (match inspect_comp c with
        | C_Total ret ->
          (match inspect_ln ret with
           | Tv_App l _ ->
             (match get_fv l with
              | Some "IO.io" -> true
              | _ -> false)
           | _ -> false)
        | _ -> false)
     | _ -> false)
  | None -> false

let is_oprod (t:term) : Tac bool =
  let (h, _) = collect_app t in
  match inspect_ln h with
  | Tv_FVar fv ->
     let s = fv_to_string fv in
     s = "QExp.QReturn" || s = "QExp.QBindProd" || s = "QExp.QAppProd" ||
     s = "QExp.QRead" || s = "QExp.QWrite" || s = "QExp.QOpenfile" || s = "QExp.QClose" ||
     s = "QExp.QCaseProd" || s = "QExp.QIfProd"
  | _ -> false

let is_lambdaprod (t:term) : Tac bool =
  let (h, _) = collect_app t in
  match inspect_ln h with
  | Tv_FVar fv ->
     let s = fv_to_string fv in
     s = "QExp.QLambdaProd"
  | _ -> false

let rec create_derivation g (dbmap:db_mapping) (btmap:bt_mapping) (fuel:int) (qfs:term) : Tac term =
  if fuel <= 0 then
    fail ("Unfolding depth exceeded while processing: " ^ tag_of qfs ^ " — " ^ term_to_string qfs
          ^ "\nThis likely means an unsupported primitive (e.g., op_Equality, op_Hat) was encountered.")
  else
  let _ = print ("      in exp translation: " ^ tag_of qfs) in
  match inspect_ln qfs with
  | Tv_FVar fv -> begin
    let fnm = fv_to_string fv in
    print ("        looking for fvar: " ^ fnm);
    let qfs' = norm_term_env g [delta_only [fnm]; zeta] qfs in
    match inspect_ln qfs' with
    | Tv_FVar fv' ->
      if fnm = fv_to_string fv' then fail (fnm ^ " does not unfold in create_derivation!")
      else create_derivation g dbmap btmap (fuel - 1) qfs'
    | _ -> create_derivation g dbmap btmap (fuel - 1) qfs'
  end

  | Tv_BVar v -> begin
    let i = (inspect_bv v).index in
    match dbmap i with
    | Some i' -> mk_qvarI i'
    | None -> fail (print_nat i ^ " not defined")
  end

  | Tv_Abs bin body ->
    let qbody = create_derivation g (extend_dbmap_binder dbmap) (extend_btmap btmap (binder_sort bin)) fuel body in
    if is_oprod qbody then mk_qlambdaprod qbody
    else mk_qlambda qbody

  | Tv_App hd (a, _) -> begin
    let (head, args) = collect_app qfs in
    let explicit_args : list term =
      args |> List.Tot.filter (fun (_, q) -> Q_Explicit? q) |> List.Tot.map fst in
    match get_fv head, explicit_args with
    | Some "FStar.Pervasives.Native.Mktuple2", [v1; v2] ->
      mk_qmkpair (create_derivation g dbmap btmap fuel v1) (create_derivation g dbmap btmap fuel v2)
    | Some "FStar.Pervasives.Native.fst", [v1] ->
      mk_qfst (create_derivation g dbmap btmap fuel v1)
    | Some "FStar.Pervasives.Native.snd", [v1] ->
      mk_qsnd (create_derivation g dbmap btmap fuel v1)
    | Some "FStar.Pervasives.Inl", [v1] ->
      mk_qinl (create_derivation g dbmap btmap fuel v1)
    | Some "FStar.Pervasives.Inr", [v1] ->
      mk_qinr (create_derivation g dbmap btmap fuel v1)
    | Some "IO.io_return", [v] ->
      mk_qreturn (create_derivation g dbmap btmap fuel v)
    | Some "IO.return", [v] ->
      mk_qreturn (create_derivation g dbmap btmap fuel v)
    | Some "IO.openfile", [v] ->
      mk_qopenfile (create_derivation g dbmap btmap fuel v)
    | Some "IO.read", [v] ->
      mk_qread (create_derivation g dbmap btmap fuel v)
    | Some "IO.close", [v] ->
      mk_qclose (create_derivation g dbmap btmap fuel v)
    | Some "IO.write", [v] -> begin
      let (h, as_) = collect_app v in
      match get_fv h, as_ with
      | Some "FStar.Pervasives.Native.Mktuple2", [_; _; (v1, _); (v2, _)] ->
        mk_qwrite (create_derivation g dbmap btmap fuel v1) (create_derivation g dbmap btmap fuel v2)
      | _ -> fail "IO.write argument is not a tuple structure"
    end
    | Some "IO.op_let_Bang_At", [m; k]
    | Some "IO.io_bind", [m; k] -> begin
      let qm = create_derivation g dbmap btmap fuel m in
      match inspect_ln k with
      | Tv_Abs bin body ->
        let qk = create_derivation g (extend_dbmap_binder dbmap) (extend_btmap btmap (binder_sort bin)) fuel body in
        mk_qbind qm qk
      | _ -> fail "IO.io_bind continuation is not a lambda"
    end
    | Some "ExamplesIO.eq_string", [v1; v2] ->
      mk_qeq_string (create_derivation g dbmap btmap fuel v1) (create_derivation g dbmap btmap fuel v2)
    | Some "ExamplesIO.op_let_Bang_At_Bang", [m; k] -> begin
      (** let!@! m k = match!@ m with Inl x -> k x | Inr y -> return (Inr y)
          Translates to: QBindProd m (QCaseProd QVar0 (k_body) (QReturn (QInr QVar0)))
          The dbmap for k_body needs two shifts (bind + case) but only one new binder from k's lambda.
          So we shift existing mappings by 1 (for the synthetic bind binder) and then extend for the case binder. **)
      let qm = create_derivation g dbmap btmap fuel m in
      match inspect_ln k with
      | Tv_Abs bin body ->
        let dbmap' = extend_dbmap_binder (fun x -> incr_option (dbmap x)) in
        let qk_body = create_derivation g dbmap' (extend_btmap btmap (binder_sort bin)) fuel body in
        let qinr_branch = mk_qreturn (mk_qinr mk_qvar0) in
        mk_qbind qm (mk_qcaseprod mk_qvar0 qk_body qinr_branch)
      | _ -> fail "ExamplesIO.op_let_Bang_At_Bang continuation is not a lambda"
    end
    | _ ->
      let f = (create_derivation g dbmap btmap fuel hd) in
      let x = (create_derivation g dbmap btmap fuel a) in
      if is_lambdaprod f then mk_qappprod f x
      else if app_result_is_io g btmap hd then mk_qappprod f x
      else mk_qapp f x
  end

  | Tv_Const C_Unit -> mk_qtt
  | Tv_Const C_True -> mk_qtrue
  | Tv_Const C_False -> mk_qfalse
  | Tv_Const (C_String s) -> mk_qstringlit (pack_ln (Tv_Const (C_String s)))
  | Tv_Const (C_Int i) -> mk_qfd qfs
  | Tv_Const c -> fail ("constant " ^ (print_vconst c) ^ " not implemented")

  | Tv_Match b _ brs -> begin
    if List.length brs <> 2 then fail ("only supporting matches with 2 branches") else ();
    print ("Got: " ^ (branches_to_string brs));
    match brs with
    | [(Pat_Constant C_True, t1); (Pat_Var _ _, t2)] -> (** if **)
      let qb = create_derivation g dbmap btmap fuel b in
      let qt1 = create_derivation g dbmap btmap fuel t1 in
      let qt2 = create_derivation g (skip_dbmap_binder dbmap) (skip_btmap btmap) fuel t2 in
      if is_oprod qt1 then mk_qifprod qb qt1 qt2
      else mk_qif qb qt1 qt2

    | [(Pat_Cons fv1 _ _, t1); (Pat_Cons _ _ _, t2)] ->
      let fnm1 = fv_to_string fv1 in
      if fnm1 = "FStar.Pervasives.Inl" then
        let qb = create_derivation g dbmap btmap fuel b in
        let qt1 = create_derivation g (extend_dbmap_binder dbmap) (extend_btmap_unknown btmap) fuel t1 in
        let qt2 = create_derivation g (extend_dbmap_binder dbmap) (extend_btmap_unknown btmap) fuel t2 in
        if is_oprod qt1 then mk_qcaseprod qb qt1 qt2
        else mk_qcase qb qt1 qt2
      else fail ("only supporting matches on inl and inr for now (in this order). Got: " ^ fnm1)
    | _ -> fail ("Only boolean matches (if-then-else) are supported. Got: " ^ (branches_to_string brs))  end


  | Tv_AscribedC t c _ _ -> begin
    match inspect_comp c with
    | C_Total _ -> create_derivation g dbmap btmap fuel t
    | _ -> fail ("not a total function type")
  end

  | Tv_AscribedT e t _ _ -> create_derivation g dbmap btmap fuel e

  | Tv_UInst fv _ -> begin
    let fnm = fv_to_string fv in
    print ("        looking for uinst fvar: " ^ fnm);
    let qfs' = norm_term_env g [delta_only [fnm]; zeta] qfs in
    match inspect_ln qfs' with
    | Tv_FVar fv' ->
      if fnm = fv_to_string fv' then fail (fnm ^ " does not unfold in create_derivation!")
      else create_derivation g dbmap btmap (fuel - 1) qfs'
    | Tv_UInst fv' _ ->
      if fnm = fv_to_string fv' then fail (fnm ^ " does not unfold in create_derivation!")
      else create_derivation g dbmap btmap (fuel - 1) qfs'
    | _ -> create_derivation g dbmap btmap (fuel - 1) qfs'
  end

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

let initial_unfold_fuel : int = 32

let create_and_type_check_derivation g (dbmap:db_mapping) (qprog:term) : Tac (r:(term & term){tot_typing g (fst r) (snd r)}) =
  let (qprog, (_, qtyp)) = must <| tc_term g qprog in (** one has to dynamically retype the term to get its type **)
  let desired_qtyp = mk_tyj (typ_translation qtyp) qprog in
  let qderivation = create_derivation g dbmap empty_btmap initial_unfold_fuel qprog in
  type_check_derivation g qderivation desired_qtyp

let generate_derivation (nm:string) (qprog:term) : dsl_tac_t = fun (g, expected_t) ->
  match expected_t with
  | Some t -> fail ("expected type " ^ tag_of t ^ " not supported")
  | None -> begin
    let (qderivation, qtyp_derivation) = create_and_type_check_derivation g empty_mapping qprog in
    //dump (term_to_string qderivation ^ " : " ^ term_to_string qtyp_derivation);
    ([], mk_checked_let g (cur_module ()) nm qderivation qtyp_derivation, [])
  end
