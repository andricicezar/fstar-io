module RQ.Metaprogram

open RQ.Metaprogram.Utils

open FStar.Tactics.V2
open FStar.Tactics.Typeclasses
open FStar.Reflection.Typing
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data

open RQ.TypingRelation
open QTypes.HelperTactics

let print_debug (s:string) : Tac unit =
  if debugging () then print s
  else ()

(** Quotation of types **)

let mk_qunit (oref:option term) : term =
  match oref with
  | None -> mk_app (`QTypes.qUnit) []
  | Some ref -> mk_app (`QTypes.qUnitR) [(ref, Q_Explicit)]
let mk_qbool (oref:option term) : term =
  match oref with
  | None -> mk_app (`QTypes.qBool) []
  | Some ref -> mk_app (`QTypes.qBoolR) [(ref, Q_Explicit)]
let mk_qfiledescr (oref:option term) : term =
  match oref with
  | None -> mk_app (`QTypes.qFileDescr) []
  | Some ref -> mk_app (`QTypes.qFileDescrR) [(ref, Q_Explicit)]
let mk_qnat : term = mk_app (`QTypes.qNat) []

let mk_qstring (oref:option term) : term =
  match oref with
  | None -> mk_app (`QTypes.qString) []
  | Some ref -> mk_app (`QTypes.qStringR) [(ref, Q_Explicit)]
let mk_qresexn (t:term) : term = mk_app (`QTypes.qResexn) [(t, Q_Explicit)]
let mk_qarr (t1 t2:term) : term = mk_app (`QTypes.op_Hat_Subtraction_Greater) [(t1, Q_Explicit); (t2, Q_Explicit)]
let mk_qarrio (t1 t2:term) : term = mk_app (`QTypes.op_Hat_Subtraction_Greater_Bang_At) [(t1, Q_Explicit); (t2, Q_Explicit)]
let mk_qpair (t1 t2:term) (oref:option term): term =
  match oref with
  | None ->  mk_app (`QTypes.op_Hat_Star) [(t1, Q_Explicit); (t2, Q_Explicit)]
  | Some ref -> mk_app (`QTypes.qPairR) [(t1, Q_Explicit); (t2, Q_Explicit); (ref, Q_Explicit)]
let mk_qsum (t1 t2:term) (oref:option term): term =
  match oref with
  | None -> mk_app (`QTypes.op_Hat_Plus) [(t1, Q_Explicit); (t2, Q_Explicit)]
  | Some ref -> mk_app (`QTypes.qSumR) [(t1, Q_Explicit); (t2, Q_Explicit); (ref, Q_Explicit)]

let rec typ_translation (qt:term) (oref:option term) : Tac term =
  match inspect_ln qt with
  | Tv_FVar fv -> begin
    match fv_to_string fv with
    | "Prims.unit" -> mk_qunit oref
    | "Prims.bool" -> mk_qbool oref
    | "Prims.string" -> mk_qstring oref
    | "Prims.nat" -> mk_qnat
    | "Trace.file_descr" -> mk_qfiledescr oref
    | "Prims.int" -> mk_qnat
    | _ -> fail ("Type " ^ fv_to_string fv ^ " not supported")
  end

  | Tv_App l (r, _) -> begin
    let (head, app_args) = collect_app qt in
    match get_fv head with
    | Some fv -> begin
        match fv, app_args with
        | "FStar.Pervasives.Native.tuple2", [(v1, _); (v2, _)] ->
          mk_qpair (typ_translation v1 None) (typ_translation v2 None) oref
        | "FStar.Pervasives.either", [(v1, _); (v2, _)] ->
           mk_qsum (typ_translation v1 None) (typ_translation v2 None) oref
        | "Trace.resexn", [(v, _)] ->
           mk_qresexn (typ_translation v None)
        | fnm, _ -> fail ("Type application not supported: "^ fnm ^ " - " ^ term_to_string qt)
    end
    | _ -> fail ("Type application not supported: " ^ term_to_string qt)
  end

  | Tv_Arrow b c ->  begin
    let tbv = typ_translation (binder_sort b) None in
    match inspect_comp c with
    | C_Total ret ->
      let maybe_io =
        match inspect_ln ret with
        | Tv_App l (r, _) -> begin
          match get_fv l with
          | Some "IOStar.io" -> Some r
          | _ -> None
        end
        | _ -> None
      in
      (match maybe_io with
       | Some r -> mk_qarrio tbv (typ_translation r None)
       | None -> mk_qarr tbv (typ_translation ret None))
    | _ -> fail ("not a total function type")
  end

  (** erase refinement **)
  | Tv_Refine b ref ->
    let bv = inspect_binder b in
    let lam = pack_ln (Tv_Abs b ref) in
    (** Re-elaborate the lambda so it gets a residual computation type;
        otherwise the SMT encoding warns with "Unannotated abstraction". *)
    let env = top_env () in
    let (tc_res, _) = tc_term env lam in
    let lam =
      match tc_res with
      | Some r -> let (lam', _) = r in lam'
      | None -> lam
    in
    typ_translation bv.sort (Some lam)

  | Tv_Unknown -> fail ("an underscore was found in the term")
  | Tv_Unsupp -> fail ("unsupported by F* terms")

  | _ -> fail ("not implemented in types: " ^ tag_of qt)

(** Try to extract the qTypes for the [a] and [b] branches of [either a b]
    (or [resexn a], which unfolds to [either a unit]) from [ty]. *)
let either_branches_of_ty (ty:typ) : Tac (option (term & term)) =
  let (h, args) = collect_app ty in
  match get_fv h, args with
  | Some "FStar.Pervasives.either", [(a, _); (b, _)] ->
    Some (typ_translation a None, typ_translation b None)
  | Some "Trace.resexn", [(a, _)] ->
    Some (typ_translation a None, typ_translation (`unit) None)
  | _ -> None

(** Try to extract the qTypes for the [a] and [b] branches of [either a b]
    from [fstar_ty] (the expected F* type of [qfs]); if [fstar_ty] is [None],
    fall back to type-checking [qfs] in [g]. *)
let extract_either_branches (g:env) (fstar_ty:option typ) (qfs:term) : Tac (option (term & term)) =
  let ty_opt =
    match fstar_ty with
    | Some t -> Some t
    | None -> None
    // (match tc_term g qfs with
    //            | Some (_, (_, t)), _ -> Some t
    //            | _ -> None)
  in
  match ty_opt with
  | None -> None
  | Some ty -> either_branches_of_ty ty

(** Strip a leading [IOStar.io] application from [ty], returning the payload
    type if matched. *)
let strip_io (ty:typ) : Tac (option typ) =
  let (h, args) = collect_app ty in
  match get_fv h, args with
  | Some "IOStar.io", [(a, _)] -> Some a
  | _ -> None

(** Quotation of expressions **)
unfold let ptyping (ty:qType) (t:fs_val ty) =
  g:typ_env -> packed_turnstile_g g ty t

let mk_ptyj (ty t : term) : Tot term =
  mk_app (`ptyping) [(ty, Q_Explicit); (t, Q_Explicit)]

let mk_pack_turnstile_g (g:term) (ptyj:term) : Tot term =
  mk_app (`RQ.TypingRelation.pack_turnstile_g) [
    (g, Q_Implicit);
    (ptyj, Q_Explicit)]

let mk_wrap_deriv (typj : term) : Tot term =
  let g_binder = pack_binder ({ ppname = seal "g_env"; qual = Q_Explicit; attrs = []; sort = (`QTypes.TypEnv.typ_env) }) in
  let g_env = pack_ln (Tv_BVar (pack_bv ({ ppname = seal "g_env"; index = 0; sort = seal (`QTypes.TypEnv.typ_env) }))) in
  let packed_turnstile_g = mk_pack_turnstile_g g_env typj in
  pack_ln (Tv_Abs g_binder packed_turnstile_g)

let mk_qref (x:term) : term = mk_app (`QRef) [(x, Q_Explicit)]

let mk_qtt : term = mk_app (`Qtt) []
let mk_qfd (t:term) = mk_app (`QFd) [(t, Q_Explicit)]

let mk_qtrue : term = mk_app (`QTrue) []
let mk_qfalse : term = mk_app (`QFalse) []

let mk_qif (b:term) (t1:term) (t2:term) : term =
  mk_app (`QIf) [(mk_qref b, Q_Explicit); (t1, Q_Explicit); (t2, Q_Explicit)]

let mk_qzero : term = mk_app (`QZero) []
let mk_qsucc (n:term) : term = mk_app (`QSucc) [(n, Q_Explicit)]
let mk_qnrec (n base f : term) : term = mk_app (`QNRec) [(n, Q_Explicit); (base, Q_Explicit); (f, Q_Explicit)]

let rec mk_nat_literal (n:nat) : Tot term (decreases n) =
  if n = 0 then mk_qzero
  else mk_qsucc (mk_nat_literal (n - 1))

let mk_qstringlit (s:term) : term = mk_app (`QStringLit) [(s, Q_Explicit)]
let mk_qeq_string (v1 v2 : term) : term =
  mk_app (`QStringEq) [(v1, Q_Explicit); (v2, Q_Explicit)]

let mk_qmkpair (t1:term) (t2:term) : term =
  mk_app (`QMkpair) [(mk_qref t1, Q_Explicit); (mk_qref t2, Q_Explicit)]
let mk_qfst (t:term) : term = mk_app (`QFst) [(t, Q_Explicit)]
let mk_qsnd (t:term) : term = mk_app (`QSnd) [(t, Q_Explicit)]

let mk_qinl (t:term) : term = mk_app (`QInl) [(mk_qref t, Q_Explicit)]
let mk_qinr (t:term) : term = mk_app (`QInr) [(mk_qref t, Q_Explicit)]

(** Construct [QInl #_ #a #b #_ #_ t] / [QInr ...] with [a] (the Inl branch
    qType) and [b] (the Inr branch qType) provided explicitly. This avoids
    leaving the "other-branch" qType implicit as an uninferable uvar that
    F*'s unifier cannot solve through [get_rel ?b] when the constructor's
    result is compared against a known sum type. *)
let mk_qinl_explicit (a b inner:term) : term =
  let unk = pack_ln Tv_Unknown in
  mk_app (`QInl) [(unk, Q_Implicit); (a, Q_Implicit); (b, Q_Implicit);
                  (unk, Q_Implicit); (unk, Q_Implicit); (mk_qref inner, Q_Explicit)]
let mk_qinr_explicit (a b inner:term) : term =
  let unk = pack_ln Tv_Unknown in
  mk_app (`QInr) [(unk, Q_Implicit); (a, Q_Implicit); (b, Q_Implicit);
                  (unk, Q_Implicit); (unk, Q_Implicit); (mk_qref inner, Q_Explicit)]
let mk_qcase (t:term) (x1:term) (x2:term) : term =
  mk_app (`QCase) [(t, Q_Explicit); (x1, Q_Explicit); (x2, Q_Explicit)]

let mk_qaxiom : term = mk_app (`QAxiom) []
let mk_qweaken (t:term) : term = mk_app (`QWeaken) [(t, Q_Explicit)]
let rec mk_qvarI (n:int) : term =
  if n <= 0 then mk_qaxiom
  else mk_qweaken (mk_qvarI (n-1))
let mk_qlambda (body:term) : term = mk_app (`QLambda) [(mk_qref body, Q_Explicit)]
let mk_qapp (f arg : term) : term = mk_app (`QApp) [(f, Q_Explicit); (mk_qref arg, Q_Explicit)]

let mk_qlambdacomp (body:term) : term = mk_app (`QLambdaIO) [(body, Q_Explicit)]
let mk_qappcomp (f arg : term) : term = mk_app (`QAppIO) [(f, Q_Explicit); (arg, Q_Explicit)]
let mk_qcall (op:term) (args:term) : term = mk_app (`QCall) [(op, Q_Explicit); (args, Q_Explicit)]
let mk_qreturn (t:term) : term = mk_app (`QReturn) [(mk_qref t, Q_Explicit)]
let mk_qbind (e:term) (f:term) : term = mk_app (`QBind) [(e, Q_Explicit); (f, Q_Explicit)]
let mk_qifcomp (b:term) (t1:term) (t2:term) : term =
  mk_app (`QIfIO) [(b, Q_Explicit); (t1, Q_Explicit); (t2, Q_Explicit)]
let mk_qcasecomp (t:term) (x1:term) (x2:term) : term =
  mk_app (`QCaseIO) [(t, Q_Explicit); (x1, Q_Explicit); (x2, Q_Explicit)]

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

(** Check if a type is IOStar.io _ **)
let is_io_type (ty:term) : Tot bool =
  match inspect_ln ty with
  | Tv_App l _ ->
    (match get_fv l with
     | Some "IOStar.io" -> true
     | _ -> false)
  | _ -> false

(** Cache of already-generated derivations: maps source fvar name to term to emit at cache hit.
    Each term should be of the form `deriv_name g_env_term`, i.e. the derivation fvar applied to g_env. **)
type prior_derivations = list (string & term)

let rec create_derivation g (dbmap:db_mapping) (prior_derivs:prior_derivations) (fuel:int) (is_comp:bool) (fstar_ty:option typ) (qfs:term) : Tac term =
  if fuel <= 0 then
    fail ("Unfolding depth exceeded while processing: " ^ tag_of qfs ^ " — " ^ term_to_string qfs
          ^ "\nThis likely means an unsupported primitive (e.g., op_Equality, op_Hat) was encountered.")
  else
  let _ = print_debug ("      in exp translation: " ^ tag_of qfs) in
  match inspect_ln qfs with
  | Tv_FVar fv -> begin
    let fnm = fv_to_string fv in
    match List.Tot.assoc fnm prior_derivs with
    | Some cached ->
      print_debug ("        reusing prior derivation for: " ^ fnm);
      cached
    | None -> begin
      print_debug ("        looking for fvar: " ^ fnm);
      let fstar_ty = match fstar_ty with
        | Some _ -> fstar_ty
        | None -> match tc_term g qfs with
          | Some (_, (_, ty)), _ -> Some ty
          | _ -> None
      in
      let qfs' = norm_term_env g [delta_only [fnm]; zeta] qfs in
      match inspect_ln qfs' with
      | Tv_FVar fv' ->
        if fnm = fv_to_string fv' then fail (fnm ^ " does not unfold in create_derivation!")
        else create_derivation g dbmap prior_derivs (fuel - 1) is_comp fstar_ty qfs'
      | _ -> create_derivation g dbmap prior_derivs (fuel - 1) is_comp fstar_ty qfs'
    end
  end

  | Tv_BVar v -> begin
    let i = (inspect_bv v).index in
    match dbmap i with
    | Some i' -> mk_qvarI i'
    | None -> fail (print_nat i ^ " not defined")
  end

  | Tv_Abs bin body ->
    let (body_is_comp, body_ty) =
      match fstar_ty with
      | Some ty ->
        (match inspect_ln ty with
         | Tv_Arrow _ c ->
           (match inspect_comp c with
            | C_Total ret -> (is_io_type ret, Some ret)
            | _ -> (false, None))
         | _ -> (false, None))
      | None -> (false, None)
    in
    let qbody = create_derivation g (extend_dbmap_binder dbmap) prior_derivs fuel body_is_comp body_ty body in
    if body_is_comp then mk_qlambdacomp qbody
    else mk_qlambda qbody

  | Tv_App hd (a, _) -> begin
    let (head, args) = collect_app qfs in
    let explicit_args : list term =
      args |> List.Tot.filter (fun (_, q) -> Q_Explicit? q) |> List.Tot.map fst in
    match get_fv head, explicit_args with
    | Some "FStar.Pervasives.Native.Mktuple2", [v1; v2] ->
      mk_qmkpair (create_derivation g dbmap prior_derivs fuel false None v1) (create_derivation g dbmap prior_derivs fuel false None v2)
    | Some "FStar.Pervasives.Native.fst", [v1] ->
      mk_qfst (create_derivation g dbmap prior_derivs fuel false None v1)
    | Some "FStar.Pervasives.Native.snd", [v1] ->
      mk_qsnd (create_derivation g dbmap prior_derivs fuel false None v1)
    | Some "FStar.Pervasives.Inl", [v1] ->
      let inner = create_derivation g dbmap prior_derivs fuel false None v1 in
      (match extract_either_branches g fstar_ty qfs with
       | Some (qa, qb) -> mk_qinl_explicit qa qb inner
       | None -> mk_qinl inner)
    | Some "FStar.Pervasives.Inr", [v1] ->
      let inner = create_derivation g dbmap prior_derivs fuel false None v1 in
      (match extract_either_branches g fstar_ty qfs with
       | Some (qa, qb) -> mk_qinr_explicit qa qb inner
       | None -> mk_qinr inner)
    | Some "IOStar.io_return", [v] ->
      let v_ty = match fstar_ty with
        | Some t -> strip_io t
        | None -> None in
      mk_qreturn (create_derivation g dbmap prior_derivs fuel false v_ty v)
    | Some "IOStar.return", [v] ->
      let v_ty = match fstar_ty with
        | Some t -> strip_io t
        | None -> None in
      mk_qreturn (create_derivation g dbmap prior_derivs fuel false v_ty v)
    | Some "IOStar.io_call", [op; v] ->
      mk_qcall op (create_derivation g dbmap prior_derivs fuel false None v)
    | Some "IOStar.op_let_Bang_At", [m; k]
    | Some "IOStar.io_bind", [m; k] -> begin
      let qm = create_derivation g dbmap prior_derivs fuel true None m in
      match inspect_ln k with
      | Tv_Abs bin body ->
        (** Continuation [k : a -> io b] has the same outer io result type as the
            whole [io_bind], so propagate [fstar_ty] into the body. *)
        let qk = create_derivation g (extend_dbmap_binder dbmap) prior_derivs fuel true fstar_ty body in
        mk_qbind qm qk
      | _ -> fail "IOStar.io_bind continuation is not a lambda"
    end
    | Some "ExamplesIO.eq_string", [v1; v2] -> // TODO: Move eq_string in IOStar.fst.
      mk_qeq_string (create_derivation g dbmap prior_derivs fuel false None v1) (create_derivation g dbmap prior_derivs fuel false None v2)
    | Some "IOStar.op_let_Bang_At_Bang", [m; k] -> begin
      (** let!@! m k = match!@ m with Inl x -> k x | Inr y -> return (Inr y)
          Translates to: QBind m (QCaseIO QAxiom (k_body) (QReturn (QInr QAxiom)))
          The dbmap for k_body needs two shifts (bind + case) but only one new binder from k's lambda.
          So we shift existing mappings by 1 (for the synthetic bind binder) and then extend for the case binder. **)
      let qm = create_derivation g dbmap prior_derivs fuel true None m in
      match inspect_ln k with
      | Tv_Abs bin body ->
        let dbmap' = extend_dbmap_binder (fun x -> incr_option (dbmap x)) in
        let qk_body = create_derivation g dbmap' prior_derivs fuel true None body in
        let qinr_node =
          let branches =
            match fstar_ty with
            | Some t -> (match strip_io t with
                         | Some payload -> either_branches_of_ty payload
                         | None -> None)
            | None -> None
          in
          match branches with
          | Some (qa, qb) -> mk_qinr_explicit qa qb mk_qaxiom
          | None -> mk_qinr mk_qaxiom
        in
        let qinr_branch = mk_app (`QReturn) [(qinr_node, Q_Explicit)] in
        mk_qbind qm (mk_qcasecomp mk_qaxiom qk_body qinr_branch)
      | _ -> fail "IOStar.op_let_Bang_At_Bang continuation is not a lambda"
    end
    | Some "QTypes.OpenValComp.fs_nrec_val", [n; base; f]
    | Some "IOStar.io_nrec", [n; base; f] ->
      mk_qnrec
        (create_derivation g dbmap prior_derivs fuel false (Some (`nat)) n)
        (create_derivation g dbmap prior_derivs fuel false fstar_ty base)
        (create_derivation g dbmap prior_derivs fuel false None f)
    | Some "Prims.op_Addition", [v1; v2] ->
      (match inspect_ln v2 with
       | Tv_Const (C_Int 1) ->
         mk_qsucc (create_derivation g dbmap prior_derivs fuel false fstar_ty v1)
       | _ -> fail "only n + 1 (successor) is supported for nat addition")
    | _ ->
      let arg_fstar_ty =
        match tc_term g hd with
        | Some (_, (_, ty)), _ ->
          (match inspect_ln ty with
           | Tv_Arrow b _ -> Some (binder_sort b)
           | _ -> None)
        | _ -> None
      in
      let f = (create_derivation g dbmap prior_derivs fuel false None hd) in
      let x = (create_derivation g dbmap prior_derivs fuel false arg_fstar_ty a) in
      if is_comp then mk_qappcomp f x
      else mk_qapp f x
  end

  | Tv_Const C_Unit -> mk_qtt
  | Tv_Const C_True -> mk_qtrue
  | Tv_Const C_False -> mk_qfalse
  | Tv_Const (C_String s) -> mk_qstringlit (pack_ln (Tv_Const (C_String s)))
  | Tv_Const (C_Int i) ->
      if i >= 0 then mk_nat_literal i
      else fail ("negative integer not supported as nat")
  | Tv_Const c -> fail ("constant " ^ (print_vconst c) ^ " not implemented")

  | Tv_Match b _ brs -> begin
    if List.length brs <> 2 then fail ("only supporting matches with 2 branches") else ();
    // print_debug ("Got: " ^ (branches_to_string brs));
    match brs with
    | [(Pat_Constant C_True, t1); (Pat_Var _ _, t2)] -> (** if **)
      let qb = create_derivation g dbmap prior_derivs fuel false None b in
      let qt1 = create_derivation g dbmap prior_derivs fuel is_comp fstar_ty t1 in
      let qt2 = create_derivation g (skip_dbmap_binder dbmap) prior_derivs fuel is_comp fstar_ty t2 in
      if is_comp then mk_qifcomp qb qt1 qt2
      else mk_qif qb qt1 qt2

    | [(Pat_Cons fv1 _ _, t1); (Pat_Cons _ _ _, t2)] ->
      let fnm1 = fv_to_string fv1 in
      if fnm1 = "FStar.Pervasives.Inl" then
        let qb = create_derivation g dbmap prior_derivs fuel false None b in
        let qt1 = create_derivation g (extend_dbmap_binder dbmap) prior_derivs fuel is_comp fstar_ty t1 in
        let qt2 = create_derivation g (extend_dbmap_binder dbmap) prior_derivs fuel is_comp fstar_ty t2 in
        if is_comp then mk_qcasecomp qb qt1 qt2
        else mk_qcase qb qt1 qt2
      else fail ("only supporting matches on inl and inr for now (in this order). Got: " ^ fnm1)
    | _ -> fail ("Only boolean matches (if-then-else) are supported. Got: " ^ (branches_to_string brs))  end


  | Tv_AscribedC t c _ _ -> begin
    match inspect_comp c with
    | C_Total _ -> create_derivation g dbmap prior_derivs fuel is_comp fstar_ty t
    | _ -> fail ("not a total function type")
  end

  | Tv_AscribedT e t _ _ -> create_derivation g dbmap prior_derivs fuel is_comp fstar_ty e

  | Tv_UInst fv _ -> begin
    let fnm = fv_to_string fv in
    match List.Tot.assoc fnm prior_derivs with
    | Some cached ->
      print_debug ("        reusing prior derivation for: " ^ fnm);
      cached
    | None -> begin
      print_debug ("        looking for uinst fvar: " ^ fnm);
      let fstar_ty = match fstar_ty with
        | Some _ -> fstar_ty
        | None -> match tc_term g qfs with
          | Some (_, (_, ty)), _ -> Some ty
          | _ -> None
      in
      let qfs' = norm_term_env g [delta_only [fnm]; zeta] qfs in
      match inspect_ln qfs' with
      | Tv_FVar fv' ->
        if fnm = fv_to_string fv' then fail (fnm ^ " does not unfold in create_derivation!")
        else create_derivation g dbmap prior_derivs (fuel - 1) is_comp fstar_ty qfs'
      | Tv_UInst fv' _ ->
        if fnm = fv_to_string fv' then fail (fnm ^ " does not unfold in create_derivation!")
        else create_derivation g dbmap prior_derivs (fuel - 1) is_comp fstar_ty qfs'
      | _ -> create_derivation g dbmap prior_derivs (fuel - 1) is_comp fstar_ty qfs'
    end
  end

  | _ -> fail ("not implemented in expressions: " ^ tag_of qfs)

let prove_equality (nm:string) (unfold_names:list string) : Tac unit =
  ignore (repeat forall_intro);
  norm [delta_only qType_defs_list;
        delta_only unfold_names;
        delta_qualifier ["unfold"];
        simplify; primops; iota;
        unascribe;
        simplify];
  (**
  norm [
    delta_namespace ["QTypes"; "QTypes.TypEnv"; "QTypes.EvalEnv";"QTypes.OpenValComp";"FStar.FunctionalExtensionality"];
    delta_only [`%LambdaIO.var;`%Some?.v;`%Mkdtuple2?._1; `%Mkdtuple2?._2];
    simplify; primops;
    delta_only [`%LambdaIO.var;`%Some?.v;`%Mkdtuple2?._1; `%Mkdtuple2?._2];
    primops; iota;
    simplify];
  ignore (repeat split);**)
  dump ("PROVE_EQ_DUMP_BEGIN " ^ nm);
  print ("PROVE_EQ_DUMP_END " ^ nm);
  or_else
    (fun () -> or_else trivial trefl)
    (fun () -> dump "RQ's unification failed"; fail "unification failed")


unfold let trivial_ref0 (#a:Type0) (_:a) : Type0 = True

(** Fill any remaining implicit (from [instantiate_implicits]) of type [X -> Type0]
    by substituting in [fun (_:X) -> Prims.l_True].
    As we substitute, we also propagate the substitution into the recorded types
    of the remaining implicits, in case an implicit's domain references an earlier
    implicit. *)
let fill_trivial_refinements (l:list (FStar.Stubs.Reflection.Types.namedv & typ)) (qderivation:term) : Tac term =
  let rec go (l:list (FStar.Stubs.Reflection.Types.namedv & typ)) (qd:term) : Tac term =
    match l with
    | [] -> qd
    | (nv, typ) :: rest ->
      match inspect_ln typ with
      | Tv_Arrow b _ ->
        let bv = inspect_binder b in
        let dom = bv.sort in
        let true_fun = mk_app (`trivial_ref0) [(dom, Q_Implicit)] in
        let sub = [FStar.Stubs.Syntax.Syntax.NT nv true_fun] in
        let qd' = subst_term sub qd in
        let rest' = map (fun (nv', t) -> (nv', subst_term sub t)) rest in
        go rest' qd'
      | _ ->
        (** Leftover implicit is not [_ -> Type0] (typically a stray [qType]
            from a failed QInl/QInr inversion through [change_refinement]).
            Skip it so the substitution machinery does not get a derivation
            term piped into [trivial_ref0]'s [#a:Type0] slot. *)
        go rest qd
  in
  go l qderivation

let type_check_derivation (nm:string) g (qderivation:term) (desired_qtyp:term) (unfold_names:list string)  : Tac (r:(term & term){tot_typing g (fst r) (snd r)}) =
  set_guard_policy Goal;
  print_debug ("DEBUG: entering type_check_derivation");
  let (l, qderivation, _) = must <| instantiate_implicits g qderivation (Some desired_qtyp) false in
  print_debug ("DEBUG: done instantiating implicits");
  // print_debug ("DEBUG: deriv = " ^ term_to_string qderivation);
  let qderivation = fill_trivial_refinements l qderivation in
  print_debug ("DEBUG: done filling refinements");

  let qderivation = norm_well_typed_term g [delta_only qType_defs_list; primops; iota; simplify] qderivation in
  print_debug ("DEBUG: done normalizing derivation");

  // print_debug ("DEBUG: deriv' = " ^ term_to_string qderivation');
  let desired_qtyp' = norm_well_typed_term g [delta_only qType_defs_list; iota] desired_qtyp in
  print_debug ("DEBUG: before core_check_term");
  let token = must <| core_check_term g qderivation desired_qtyp' E_Total in
  print_debug ("DEBUG: core_checm_term successfull, "^ string_of_int (ngoals ()) ^" goals to prove");

  (match ngoals () with
  | 0 -> ()
  | 1 ->  with_compat_pre_core 0 (fun () -> prove_equality nm unfold_names)
  | _ -> fail "too many goals");
  print_debug ("DEBUG: proved equality!");
  set_guard_policy Force;
  lem_retype_token g qderivation desired_qtyp' desired_qtyp;
  token_as_typing g qderivation E_Total desired_qtyp;
  (qderivation, desired_qtyp)

let initial_unfold_fuel : int = 32

let create_and_type_check_derivation (nm:string) g (dbmap:db_mapping) (prior_derivs:prior_derivations) (qprog:term) : Tac (r:(term & term){tot_typing g (fst r) (snd r)}) =
  let (qprog, (_, qtyp)) = must <| tc_term g qprog in (** one has to dynamically retype the term to get its type **)
  let unfold_names = match get_fv qprog with
    | Some nm -> [nm]
    | None -> []
  in
  let desired_qtyp = mk_ptyj (typ_translation qtyp None) qprog in
  let open_qderivation = mk_qref (create_derivation g dbmap prior_derivs initial_unfold_fuel false (Some qtyp) qprog) in
  let qderivation = mk_wrap_deriv open_qderivation in
  type_check_derivation nm g qderivation desired_qtyp unfold_names

let generate_derivation (nm:string) (qprog:term) : dsl_tac_t = fun (g, expected_t) ->
  set_guard_policy Force;
  match expected_t with
  | Some t -> fail ("expected type " ^ tag_of t ^ " not supported")
  | None -> begin
    let t0 = curms () in
    print ("SPLICE_BEGIN " ^ nm ^ " " ^ string_of_int t0);
    let (qderivation, qtyp_derivation) = create_and_type_check_derivation nm g empty_mapping [] qprog in
    let t1 = curms () in
    print ("SPLICE_END " ^ nm ^ " " ^ string_of_int t1 ^ " ELAPSED_MS " ^ string_of_int (t1 - t0));
    ([], mk_checked_let g (cur_module ()) nm qderivation qtyp_derivation, [])
  end

(** Generate a derivation for a program, reusing already-generated derivations.
    `deps` is a list of (source_program, derivation) pairs where:
    - source_program is a quoted fvar of the original F* function (e.g. `validate)
    - derivation is a quoted fvar of its already-generated derivation (e.g. `validate_derivation)

    When the metaprogram encounters a reference to a source program that has a
    matching entry in `deps`, it emits `derivation g_env` instead of expanding
    the program inline.

    Usage:
      %splice_t[validate_d] (generate_derivation "validate_d" (`validate))
      %splice_t[read_file_d] (generate_derivation "read_file_d" (`read_file))
      %splice_t[wrapper_d] (generate_derivation_using "wrapper_d" (`wrapper) [
        ("RunningExample.validate", `validate_d);
        ("RunningExample.read_file", `read_file_d)
      ])
**)
let use_deriv (deriv:term) : term =
  mk_app (`dsnd) [
      (mk_app deriv [(pack_ln Tv_Unknown, Q_Explicit)], Q_Explicit)] // the g_env argument will be filled in by the caller's context

let generate_derivation_using (nm:string) (qprog:term) (deps: list (string & term)) : dsl_tac_t = fun (g, expected_t) ->
  match expected_t with
  | Some t -> fail ("expected type " ^ tag_of t ^ " not supported")
  | None -> begin
    (** Build prior_derivs: map source fvar names to `deriv_fvar _`.
        Use Tv_Unknown for the typing environment (g_env : typ_env) expected
        by the prior derivations, letting F*'s typechecker infer it. **)
    let prior_derivs = deps |> map (fun (src_name, deriv) -> (src_name, use_deriv deriv)) in
    let t0 = curms () in
    print ("SPLICE_BEGIN " ^ nm ^ " " ^ string_of_int t0);
    let (qderivation, qtyp_derivation) = create_and_type_check_derivation nm g empty_mapping prior_derivs qprog in
    let t1 = curms () in
    print ("SPLICE_END " ^ nm ^ " " ^ string_of_int t1 ^ " ELAPSED_MS " ^ string_of_int (t1 - t0));
    ([], mk_checked_let g (cur_module ()) nm qderivation qtyp_derivation, [])
  end