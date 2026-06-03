module RQ.Metaprogram

open RQ.Metaprogram.Utils

open FStar.Tactics.V2
open FStar.Tactics.Typeclasses
open FStar.Reflection.Typing
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data

open RQ.TypingRelation
open RQ.SigeltAttrs
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
let mk_qnat (oref:option term) : term =
  match oref with
  | None -> mk_app (`QTypes.qNat) []
  | Some ref -> mk_app (`QTypes.qNatR) [(ref, Q_Explicit)]

let mk_qstring (oref:option term) : term =
  match oref with
  | None -> mk_app (`QTypes.qString) []
  | Some ref -> mk_app (`QTypes.qStringR) [(ref, Q_Explicit)]
let mk_qresexn (t:term) : term = mk_app (`QTypes.qResexn) [(t, Q_Explicit)]
let mk_qarr (t1 t2:term) (oref:option term): term =
  match oref with
  | None -> mk_app (`QTypes.op_Hat_Subtraction_Greater) [(t1, Q_Explicit); (t2, Q_Explicit)]
  | Some ref -> mk_app (`QTypes.qArrR) [(t1, Q_Explicit); (t2, Q_Explicit); (ref, Q_Explicit)]
let mk_qarrio (t1 t2:term) (oref:option term): term =
  match oref with
  | None -> mk_app (`QTypes.op_Hat_Subtraction_Greater_Bang_At) [(t1, Q_Explicit); (t2, Q_Explicit)]
  | Some ref -> mk_app (`QTypes.qArrIOR) [(t1, Q_Explicit); (t2, Q_Explicit); (ref, Q_Explicit)]
let mk_qpair (t1 t2:term) (oref:option term): term =
  match oref with
  | None ->  mk_app (`QTypes.op_Hat_Star) [(t1, Q_Explicit); (t2, Q_Explicit)]
  | Some ref -> mk_app (`QTypes.qPairR) [(t1, Q_Explicit); (t2, Q_Explicit); (ref, Q_Explicit)]
let mk_qsum (t1 t2:term) (oref:option term): term =
  match oref with
  | None -> mk_app (`QTypes.op_Hat_Plus) [(t1, Q_Explicit); (t2, Q_Explicit)]
  | Some ref -> mk_app (`QTypes.qSumR) [(t1, Q_Explicit); (t2, Q_Explicit); (ref, Q_Explicit)]

(** Collect every refinement layer of a (possibly synonym-folded, possibly
    nested) base type into the innermost binder plus the conjunction of all
    predicates. For [(x:t{A}){B}] each layer's predicate is open over de Bruijn
    index 0 (its own bound variable); across layers they all refer to the same
    logical variable at index 0, so they can be conjoined directly without any
    shifting. Type synonyms (e.g. [int64 = x:nat{x <= 10}]) are unfolded so their
    refinements are not lost. Predicates are conjoined innermost-first
    ([inner /\ outer]) so the synthesized refinement matches the order in which
    F* builds the desired refinement VC; otherwise the resulting [P ==> Q]
    obligation is a mere permutation that [simplify] cannot collapse to [True]
    (and [prove_equality] has no SMT fallback). Returns [None] for arrows /
    unrefined base types. *)
let rec collect_ref_layers (ty:typ)
  : Tac (option (FStar.Stubs.Reflection.Types.binder & term)) =
  match inspect_ln ty with
  | Tv_Refine b ref ->
    (match collect_ref_layers (inspect_binder b).sort with
     | None -> Some (b, ref)
     | Some (inner_b, inner_pred) ->
       Some (inner_b, mk_app (`Prims.l_and) [(inner_pred, Q_Explicit); (ref, Q_Explicit)]))
  | Tv_FVar fv ->
    (** Do not unfold the primitive base types that [typ_translation] handles
        specially (e.g. [nat = x:int{x>=0}]): unfolding them would inject a
        redundant refinement (and change the base type from [nat] to [int]),
        making otherwise-identical refinements compare as arithmetic implications
        instead of matching syntactically. Only user-defined synonyms unfold. *)
    (match fv_to_string fv with
     | "Prims.unit" | "Prims.bool" | "Prims.string"
     | "Prims.nat" | "Prims.int" | "Trace.file_descr" -> None
     | _ ->
       (match try_to_unfold_fv (fv_to_string fv) ty with
        | Some ty' -> collect_ref_layers ty'
        | None -> None))
  | _ -> None

(** Build the closed refinement predicate [fun x -> conj] for a refined base
    type, unfolding synonyms and conjoining nested refinements via
    [collect_ref_layers]. The lambda is re-elaborated so it gets a residual
    computation type (otherwise the SMT encoding warns about an unannotated
    abstraction). Returns [None] when there is no refinement to attach. *)
let refinement_lam_of_ty (ty:typ) : Tac (option term) =
  match collect_ref_layers ty with
  | None -> None
  | Some (inner_b, pred) ->
    let lam = pack_ln (Tv_Abs inner_b pred) in
    let env = top_env () in
    let (tc_res, _) = tc_term env lam in
    let lam =
      match tc_res with
      | Some r -> let (lam', _) = r in lam'
      | None -> lam
    in
    Some lam

let rec typ_translation (qt:term) (oref:option term) : Tac term =
  match inspect_ln qt with
  | Tv_FVar fv -> begin
    match fv_to_string fv with
    | "Prims.unit" -> mk_qunit oref
    | "Prims.bool" -> mk_qbool oref
    | "Prims.string" -> mk_qstring oref
    | "Prims.nat" -> mk_qnat oref
    | "Trace.file_descr" -> mk_qfiledescr oref
    | "Prims.int" -> mk_qnat oref
    | nfv -> begin
      match try_to_unfold_fv nfv qt with
      | Some qt -> typ_translation qt oref
      | None -> fail ("Type " ^ nfv ^ " not supported")
    end
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
       | Some r -> mk_qarrio tbv (typ_translation r None) oref
       | None -> mk_qarr tbv (typ_translation ret None) oref)
    | _ -> fail ("not a total function type")
  end

  (** erase refinement **)
  | Tv_Refine _ _ ->
    (match collect_ref_layers qt with
     | Some (inner_b, pred) ->
       let lam = pack_ln (Tv_Abs inner_b pred) in
       (** Re-elaborate the lambda so it gets a residual computation type;
           otherwise the SMT encoding warns with "Unannotated abstraction". *)
       let env = top_env () in
       let (tc_res, _) = tc_term env lam in
       let lam =
         match tc_res with
         | Some r -> let (lam', _) = r in lam'
         | None -> lam
       in
       typ_translation (inspect_binder inner_b).sort (Some lam)
     | None -> fail "unexpected: Tv_Refine collected no refinement layers")

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

let either_branch_types_of_ty (ty:typ) : Tac (option (typ & typ)) =
  let (h, args) = collect_app ty in
  match get_fv h, args with
  | Some "FStar.Pervasives.either", [(a, _); (b, _)] -> Some (a, b)
  | Some "Trace.resexn", [(a, _)] -> Some (a, `unit)
  | _ -> None

(** Try to extract the component F* types [a] and [b] of a tuple type [a & b]. *)
let tuple_component_types_of_ty (ty:typ) : Tac (option (typ & typ)) =
  let (h, args) = collect_app ty in
  match get_fv h, args with
  | Some "FStar.Pervasives.Native.tuple2", [(a, _); (b, _)] -> Some (a, b)
  | _ -> None

(** Try to extract the qTypes for the [a] and [b] branches of [either a b]
    from [fstar_ty] (the expected F* type of [qfs]); if [fstar_ty] is [None],
    fall back to type-checking [qfs] in [g]. *)
let extract_either_branches (g:env) (fstar_ty:option typ) (qfs:term) : Tac (option (term & term)) =
  let ty_opt =
    match fstar_ty with
    | Some t -> Some t
    | None -> None
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
unfold let trivial_ref0 (#a:Type0) (_:a) : Type0 = True
let mk_qerase_ref (x:term) : term = mk_app (`QRef) [(x, Q_Explicit); (`trivial_ref0, Q_Implicit)]

(** Wrap a derivation of qType [a] in [QRef], supplying [#a] explicitly but
    leaving [#ref] as a uvar to be inferred from the expected type. Supplying
    [#a] concretely keeps [change_refinement a ref] reducible (a uvar [?a] makes
    it stuck on [get_rel ?a] for the refined [QArr]/[QArrIO]/[QNat] constructors),
    while keeping [#ref] open preserves refinement inference (e.g. [t == true]). *)
let mk_qref_typed (a x:term) : term =
  mk_app (`QRef) [(unk, Q_Implicit); (a, Q_Implicit); (x, Q_Explicit)]

(** Wrap [x] in [QRef]. When the F* type [oty] is an arrow -- possibly under one
    or more refinements, e.g. [(f:(t1 -> t2){P f})] -- supply the translated
    *unrefined* arrow qType explicitly via [mk_qref_typed] so the unifier does
    not get stuck on [change_refinement] over the refined [QArr]/[QArrIO]
    constructors. We translate [strip_refinements oty] (the arrow with its outer
    refinements removed) so [#a] is the trivial arrow that the inner value (a
    [QLambda]) actually has; the outer refinement is re-attached through
    [change_refinement]/[#ref]. Otherwise fall back to the implicit [mk_qref],
    which lets non-arrow refinements (e.g. [t == true]) be inferred from the
    expected type. *)
let rec strip_refinements (ty:typ) : typ =
  let v = inspect_ln ty in
  match v with
  | Tv_Refine b _ ->
    let s = (inspect_binder b).sort in
    strip_refinements s
  | _ -> ty

(** Wrap [x] in [QRef], supplying [#ref] explicitly (as a trailing implicit
    after the explicit premise, like [mk_qerase_ref]). Used for base-type
    refined codomains where the value already carries the target refinement
    (e.g. returning a refined argument), so the unifier would otherwise leave
    [#ref] open and [fill_trivial_refinements] would set it to [trivial_ref0]. *)
let mk_qref_refined (ref_pred x:term) : term =
  mk_app (`QRef) [(x, Q_Explicit); (ref_pred, Q_Implicit)]

let mk_qref_oty (oty:option typ) (x:term) : Tac term =
  match oty with
  | Some ty ->
    let stripped = strip_refinements ty in
    let v = inspect_ln stripped in
    (match v with
     | Tv_Arrow _ _ -> mk_qref_typed (typ_translation stripped None) x
     | _ ->
       (match refinement_lam_of_ty ty with
        | Some lam -> mk_qref_refined lam x
        | None -> mk_qref x))
  | None -> mk_qref x

let mk_qtt : term = mk_app (`Qtt) []
let mk_qfd (t:term) = mk_app (`QFd) [(t, Q_Explicit)]

let mk_qtrue : term = mk_app (`QTrue) []
let mk_qfalse : term = mk_app (`QFalse) []

let mk_qif (b:term) (t1:term) (t2:term) : term =
  mk_app (`QIf) [(mk_qerase_ref b, Q_Explicit); (t1, Q_Explicit); (t2, Q_Explicit)]

let mk_qzero : term = mk_app (`QZero) []
let mk_qsucc (n:term) : term = mk_app (`QSucc) [(n, Q_Explicit)]
let mk_qnrec (n base f : term) : term = mk_app (`QNRec) [(n, Q_Explicit); (base, Q_Explicit); (f, Q_Explicit)]

let rec mk_nat_literal (n:nat) : Tot term (decreases n) =
  if n = 0 then mk_qzero
  else mk_qsucc (mk_nat_literal (n - 1))

let mk_qstringlit (s:term) : term = mk_app (`QStringLit) [(s, Q_Explicit)]
let mk_qeq_string (v1 v2 : term) : term =
  mk_app (`QStringEq) [(mk_qerase_ref v1, Q_Explicit); (mk_qerase_ref v2, Q_Explicit)]

let mk_qmkpair (oty1:option typ) (oty2:option typ) (t1:term) (t2:term) : Tac term =
  mk_app (`QMkpair) [(mk_qref_oty oty1 t1, Q_Explicit); (mk_qref_oty oty2 t2, Q_Explicit)]
let mk_qfst (t:term) : term = mk_app (`QFst) [(mk_qerase_ref t, Q_Explicit)]
let mk_qsnd (t:term) : term = mk_app (`QSnd) [(mk_qerase_ref t, Q_Explicit)]

let mk_qinl (t:term) : term = mk_app (`QInl) [(mk_qref t, Q_Explicit)]
let mk_qinr (t:term) : term = mk_app (`QInr) [(mk_qref t, Q_Explicit)]

(** Construct [QInl #_ #a #b #_ #_ t] / [QInr ...] with [a] (the Inl branch
    qType) and [b] (the Inr branch qType) provided explicitly. This avoids
    leaving the "other-branch" qType implicit as an uninferable uvar that
    F*'s unifier cannot solve through [get_rel ?b] when the constructor's
    result is compared against a known sum type. *)
let mk_qinl_explicit (a b:term) (inner_oty:option typ) (inner:term) : Tac term =
  mk_app (`QInl) [(unk, Q_Implicit); (a, Q_Implicit); (b, Q_Implicit);
                  (mk_qref_oty inner_oty inner, Q_Explicit)]
let mk_qinr_explicit (a b:term) (inner_oty:option typ) (inner:term) : Tac term =
  mk_app (`QInr) [(unk, Q_Implicit); (a, Q_Implicit); (b, Q_Implicit);
                  (mk_qref_oty inner_oty inner, Q_Explicit)]
let mk_qcase (t:term) (x1:term) (x2:term) : term =
  mk_app (`QCase) [(mk_qerase_ref t, Q_Explicit); (x1, Q_Explicit); (x2, Q_Explicit)]

let mk_qaxiom : term = mk_app (`QAxiom) []
let mk_qweaken (t:term) : term = mk_app (`QWeaken) [(t, Q_Explicit)]
let rec mk_qvarI (n:int) : term =
  if n <= 0 then mk_qaxiom
  else match n with
  | 1 -> mk_app (`qVar1) []
  | 2 -> mk_app (`qVar2) []
  | 3 -> mk_app (`qVar3) []
  | 4 -> mk_app (`qVar4) []
  | 5 -> mk_app (`qVar5) []
  | 6 -> mk_app (`qVar6) []
  | 7 -> mk_app (`qVar7) []
  | 8 -> mk_app (`qVar8) []
  | 9 -> mk_app (`qVar9) []
  | _ -> mk_qweaken (mk_qvarI (n-1))
let mk_qlambda (oty:option typ) (body:term) : Tac term =
  mk_app (`QLambda) [(mk_qref_oty oty body, Q_Explicit)]
let mk_qapp (oty:option typ) (f arg : term) : Tac term = mk_app (`QApp) [(f, Q_Explicit); (mk_qref_oty oty arg, Q_Explicit)]

let mk_qlambdacomp (body:term) : term = mk_app (`QLambdaIO) [(body, Q_Explicit)]
let mk_qappcomp (f arg : term) : term = mk_app (`QAppIO) [(f, Q_Explicit); (mk_qref arg, Q_Explicit)]
let mk_qcall (op:term) (args:term) : term = mk_app (`QCall) [(op, Q_Explicit); (mk_qerase_ref args, Q_Explicit)] (** the operation takes non-refined arguments **)
let mk_qreturn (oty:option typ) (t:term) : Tac term = mk_app (`QReturn) [(mk_qref_oty oty t, Q_Explicit)]
let mk_qbind (e:term) (f:term) : term = mk_app (`QBind) [(e, Q_Explicit); (f, Q_Explicit)]
let mk_qifcomp (b:term) (t1:term) (t2:term) : term =
  mk_app (`QIfIO) [(mk_qerase_ref b, Q_Explicit); (t1, Q_Explicit); (t2, Q_Explicit)]
let mk_qcasecomp (t:term) (x1:term) (x2:term) : term =
  mk_app (`QCaseIO) [(mk_qerase_ref t, Q_Explicit); (x1, Q_Explicit); (x2, Q_Explicit)]
let mk_qletioex_explicit (qm qk:term) : term =
  mk_app (`qLetIOEx) [(qm, Q_Explicit); (qk, Q_Explicit)]

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

let rec create_derivation g (dbmap:db_mapping) (prior_derivs:prior_derivations) (is_comp:bool) (fstar_ty:option typ) (qfs:term) : Tac term =
  let _ = print_debug ("      in exp translation: " ^ tag_of qfs) in
  match inspect_ln qfs with
  | Tv_UInst fv _
  | Tv_FVar fv -> begin
    let fnm = fv_to_string fv in
    match List.Tot.assoc fnm prior_derivs with
    | Some cached ->
      print_debug ("        reusing prior derivation for: " ^ fnm);
      cached
    | None -> fail ("Error: Derivation of " ^ fnm ^ " not found.")
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
    let qbody = create_derivation g (extend_dbmap_binder dbmap) prior_derivs body_is_comp body_ty body in
    if body_is_comp then mk_qlambdacomp qbody
    else mk_qlambda body_ty qbody

  | Tv_App hd (a, _) -> begin
    let (head, args) = collect_app qfs in
    let explicit_args : list term =
      args |> List.Tot.filter (fun (_, q) -> Q_Explicit? q) |> List.Tot.map fst in
    match get_fv head, explicit_args with
    | Some "FStar.Pervasives.Native.Mktuple2", [v1; v2] ->
      let comp_ty = match fstar_ty with
        | Some ty -> tuple_component_types_of_ty ty
        | None -> None in
      let ty1, ty2 = match comp_ty with
        | Some (a, b) -> Some a, Some b
        | None -> None, None in
      mk_qmkpair ty1 ty2 (create_derivation g dbmap prior_derivs false ty1 v1) (create_derivation g dbmap prior_derivs false ty2 v2)
    | Some "FStar.Pervasives.Native.fst", [v1] ->
      mk_qfst (create_derivation g dbmap prior_derivs false None v1)
    | Some "FStar.Pervasives.Native.snd", [v1] ->
      mk_qsnd (create_derivation g dbmap prior_derivs false None v1)
    | Some "FStar.Pervasives.Inl", [v1] ->
      let branches_ty = match fstar_ty with
        | Some ty -> either_branch_types_of_ty ty
        | None -> None in
      let inner_ty = match branches_ty with
        | Some (a, _) -> Some a
        | None -> None in
      let inner = create_derivation g dbmap prior_derivs false inner_ty v1 in
      (match branches_ty with
       | Some (a, b) -> mk_qinl_explicit (typ_translation a None) (typ_translation b None) inner_ty inner
       | None -> mk_qinl inner)
    | Some "FStar.Pervasives.Inr", [v1] ->
      let branches_ty = match fstar_ty with
        | Some ty -> either_branch_types_of_ty ty
        | None -> None in
      let inner_ty = match branches_ty with
        | Some (_, b) -> Some b
        | None -> None in
      let inner = create_derivation g dbmap prior_derivs false inner_ty v1 in
      (match branches_ty with
       | Some (a, b) -> mk_qinr_explicit (typ_translation a None) (typ_translation b None) inner_ty inner
       | None -> mk_qinr inner)
    | Some "IOStar.io_return", [v] ->
      let v_ty = match fstar_ty with
        | Some t -> strip_io t
        | None -> None in
      mk_qreturn v_ty (create_derivation g dbmap prior_derivs false v_ty v)
    | Some "IOStar.return", [v] ->
      let v_ty = match fstar_ty with
        | Some t -> strip_io t
        | None -> None in
      mk_qreturn v_ty (create_derivation g dbmap prior_derivs false v_ty v)
    | Some "IOStar.io_call", [op; v] ->
      mk_qcall op (create_derivation g dbmap prior_derivs false None v)
    | Some "IOStar.op_let_Bang_At", [m; k]
    | Some "IOStar.io_bind", [m; k] -> begin
      let qm = create_derivation g dbmap prior_derivs true None m in
      match inspect_ln k with
      | Tv_Abs bin body ->
        (** Continuation [k : a -> io b] has the same outer io result type as the
            whole [io_bind], so propagate [fstar_ty] into the body. *)
        let qk = create_derivation g (extend_dbmap_binder dbmap) prior_derivs true fstar_ty body in
        mk_qbind qm qk
      | _ -> fail "IOStar.io_bind continuation is not a lambda"
    end
    | Some "IOStar.eq_string", [v1; v2] ->
      mk_qeq_string (create_derivation g dbmap prior_derivs false None v1) (create_derivation g dbmap prior_derivs false None v2)
    | Some "IOStar.op_let_Bang_At_Bang", [m; k] -> begin
      (** let!@! m k = match!@ m with Inl x -> k x | Inr y -> return (Inr y)
          Translates to: QBind m (QCaseIO QAxiom (k_body) (QReturn (QInr QAxiom)))
          The dbmap for k_body needs two shifts (bind + case) but only one new binder from k's lambda.
          So we shift existing mappings by 1 (for the synthetic bind binder) and then extend for the case binder. **)
      let qm = create_derivation g dbmap prior_derivs true None m in
      match inspect_ln k with
      | Tv_Abs bin body ->
        let dbmap' = extend_dbmap_binder (fun x -> incr_option (dbmap x)) in
        let qk_body = create_derivation g dbmap' prior_derivs true fstar_ty body in
        mk_qletioex_explicit qm qk_body
      | _ -> fail "IOStar.op_let_Bang_At_Bang continuation is not a lambda"
    end
    | Some "IOStar.io_nrec", [n; base; f] ->
      mk_qnrec
        (create_derivation g dbmap prior_derivs false (Some (`nat)) n)
        (create_derivation g dbmap prior_derivs false fstar_ty base)
        (create_derivation g dbmap prior_derivs false None f)
    | Some "Prims.op_Addition", [v1; v2] ->
      (match inspect_ln v2 with
       | Tv_Const (C_Int 1) ->
         (** [QSucc]'s operand rule hardcodes [qNat], so erase any refinement the
             operand might carry (e.g. a refined lambda argument [p:nat{p+1<=10}]).
             Otherwise [QSucc] pins the operand's qType -- and hence the enclosing
             [QLambda]'s domain -- to the trivial [qNat], dropping the domain
             refinement that the desired arrow type requires. *)
         mk_qsucc (mk_qerase_ref (create_derivation g dbmap prior_derivs false None v1))
       | _ -> fail "only n + 1 (successor) is supported for nat addition")
    | _ ->
      (** The head's F* type tells us the argument's expected (refined) domain.
          For a *bound variable* the metaprogram never pushes the lambda binders
          into the reflection env [g] (it tracks them via [dbmap]), so its type is
          recovered from the bound variable's own [sort]; for a *top-level* head
          it is read from the environment with [lookup_typ] (see
          [head_fstar_type]). This is essential for refined domains like
          [f:(x:t{P x} -> u)] applied as [f x] (or a top-level
          [needs_true : b:bool{b==true} -> _]): without it [arg_fstar_ty] is
          [None], the argument is wrapped with a trivial [QRef] (its [#ref]
          defaulting to [trivial_ref0], i.e. [fun _ -> True]), and [QApp]'s [#a]
          is pinned to the trivial domain -- clashing with the head's refined
          domain and leaving the remaining implicits unsolved. *)
      let hd_view = inspect_ln hd in
      let hd_ty = head_fstar_type g hd in
      let arg_fstar_ty =
        match hd_ty with
        | Some ty ->
          let stripped = strip_refinements ty in
          let sv = inspect_ln stripped in
          (match sv with
           | Tv_Arrow b _ -> Some (binder_sort b)
           | _ -> None)
        | None -> None
      in
      (** A function value that is a bound variable may have a refined-arrow
          qType in the environment (e.g. an argument [f:(t1 -> t2){P f}], whose
          qType is [qArrR _ _ P]), but [QApp]/[QAppIO] consume the trivial arrow
          [_ ^-> _]. Erase the refinement at the use site with [mk_qerase_ref]
          ([change_refinement _ (fun _ -> True)]), which is value-preserving
          ([fs_oval_ref v _] is eta-equal to [v]). This is only done for bound
          variables: their env qType is concrete so [QRef]'s [#a] is inferable,
          whereas wrapping an unfolded [QLambda] (from an fvar) would leave [#a]
          an unsolved uvar. *)
      let fun_is_bvar = (match hd_view with | Tv_BVar _ -> true | _ -> false) in
      let f0 = create_derivation g dbmap prior_derivs false None hd in
      let f = if fun_is_bvar then mk_qerase_ref f0 else f0 in
      let x = (create_derivation g dbmap prior_derivs false arg_fstar_ty a) in
      if is_comp then mk_qappcomp f x
      else mk_qapp arg_fstar_ty f x
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
      let qb = create_derivation g dbmap prior_derivs false None b in
      let qt1 = create_derivation g dbmap prior_derivs is_comp fstar_ty t1 in
      let qt2 = create_derivation g (skip_dbmap_binder dbmap) prior_derivs is_comp fstar_ty t2 in
      if is_comp then mk_qifcomp qb qt1 qt2
      else mk_qif qb qt1 qt2

    | [(Pat_Cons fv1 _ _, t1); (Pat_Cons _ _ _, t2)] ->
      let fnm1 = fv_to_string fv1 in
      if fnm1 = "FStar.Pervasives.Inl" then
        let qb = create_derivation g dbmap prior_derivs false None b in
        let qt1 = create_derivation g (extend_dbmap_binder dbmap) prior_derivs is_comp fstar_ty t1 in
        let qt2 = create_derivation g (extend_dbmap_binder dbmap) prior_derivs is_comp fstar_ty t2 in
        if is_comp then mk_qcasecomp qb qt1 qt2
        else mk_qcase qb qt1 qt2
      else fail ("only supporting matches on inl and inr for now (in this order). Got: " ^ fnm1)
    | _ -> fail ("Only boolean matches (if-then-else) are supported. Got: " ^ (branches_to_string brs))  end


  | Tv_AscribedC t c _ _ -> begin
    match inspect_comp c with
    | C_Total _ -> create_derivation g dbmap prior_derivs is_comp fstar_ty t
    | _ -> fail ("not a total function type")
  end

  | Tv_AscribedT e t _ _ -> create_derivation g dbmap prior_derivs is_comp fstar_ty e

  | _ -> fail ("not implemented in expressions: " ^ tag_of qfs)

(* Opaque wrapper that extracts the typing derivation from a packed turnstile.
   This is intentionally NOT marked `unfold` so that uses of `unwrap_deriv X`
   remain symbolic (a single fvar application) on both sides of equality checks
   in the metaprogram. Unfolding `dsnd` via nbe would expand to a match
   expression whose anonymous binder receives fresh internal UIDs at each
   occurrence, making textually-identical terms compare unequal in
   `refl_core_check_term`. *)
let unwrap_deriv (#g:typ_env) (#a:qType) (#x:fs_val a) (p:packed_turnstile_g g a x)
  : g ⊢ fs_oval_helper_g g x (dfst p)
  = dsnd p

let prove_equality (nm:string) (unfold_names:list string) : Tac unit =
  ignore (repeat forall_intro);
  norm [delta_only qType_defs_list;
        delta_only unfold_names;
        delta_qualifier ["unfold"];
//        delta_namespace ["QTypes.EvalEnv"];
        simplify; primops; iota;
        unascribe;
        simplify];
  dump ("PROVE_EQ_DUMP_BEGIN " ^ nm);
  print ("PROVE_EQ_DUMP_END " ^ nm);
  or_else
    (fun () -> or_else trivial trefl)
    (fun () -> dump "RQ's unification failed"; fail "RQ's unification failed")

(** Fill any remaining implicit (from [instantiate_implicits]) of type [X -> Type0]
    by substituting in [fun (_:X) -> Prims.l_True].
    As we substitute, we also propagate the substitution into the recorded types
    of the remaining implicits, in case an implicit's domain references an earlier
    implicit. *)
let fill_trivial_refinements (l:list (FStar.Stubs.Reflection.Types.namedv & typ)) (qderivation:term) : Tac (term * nat) =
  let rec go (l:list (FStar.Stubs.Reflection.Types.namedv & typ)) (qd:term) (left:nat) : Tac (term * nat) =
    match l with
    | [] -> (qd, left)
    | (nv, typ) :: rest ->
      match inspect_ln typ with
      | Tv_Arrow b _ ->
        let bv = inspect_binder b in
        let dom = bv.sort in
        let true_fun = mk_app (`trivial_ref0) [(dom, Q_Implicit)] in
        let sub = [FStar.Stubs.Syntax.Syntax.NT nv true_fun] in
        let qd' = subst_term sub qd in
        let rest' = map (fun (nv', t) -> (nv', subst_term sub t)) rest in
        go rest' qd' left
      | _ ->
        (** Leftover implicit is not [_ -> Type0] (typically a stray [qType]
            from a failed QInl/QInr inversion through [change_refinement]).
            Skip it so the substitution machinery does not get a derivation
            term piped into [trivial_ref0]'s [#a:Type0] slot. *)
        go rest qd (left + 1)
  in
  go l qderivation 0

let type_check_derivation (nm:string) g (qderivation:term) (desired_qtyp:term) (unfold_names:list string)  : Tac (r:(term & term){tot_typing g (fst r) (snd r)}) =
  print_debug ("DEBUG: entering type_check_derivation");
  let t0 = curms () in
  print_debug ("DEBUG: deriv = " ^ term_to_string qderivation);
  let (l, qderivation, _) = must <| instantiate_implicits g qderivation (Some desired_qtyp) false in
  let t1 = curms () in
  print ("  done instantiating implicits, " ^ string_of_int (List.length l) ^ " left, " ^ string_of_int (t1 - t0) ^ "ms");
  let t0 = t1 in
  let (qderivation, left) = fill_trivial_refinements l qderivation in
  let t1 = curms () in
  print ("  done filling refinements, " ^ string_of_int left ^ " implicits left, " ^ string_of_int (t1 - t0) ^ "ms");
  print_debug ("DEBUG: deriv' = " ^ term_to_string qderivation);
  let t0 = t1 in

  let qderivation = norm_well_typed_term g [delta_only qType_defs_list; primops; iota; simplify] qderivation in
  let t1 = curms () in
  print ("  done normalizing derivation " ^ string_of_int (t1 - t0) ^ "ms");
  let t0 = t1 in

  // print_debug ("DEBUG: deriv' = " ^ term_to_string qderivation');
  let desired_qtyp' = norm_well_typed_term g [delta_only qType_defs_list; iota] desired_qtyp in
  print_debug ("DEBUG: before core_check_term");
  set_guard_policy Goal;
  let token = must <| core_check_term g qderivation desired_qtyp' E_Total in
  let t1 = curms () in
  print ("  done core_check_term " ^ string_of_int (t1 - t0) ^ "ms");
  let t0 = t1 in

  (match ngoals () with
  | 0 -> ()
  | 1 ->  with_compat_pre_core 0 (fun () -> prove_equality nm unfold_names)
  | _ -> fail "too many goals");
  let t1 = curms () in
  print ("  done proving equality " ^ string_of_int (t1 - t0) ^ "ms");
  set_guard_policy Force;
  lem_retype_token g qderivation desired_qtyp' desired_qtyp;
  token_as_typing g qderivation E_Total desired_qtyp;
  (qderivation, desired_qtyp)

let create_and_type_check_derivation (nm:string) g (dbmap:db_mapping) (prior_derivs:prior_derivations) (qprog:term) : Tac (r:(term & term){tot_typing g (fst r) (snd r)}) =
  (** [qprog] is assumed to be a top-level definition: get its name, then look
      up its declared (refined) F* type in the environment. *)
  let prog_name = match fv_name_of_term qprog with
    | Some n -> n
    | None -> fail (term_to_string qprog ^ " is not a top-level definition") in
  let qtyp = match lookup_fstar_type g prog_name with
    | Some t -> t
    | None -> fail ("could not find the F* type of " ^ term_to_string qprog) in
  let unfold_names = [implode_qn prog_name] in
  let desired_qtyp_inner = typ_translation qtyp None in
  let desired_qtyp = mk_ptyj desired_qtyp_inner qprog in
  let qprog = norm_term_env g [delta_only unfold_names] qprog in
  let open_qderivation = mk_qref_oty (Some qtyp) (create_derivation g dbmap prior_derivs false (Some qtyp) qprog) in
  let qderivation = mk_wrap_deriv open_qderivation in
  type_check_derivation nm g qderivation desired_qtyp unfold_names

(** Lemma postulated in [RQ.SigeltAttrs.fsti]: [set_sigelt_attrs] and
    [set_sigelt_quals] only modify metadata fields that are NOT exposed by
    [inspect_sigelt] (per FStar.Stubs.Reflection.V2.Builtins: [sigelt_view]
    carries neither attrs nor qualifiers), so they preserve [sigelt_typing]
    and [sigelt_has_type], which are defined purely via [pack_sigelt] /
    [inspect_sigelt]. F*'s stdlib does not expose this axiom; we postulate
    it locally in [RQ.SigeltAttrs.fsti]. **)

(** Like [mk_checked_let] but attaches [opaque_to_smt] attribute and
    [Irreducible] qualifier, so F* skips both re-typechecking (checked=true)
    and SMT-encoding of the body. **)
let mk_checked_opaque_let
  (g:FStar.Stubs.Reflection.Types.env) (cur_module:name) (nm:string)
  (tm:term) (ty:typ{FStar.Reflection.Typing.typing g tm (E_Total, ty)})
  : sigelt_for g (Some ty) =
  let (b, se, blob) = mk_checked_let g cur_module nm tm ty in
  let attrs = [(`("opaque_to_smt"))] in
  let quals = [] in
  let se' = set_sigelt_quals quals (set_sigelt_attrs attrs se) in
  sigelt_typing_preserves g se (Some ty) attrs quals;
  (b, se', blob)

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
  mk_app (`unwrap_deriv) [
      (mk_app deriv [(unk, Q_Explicit)], Q_Explicit)] // the g_env argument will be filled in by the caller's context

let generate_derivation_using (nm:string) (qprog:term) (deps: list (string & term)) : dsl_tac_t = fun (g, expected_t) ->
  set_guard_policy Force;
  match expected_t with
  | Some t -> fail ("expected type " ^ tag_of t ^ " not supported")
  | None -> begin
    (** Build prior_derivs: map source fvar names to `deriv_fvar _`.
        Use Tv_Unknown for the typing environment (g_env : typ_env) expected
        by the prior derivations, letting F*'s typechecker infer it. **)
    let prior_derivs = deps |> map (fun (src_name, deriv) -> (src_name, use_deriv deriv)) in
    let t0 = curms () in
    print ("SPLICE_BEGIN " ^ nm);
    let (qderivation, qtyp_derivation) = create_and_type_check_derivation nm g empty_mapping prior_derivs qprog in
    let t1 = curms () in
    print ("SPLICE_END " ^ nm ^ " " ^ string_of_int (t1 - t0) ^ "ms");
    let se_for = mk_checked_opaque_let g (cur_module ()) nm qderivation qtyp_derivation in
    ([], se_for, [])
  end

let generate_derivation (nm:string) (qprog:term) : dsl_tac_t =
  generate_derivation_using nm qprog []
