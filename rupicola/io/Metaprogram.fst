module Metaprogram

open HelperTactics

open FStar.Tactics.Typeclasses
open FStar.Tactics.V2
open FStar.Reflection.Typing
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data

open QExp

let mk_tyj (ty t : term) : Tot term =
  let t = mk_app (`helper_oval) [(ty, Q_Implicit); (t, Q_Explicit)] in
  mk_app (`oval_quotation) [(ty, Q_Implicit); ((`QTyp.empty), Q_Explicit); (t, Q_Explicit)]

let mk_qtt : term =
  mk_app (`Qtt) [(pack_ln Tv_Unknown, Q_Implicit)]

let mk_qtrue : term =
  mk_app (`QTrue) [(pack_ln Tv_Unknown, Q_Implicit)]

let mk_qfalse : term =
  mk_app (`QFalse) [(pack_ln Tv_Unknown, Q_Implicit)]

let mk_qvar0 : term =
  mk_app (`QVar0) [
    (pack_ln Tv_Unknown, Q_Implicit);
    (pack_ln Tv_Unknown, Q_Implicit)]

let mk_qvars (t:term) : term =
  mk_app (`QVarS) [
    (pack_ln Tv_Unknown, Q_Implicit);
    (pack_ln Tv_Unknown, Q_Implicit);
    (pack_ln Tv_Unknown, Q_Implicit);
    (pack_ln Tv_Unknown, Q_Implicit);
    (t, Q_Explicit)]

let rec mk_qvarI (n:nat) : term =
  if n = 0 then mk_qvar0
  else mk_qvars (mk_qvarI (n-1))

let mk_qlambda (body:term) : term =
  mk_app (`QLambda) [
    (pack_ln Tv_Unknown, Q_Implicit);
    (pack_ln Tv_Unknown, Q_Implicit);
    (pack_ln Tv_Unknown, Q_Implicit);
    (pack_ln Tv_Unknown, Q_Implicit);
    (body, Q_Explicit)]

let mk_qapp (f arg : term) : term =
  mk_app (`QApp) [
    (pack_ln Tv_Unknown, Q_Implicit);
    (pack_ln Tv_Unknown, Q_Implicit);
    (pack_ln Tv_Unknown, Q_Implicit);
    (pack_ln Tv_Unknown, Q_Implicit);
    (pack_ln Tv_Unknown, Q_Implicit);
    (f, Q_Explicit);
    (arg, Q_Explicit)]

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

let meta_translation (nm:string) (qprog:term) (qtyp:term): dsl_tac_t = fun (g, expected_t) ->
  match expected_t with
  | Some t -> fail ("expected type " ^ tag_of t ^ " not supported")
  | None -> begin
    let qtyp_derivation = mk_tyj qtyp qprog in
    let (_, qderivation) = def_translation g empty_mapping qprog in
    match instantiate_implicits g qderivation (Some qtyp_derivation) true with
    | (Some (_, qderivation', qtyp_derivation'), _) ->
      let qderivation' = norm_term_env g [delta_only [
 //        `%QTyp.fs_oval; `%QTyp.qUnit; `%QTyp.qBool; `%QTyp.qResexn; `%QTyp.op_Hat_Subtraction_Greater; `%QTyp.op_Hat_Star; `%QTyp.op_Hat_Plus; `%QTyp.get_rel; `%QTyp.get_Type; `%Mkdtuple2?._1;`%Mkdtuple2?._2;
        `%QExp.helper_oval;
	`%QTyp.fs_oval_lambda;`%QTyp.fs_oval_return;`%QTyp.fs_oval_var0;`%QTyp.fs_oval_varS;
        `%QTyp.fs_oval_app]; zeta; iota; simplify] qderivation' in

      // type_dynamically g qtyp_derivation' qderivation';
      ([], mk_unchecked_let g (cur_module ()) nm qderivation' qtyp_derivation', [])
    | _ -> fail "could not instantiate implicits in derivation"
  end

open QTyp

%splice_t[tgt1] (meta_translation "tgt1" (`Examples.ut_unit) (`qUnit))
let _ = assert (tgt1 == test_ut_unit) by (trefl ())

%splice_t[tgt2] (meta_translation "tgt2" (`Examples.ut_true) (`qBool))
let _ = assert (tgt2 == test_ut_true) by (trefl ())

%splice_t[tgt3] (meta_translation "tgt3" (`Examples.ut_false) (`qBool))
let _ = assert (tgt3 == test_ut_false) by (trefl ())

%splice_t[tgt4] (meta_translation "tgt4" (`Examples.constant) (`(qBool ^-> qBool)))
let _ = assert (tgt4 == test_constant) by (trefl ())

%splice_t[tgt5] (meta_translation "tgt5" (`Examples.identity) (`(qBool ^-> qBool)))
let _ = assert (tgt5 == test_identity) by (trefl ())

%splice_t[tgt6] (meta_translation "tgt6" (`Examples.thunked_id) (`(qBool ^-> qBool ^-> qBool)))
let _ = assert (tgt6 == test_thunked_id) by (trefl ())

%splice_t[tgt7] (meta_translation "tgt7" (`Examples.proj1) (`(qBool ^-> qBool ^-> qBool ^-> qBool)))
let _ = assert (tgt7 == test_proj1) by (trefl ())
%splice_t[tgt8] (meta_translation "tgt8" (`Examples.proj2) (`(qBool ^-> qBool ^-> qBool ^-> qBool)))
let _ = assert (tgt8 == test_proj2) by (trefl ())
%splice_t[tgt9] (meta_translation "tgt9" (`Examples.proj3) (`(qBool ^-> qBool ^-> qBool ^-> qBool)))
let _ = assert (tgt9 == test_proj3) by (trefl ())

%splice_t[tgt10] (meta_translation "tgt10" (`Examples.apply_arg) (`((qUnit ^-> qUnit) ^-> qUnit)))
let _ = assert (tgt10 == test_apply_arg) by (trefl ())

// TODO: why is this failing?
%splice_t[tgt11] (meta_translation "tgt11" (`Examples.apply_arg2) (`((qBool ^-> qBool ^-> qBool) ^-> qBool)))
let _ = assert (tgt11 == test_apply_arg2 ()) by (trefl ())

%splice_t[tgt12] (meta_translation "tgt12" (`Examples.papply_arg2) (`((qBool ^-> qBool ^-> qBool) ^-> qBool ^-> qBool)))
let _ = assert (tgt12 == test_papply_arg2 ()) by (trefl ())
