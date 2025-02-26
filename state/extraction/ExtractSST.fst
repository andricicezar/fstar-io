module ExtractSST

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Util
open FStarC.Extraction
open FStarC.Extraction.ML
open FStarC.Extraction.ML.Syntax
open FStarC.Const
open FStarC.BaseTypes

module BU = FStarC.Util

open FStarC.Class.Show

open FStarC.Syntax.Syntax
open FStarC.Extraction.ML.UEnv
open FStarC.Extraction.ML.Term

module SS = FStarC.Syntax.Subst
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module Ident = FStarC.Ident
open FStarC.Syntax.Print {}

let dbg = Debug.get_toggle "extraction"

let nop () = raise NotSupportedByExtension

let hua (t:term) : option (S.fv & list S.universe & S.args) =
  let t = U.unmeta t in
  let hd, args = U.head_and_args_full t in
  let hd = U.unmeta hd in
  match (SS.compress hd).n with
  | Tm_fvar fv -> Some (fv, [], args)
  | Tm_uinst ({ n = Tm_fvar fv }, us) -> Some (fv, us, args)
  | _ -> None

let tr_typ (g:uenv) (t:term) : mlty =
  let cb = FStarC.Extraction.ML.Term.term_as_mlty in
  let hua = hua t in
  if None? hua then
    nop ();
  let Some (fv, us, args) = hua in
  if !dbg then BU.print1 "GGG checking typ %s\n" (show hua);
  match fv, us, args with
  | _, _, [(t, _)] when S.fv_eq_lid fv (Ident.lid_of_str "MST.Tot.ref") ->
    MLTY_Named ([cb g t], ([], "ref"))
  | _, _, [(t, _); _] when S.fv_eq_lid fv (Ident.lid_of_str "FStar.Monotonic.Heap.mref") ->
    MLTY_Named ([cb g t], ([], "ref"))

  | _, _, [(t, _); _; _] when S.fv_eq_lid fv (Ident.lid_of_str "MST.Tot.mheap") ->
    cb g t

  | _, _, []
    when S.fv_eq_lid fv (Ident.lid_of_str "FStar.SizeT.t")
      || S.fv_eq_lid fv (Ident.lid_of_str "Prims.nat")
      || S.fv_eq_lid fv (Ident.lid_of_str "Prims.int")
    ->
    MLTY_Named ([], ([], "int"))

  | _ -> nop ()

let tr_expr (g:uenv) (t:term) : mlexpr & e_tag & mlty =
  (* Only enabled with an extension flag *)
  let cb = FStarC.Extraction.ML.Term.term_as_mlexpr in
  let hua = hua t in
  if None? hua then
    nop ();
  let Some (fv, us, args) = hua in
  if !dbg then BU.print2 "GGG checking expr %s; nargs = %s\n" (show hua) (show (List.length args));
  match fv, us, args with

  (* bind *)
  | _, _, [(ta, _); (tb, _); _flagv; _wpv; _flagf; _wpf; (v, None); (f, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "MST.Tot.mheap_bind") ->
    let v, _, _ = cb g v in
    let f, _, _ = cb g f in
    let mlta = term_as_mlty g ta in
    let mltb = term_as_mlty g tb in
    let e =
      match f.expr with
      | MLE_Fun ([b], body) ->
        let lb : mllb = {
          mllb_name = b.mlbinder_name;
          mllb_tysc = Some ([], mlta);
          mllb_add_unit = false;
          mllb_def = v;
          mllb_attrs = [];
          mllb_meta = [];
          print_typ = false;
        }
        in
        MLE_Let ((NonRec, [lb]), body)

      | _ -> MLE_App (f, [v])
    in
    let e = with_ty mlta e in
    BU.print1 "GG e = %s\n" (show e);
    e, E_IMPURE, mltb

  | _, _, [(ta, _); _wp; (f, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "MST.Tot.lift_pure_mst") ->
    let f, _, _ = cb g f in
    let mlta = term_as_mlty g ta in
    let e =
      (* unthunk f *)
      match f.expr with
      | MLE_Fun ([b], body) -> body
      | _ -> with_ty mlta <| MLE_App (f, [ml_unit])
    in
    e, E_IMPURE, mlta

  | _, _, [(t, _); _rel; (v0, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "MST.Tot.alloc") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "ref" in
    let e = with_ty mlty <| MLE_App (bang, [(cb g v0)._1]) in
    e, E_IMPURE, mlty

  | _, _, [(t, _); _rel; (v0, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "MST.Tot.read") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "!" in
    let e = with_ty mlty <| MLE_App (bang, [(cb g v0)._1]) in
    e, E_IMPURE, mlty

  | _, _, [(t, _); _rel; (r, None); (x, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "MST.Tot.write") ->
    let mlty = term_as_mlty g t in
    let bang = with_ty ml_unit_ty <| MLE_Var "(:=)" in
    let e = with_ty mlty <| MLE_App (bang, [(cb g r)._1; (cb g x)._1]) in
    e, E_IMPURE, mlty

  (* Can we avoid this? Would be nice to have all primitives
  in a single module. *)
  | _, _, [_t; _rel; (r, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "SharedRefs.share") ->
    cb g r

  | _ -> nop ()

let _ = register_pre_translate_typ tr_typ
let _ = register_pre_translate tr_expr
