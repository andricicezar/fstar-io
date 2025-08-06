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

let reif (t:term) : option term =
  let t = U.unmeta t in
  let hd, args = U.head_and_args_full t in
  let hd = U.unmeta hd in
  match (SS.compress hd).n, args with
  | Tm_constant (Const_reify _), [(t, None)] -> Some t
  | _ -> None

(* binder is open *)
let funbody (t:term) : option (binder & term) =
  let bs, t', rc_opt = U.abs_formals t in
  match bs with
  | [] -> None
  | b::bs ->
    Some (b, U.abs bs t' rc_opt)

let tr_typ (g:uenv) (t:term) : mlty =
  let cb = FStarC.Extraction.ML.Term.term_as_mlty in
  let ohua = hua t in
  if None? ohua then
    nop ();
  let Some (fv, us, args) = ohua in
  (* if !dbg then Format.print1 "!!! checking typ %s\n" (show ohua); *)

  (* handle a ref type *)
  let h_ref (t:term) : mlty =
    (* t is probably `to_Type SNat` or similar, normalize it. *)
    let open FStarC.TypeChecker.Normalize in
    let open FStarC.TypeChecker.Env in
    let t = normalize [UnfoldUntil S.delta_constant; EraseUniverses; Iota; Zeta; ForExtraction] (tcenv_of_uenv g) t in
    MLTY_Named ([cb g t], ([], "ref"))
  in

  match fv, us, args with
  | _, _, [(t, _)] when S.fv_eq_lid fv (Ident.lid_of_str "MST.Tot.ref") ->
    h_ref t
  | _, _, [(t, _); _] when S.fv_eq_lid fv (Ident.lid_of_str "FStar.Monotonic.Heap.mref") ->
    h_ref t
  | _, _, [(t, _)] when S.fv_eq_lid fv (Ident.lid_of_str "FStar.Monotonic.Heap.core_mref") ->
    h_ref t

  | _, _, []
    when S.fv_eq_lid fv (Ident.lid_of_str "FStar.SizeT.t")
      || S.fv_eq_lid fv (Ident.lid_of_str "Prims.nat")
      || S.fv_eq_lid fv (Ident.lid_of_str "Prims.int")
    ->
    MLTY_Named ([], ([], "int"))

  | _ ->
    let bs, typ = U.arrow_formals t in
    match hua typ with
    | Some (_, _, [(t, _); _; _])
      when S.fv_eq_lid fv (Ident.lid_of_str "MST.Tot.mheap") ->
      List.fold_right (fun b mlty ->
        MLTY_Fun (cb g b.binder_bv.sort, E_IMPURE, mlty)
      ) bs (cb g t)
    | _ -> nop ()


let tr_expr (g:uenv) (t:term) : mlexpr & e_tag & mlty =
  let t = SS.compress t in
  (* if !dbg then *)
  (*   Format.print2 "!!! tr_expr (%s) (tag = %s)\n" (show t) (FStarC.Class.Tagged.tag_of t); *)
  (* Only enabled with an extension flag *)
  let cb = FStarC.Extraction.ML.Term.term_as_mlexpr in
  match reif t with
  | Some v -> cb g v
  | None ->

  let hua = hua t in
  if None? hua then (
    (* if !dbg then *)
    (*   Format.print1 "!!! no hua for expr %s\n" (show t); *)
    nop ()
  );
  let Some (fv, us, args) = hua in
  (* if !dbg then *)
  (*   Format.print2 "!!! checking expr %s ; nargs = %s\n" (show hua) (show (List.length args)); *)
  match fv, us, args with

  (* bind *)
  | _, _, [(ta, _); (tb, _); _flagv; _wpv; _flagf; _wpf; (v, None); (f, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "MST.Tot.mheap_bind") -> begin
    let v =
      match reif v with | None -> v | Some v -> v
    in
    match funbody f with | None -> nop () | Some (b, body) ->

    let body =
      match reif body with | None -> body | Some body -> body
    in

    let mlta = term_as_mlty g ta in
    let mltb = term_as_mlty g tb in
    let v, _, _ = cb g v in
    let gb, bid, _ = extend_bv g b.binder_bv ([], mlta) false false in
    let body, _, _ = cb gb body in
    let e =
      let lb : mllb = {
        mllb_name = bid;
        mllb_tysc = Some ([], mlta);
        mllb_add_unit = false;
        mllb_def = v;
        mllb_attrs = [];
        mllb_meta = [];
        print_typ = false;
      }
      in
      MLE_Let ((NonRec, [lb]), body)
    in
    let e = with_ty mlta e in
    e, E_IMPURE, mltb
  end

  | _, _, [(ta, _); _wp; (f, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "MST.Tot.lift_pure_mst") ->
    let f =
      (* unthunk f *)
      match funbody f with
      | Some (_, body) -> body
      | _ -> failwith "ExtractSST: lifted pure is not a lambda."
    in
    let f, _, _ = cb g f in
    let mlta = term_as_mlty g ta in
    f, E_IMPURE, mlta

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

  | _, _, [(x, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "MST.Tot.get_heap") ->
    ml_unit, E_PURE, ml_unit_ty
  | _, _, [(x, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "MST.Tot.witness") ->
    ml_unit, E_PURE, ml_unit_ty
  | _, _, [(x, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "MST.Tot.recall") ->
    ml_unit, E_PURE, ml_unit_ty

  (* Even with --cmi, this isn't inlined automatically? Handle
  specially (extract as no-ops). *)
  | _, _, [_t; _rel; (r, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "LabeledRefs.share") ->
    ml_unit, E_PURE, ml_unit_ty
  | _, _, [_t; _rel; (r, None)]
      when S.fv_eq_lid fv (Ident.lid_of_str "LabeledRefs.encapsulate") ->
    ml_unit, E_PURE, ml_unit_ty

  | _ -> nop ()

let _ = register_pre_translate_typ tr_typ
let _ = register_pre_translate tr_expr
