module BreakDown

open HelperTactics
open FStar.Tactics.V2
open FStar.Reflection.Typing
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data

assume val translate : term -> gstlc:STLC.context -> STLC.open_term gstlc

assume val dquote_stlc_typ : STLC.typ -> g:_ -> t:term{tot_typing g t (`STLC.typ)}
assume val dquote_stlc_ctx : STLC.context -> g:_ -> t:term{tot_typing g t (`STLC.context)}
assume val dquote_stlc_exp : STLC.exp -> g:_ -> t:term{tot_typing g t (`STLC.exp)}

type qtyj_typ (g:_) (gstlc:STLC.context) (e:STLC.exp) (ty:STLC.typ) =
  mk_app (`STLC.typing) [(dquote_stlc_ctx gstlc g, Q_Explicit);
                         (dquote_stlc_exp e g, Q_Explicit);
                         (dquote_stlc_typ ty g, Q_Explicit)]
  
assume val dquote_stlc_tyj : #gstlc:_ -> #e:STLC.exp -> #ty:STLC.typ -> STLC.typing gstlc e ty -> g:_ ->
    t:term{tot_typing g t (qtyj_typ g gstlc e ty)}
    
let dquote_stlc_open_term (#gstlc:STLC.context) ((| e, ty, tyj |):STLC.open_term gstlc) (g:env) =
    (| dquote_stlc_exp e g, dquote_stlc_typ ty g, dquote_stlc_tyj tyj g |)

assume val mk_rel : qfs:term -> qstlcctx:term -> qstlctyj:term -> term

let mk_rel' (qfs:term) #gstlc ((| _, _, tyj |):STLC.open_term gstlc) (g:_) : term =
  let qtyj = dquote_stlc_tyj tyj g in
  let qctx = dquote_stlc_ctx gstlc g in
  mk_rel qfs qctx qtyj

let translation_preserves_relation (qfs:term) (gstlc:_) (g:_)
  : TacP unit
    (requires True)
    (ensures (fun () -> valid g (mk_rel' qfs (translate qfs gstlc) g)))
= match inspect_ln qfs with
  | Tv_Const (C_Int c) -> begin
    let (| _, _, tyj |) = translate qfs gstlc in
    let qtyj = dquote_stlc_tyj tyj g in
    let qctx = dquote_stlc_ctx gstlc g in
    assert_dynamically g (mk_rel qfs qctx qtyj) (** wishfull thinking **)
  end
  | _ -> fail "hey!"

let meta_translation (nm:string) (qfs:term) (gstlc:STLC.context) : dsl_tac_t = fun g ->
  let stlc_tm = translate qfs gstlc in
  let (| qe, qty, qtyj |) = dquote_stlc_open_term stlc_tm g in
  translation_preserves_relation qfs gstlc g;
  let phi = mk_rel qfs (dquote_stlc_ctx gstlc g) qtyj in
  valid_wtf g phi;
  [
   mk_checked_let g nm qe (`STLC.exp);
   mk_checked_let g (nm^"_ty") qty (`STLC.typ); (** probably not needed since we know what type we want in the end **)
   (let (| e, ty, _ |) = stlc_tm in
    mk_checked_let g (nm^"_tyj") qtyj (qtyj_typ g gstlc e ty));
   mk_checked_let g (nm^"_pf")
                    (`())
                    (mk_squash phi);
  ]
