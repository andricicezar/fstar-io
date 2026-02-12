module Metaprogram

open HelperTactics

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

let meta_translation (nm:string) (qprog:term) : dsl_tac_t = fun (g, expected_t) ->
  match expected_t with
  | Some t -> fail ("expected type " ^ tag_of t ^ " not supported")
  | None -> begin
    let qderivation = mk_qtt in
    let qtyp_derivation = mk_tyj (`QTyp.qUnit) qprog in

    ([], mk_unchecked_let g (cur_module ()) nm qderivation qtyp_derivation, [])
  end

let src1 : unit = ()
%splice_t[tgt1] (meta_translation "tgt1" (`src1))

let _ =
  assert (tgt1 == Qtt)