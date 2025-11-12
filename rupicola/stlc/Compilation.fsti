module Compilation

open FStar.Tactics

open STLC
open QTyp
open QExp
open ExpRel

val compile #g #a (#s:fs_oexp g a) (qs:exp_quotation g s) : exp

val lem_compile_empty_closed #a (#s:fs_oexp empty a) (qs:exp_quotation empty s) : Lemma (is_closed (compile qs))

val compile_closed (#a:qType) (#s:get_Type a) (qs:exp_quotation #a empty (fun _ -> s)) : closed_exp

val compile_equiv #g (#a:qType) (#s:fs_oexp g a) (qs:exp_quotation g s)
  : Lemma (ensures (s `equiv a` (compile qs))) (decreases qs)

val compile_closed_equiv (#a:qType) (#s:get_Type a) (qs:exp_quotation #a empty (fun _ -> s))
  : Lemma (ensures (a ⦂ (s, compile_closed qs)))

val lemma_compile_closed_arrow_is_elam (#a #b:qType) (#s:get_Type (a ^-> b))
  (qs:exp_quotation #(a ^-> b) empty (fun _ -> s))
  : Lemma (ELam? (compile_closed qs))
