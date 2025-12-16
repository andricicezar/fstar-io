module Compilation

open FStar.Tactics

open STLC
open QTyp
open QExp
open ExpRel

val compile #g #a (#s:fs_oval g a) (qs:g ⊢ s) : exp

val lem_compile_empty_closed #a (#s:fs_oval empty a) (qs:empty ⊢ s) : Lemma (is_closed (compile qs))

val compile_closed (#a:qType) (#s:get_Type a) (qs:a ⊩ s) : closed_exp
val compile_equiv #g (#a:qType) (#s:fs_oval g a) (qs:g ⊢ s)
  : Lemma (ensures (s ≈ (compile qs))) (decreases qs)

val compile_closed_equiv (#a:qType) (#s:get_Type a) (qs:a ⊩ s)
  : Lemma (ensures (forall h. a ⦂ (h, s, compile_closed qs)))

val lemma_compile_closed_arrow_is_elam (#a #b:qType) (#s:fs_val (a ^->!@ b)) (qs: (a ^->!@ b) ⊩ s)
  : Lemma (ELam? (compile_closed qs))
