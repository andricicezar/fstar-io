module Compilation

open FStar.Tactics

open STLC
open QTyp
open QExp
open LogRelSourceTarget
open LogRelTargetSource

val compile #g #a (#s:fs_oval g a) (qs:g ⊢ s) : exp

val lem_compile_equiv #g (#a:qType) (#s:fs_oval g a) (qs:g ⊢ s)
  : Lemma (ensures (s ≈ (compile qs))) (decreases qs)

val lem_compile_closed_arrow_is_elam (#a #b:qType) (#s:fs_val (a ^->!@ b)) (qs: (a ^->!@ b) ⊩ s)
  : Lemma (ELam? (compile qs))

val lem_compile_closed_valid (#a:qType) (#s:fs_val a) (qs:a ⊩ s)
  : Lemma (ensures (
    is_closed (compile qs) /\
    is_value (compile qs) /\
    valid_in_val s (compile qs) /\
    (forall hist. a ∈ (hist, s, compile qs))
    ))
