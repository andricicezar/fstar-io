module Backtranslation

open STLC
open QTyp
open QExp
open LogRelSourceTarget
open LogRelTargetSource

val typing : typ_env -> exp -> qType -> Type u#1

val backtranslate (#e:value) (#t:qType) (h:typing empty e t) : fs_val t

val lem_backtranslate (#e:value) #t (h:typing empty e t)
  : Lemma (
    valid_in_val #t (backtranslate h) e /\
    (forall hist. t ∈ (hist, backtranslate h, e))
  )
