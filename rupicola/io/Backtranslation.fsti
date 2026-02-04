module Backtranslation

open STLC
open QTyp
open QExp
open ExpRel

val typing : typ_env -> exp -> qType -> Type u#1

val backtranslate (#g:typ_env) (#e:value) (#t:qType) (h:typing g e t) : fs_oval g t

val lem_backtranslate #g (#e:value{fv_in_env g e}) #t (h:typing g e t) : Lemma
(backtranslate h ≈ e)
