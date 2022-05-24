module TLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common


(** ** TLang **)
(** TLang is a language that acts as the target language. 
**)

effect MIIO (a:Type) = DM.IIO.IIOwp a (Hist.trivial_hist ())

class tlang (t:Type) = { mldummy : unit }

instance tlang_unit : tlang unit = { mldummy = () }

instance tlang_bool : tlang bool = { mldummy = () }
instance tlang_int : tlang int = { mldummy = () }
instance tlang_pair t1 t2 {| d1:tlang t1 |} {| d2:tlang t2 |} : tlang (t1 * t2) = 
  { mldummy = () }
instance tlang_either t1 t2 {| d1:tlang t1 |} {| d2:tlang t2 |} : tlang (either t1 t2) =
  { mldummy = () }

instance tlang_arrow t1 t2 {| d1:tlang t1 |} {| d2:tlang t2 |} : tlang (t1 -> MIIO t2) =
  { mldummy = () }
