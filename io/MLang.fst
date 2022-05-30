module MLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common


(** ** Mlang **)
(** Mlang is a language that acts as the target language. 
**)

effect MIIO (a:Type) = IIO.IIOwp a (Hist.trivial_hist)

class mlang (t:Type) = { mldummy : unit }

instance mlang_unit : mlang unit = { mldummy = () }

instance mlang_bool : mlang bool = { mldummy = () }
instance mlang_int : mlang int = { mldummy = () }
instance mlang_pair t1 t2 {| d1:mlang t1 |} {| d2:mlang t2 |} : mlang (t1 * t2) = 
  { mldummy = () }
instance mlang_either t1 t2 {| d1:mlang t1 |} {| d2:mlang t2 |} : mlang (either t1 t2) =
  { mldummy = () }
instance mlang_resexn t1 {| d1:mlang t1 |} : mlang (resexn t1) =
  { mldummy = () }

instance mlang_arrow t1 t2 {| d1:mlang t1 |} {| d2:mlang t2 |} : mlang (t1 -> MIIO (resexn t2)) =
  { mldummy = () }
