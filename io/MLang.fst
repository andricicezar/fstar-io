module MLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open MIO

(** ** Mlang **)
(** MLang is just TLang wrapped. See more in TLang**)


class mlang_fo (t:Type) = { mldummy : unit }

effect MIIO (a:Type) = IIO.IIOwp a (Hist.trivial_hist)
class mlang_verified (t:Type) = { mldummy2 : unit }

class mlang_unverified (t:Type) = { mldummy3 : unit }

(** *** FO instances **)
instance mlang_fo_unit : mlang_fo unit = { mldummy = () }

instance mlang_fo_bool : mlang_fo bool = { mldummy = () }
instance mlang_fo_int : mlang_fo int = { mldummy = () }

instance mlang_fo_pair t1 t2 {| d1:mlang_fo t1 |} {| d2:mlang_fo t2 |} : mlang_fo (t1 * t2) = 
  { mldummy = () }
instance mlang_fo_either t1 t2 {| d1:mlang_fo t1 |} {| d2:mlang_fo t2 |} : mlang_fo (either t1 t2) =
  { mldummy = () }

instance mlang_fo_resexn t1 {| d1:mlang_fo t1 |} : mlang_fo (resexn t1) =
  { mldummy = () }

(** *** Verified instances **)

instance mlang_verified_arrow_fo t1 t2 {| d1:mlang_fo t1 |} {| d2:mlang_fo t2 |} : mlang_verified (t1 -> MIIO (resexn t2)) =
  { mldummy2 = () }

instance mlang_verified_arrow_l t1 t2 {| d1:mlang_verified t1 |} {| d2:mlang_fo t2 |} : mlang_verified (t1 -> MIIO (resexn t2)) =
  { mldummy2 = () }

instance mlang_verified_arrow_r t1 t2 {| d1:mlang_fo t1 |} {| d2:mlang_verified t2 |} : mlang_verified (t1 -> MIIO (resexn t2)) =
  { mldummy2 = () }

instance mlang_verified_arrow t1 t2 {| d1:mlang_verified t1 |} {| d2:mlang_verified t2 |} : mlang_verified (t1 -> MIIO (resexn t2)) =
  { mldummy2 = () }

instance mlang_verified_pair t1 t2 {| d1:mlang_verified t1 |} {| d2:mlang_verified t2 |} : mlang_verified (t1 * t2) = 
  { mldummy2 = () }
instance mlang_verified_either t1 t2 {| d1:mlang_verified t1 |} {| d2:mlang_verified t2 |} : mlang_verified (either t1 t2) =
  { mldummy2 = () }

instance mlang_verified_unverified t1 t2 {| d1:mlang_unverified t1 |} {| d2:either (mlang_fo t2) (mlang_verified t2) |} : mlang_verified (t1 -> MIIO (resexn t2)) = { mldummy2 = () }

instance mlang_verified_resexn t1 {| d1:mlang_verified t1 |} : mlang_verified (resexn t1) =
  { mldummy2 = () }

(** *** Unverified instances **)

instance mlang_unverified_arrow_fo t1 t2 {| d1:mlang_fo t1 |} {| d2:mlang_fo t2 |} : mlang_unverified (t1 -> MIO (resexn t2)) =
  { mldummy3 = () }

instance mlang_unverified_arrow_l t1 t2 {| d1:mlang_unverified t1 |} {| d2:mlang_fo t2 |} : mlang_unverified (t1 -> MIO (resexn t2)) =
  { mldummy3 = () }

instance mlang_unverified_arrow_r t1 t2 {| d1:mlang_fo t1 |} {| d2:mlang_unverified t2 |} : mlang_unverified (t1 -> MIO (resexn t2)) =
  { mldummy3 = () }

instance mlang_unverified_arrow t1 t2 {| d1:mlang_unverified t1 |} {| d2:mlang_unverified t2 |} : mlang_unverified (t1 -> MIO (resexn t2)) =
  { mldummy3 = () }

instance mlang_unverified_pair t1 t2 {| d1:mlang_unverified t1 |} {| d2:mlang_unverified t2 |} : mlang_unverified (t1 * t2) = 
  { mldummy3 = () }
instance mlang_unverified_either t1 t2 {| d1:mlang_unverified t1 |} {| d2:mlang_unverified t2 |} : mlang_unverified (either t1 t2) =
  { mldummy3 = () }

instance mlang_unverified_resexn t1 {| d1:mlang_unverified t1 |} : mlang_unverified (resexn t1) =
  { mldummy3 = () }
 
instance mlang_unverified_verified t1 t2 {| d1:either (mlang_fo t1) (mlang_verified t1) |} {| d2:mlang_unverified t2 |} : mlang_unverified (t1 -> MIO (resexn t2)) = { mldummy3 = () }
