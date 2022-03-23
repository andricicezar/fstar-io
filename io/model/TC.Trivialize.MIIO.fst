module TC.Trivialize.MIIO

open FStar.Tactics
open FStar.Tactics.Typeclasses

open DM.MIIO
include TC.Trivialize

(** since `MIIO a` is a synonym of `IIOwp a (fun h p -> forall r lt. p r lt)`,
it is considered trivial. And since MIIO has no pre-condition, we can not
define any instance for trivializeable **)
instance trivial_MIIO t1 t2 : trivial (t1 -> MIIO t2) = { mldummy = () }
