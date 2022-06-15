module MLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open MIO

(** ** Mlang **)

effect MIIO (a:Type) = IIO.IIOwp a (Hist.trivial_hist)

class mlang (t:Type) = { mldummy : unit }

(** *** FO instances **)
instance mlang_unit : mlang unit = { mldummy = () }

instance mlang_bool : mlang bool = { mldummy = () }
instance mlang_int : mlang int = { mldummy = () }

instance mlang_pair t1 t2 {| d1:mlang t1 |} {| d2:mlang t2 |} : mlang (t1 * t2) = 
  { mldummy = () }
instance mlang_either t1 t2 {| d1:mlang t1 |} {| d2:mlang t2 |} : mlang (either t1 t2) =
  { mldummy = () }

instance mlang_resexn t1 {| d1:mlang t1 |} : mlang (resexn t1) =
  { mldummy = () }

instance mlang_arrow #t1 #t2 (d1:mlang t1) (d2:mlang t2) : mlang (t1 -> MIIO (resexn t2)) =
  { mldummy = () }

open IO.Sig
open TC.Monitorable.Hist

let rec special_tree
  (pi : monitorable_prop)
  (tree : iio 'a) : Type0 =
  match tree with
  | Return _ -> True
  | PartialCall _ _ -> False
  | Call GetTrace arg k -> False
  | Call cmd arg k -> forall res. special_tree pi (k res)
  | Decorated dec m k ->
    (forall h lt. dec h lt ==> enforced_locally pi h lt) /\
    (forall res. special_tree pi (k res))

(** this diff is problematic because it allows to use Decorated node.
Decorated nodes come as input, but in the same time the predicate enables
writing bad stuff **)
type unverified_arrow (t1 t2:Type) pi =
  f:(t1 -> MIIO (resexn t2)){forall x. special_tree pi (reify (f x))} 

(** only this type of arrows can be instrumented. therefore
    the instrumentation is partial **)
instance mlang_unverified_arrow #t1 #t2 pi (d1:mlang t1) (d2:mlang t2) : mlang (unverified_arrow t1 t2 pi) =
  { mldummy = () }

// assume val pi : monitorable_prop

// type arr1 = unit -> MIIO unit

// val arr2 : unverified_arrow arr1 unit pi

// let arr2 f = Inl (f ())
