module Compile.RILang

(** *** Reified ILang *)
(** Reified ILang is very similar to ILang, but instead of using the IIOpi effect directly,
    it is using the underlying Dijkstra Monad *)

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open TC.Monitorable.Hist

class rilang (t:Type u#a) (pi:monitorable_prop) = { mldummy : unit }

instance rilang_unit (pi:monitorable_prop) : rilang unit pi = { mldummy = () }
instance rilang_file_descr (pi:monitorable_prop) : rilang file_descr pi = { mldummy = () }

instance rilang_bool (pi:monitorable_prop) : rilang bool pi = { mldummy = () }
instance rilang_int (pi:monitorable_prop) : rilang int pi = { mldummy = () }
instance rilang_option (pi:monitorable_prop) t1 {| d1:rilang t1 pi |} : rilang (option t1) pi =
  { mldummy = () }
instance rilang_pair (pi:monitorable_prop) t1 {| d1:rilang t1 pi |} t2 {| d2:rilang t2 pi |} : rilang (t1 * t2) pi = 
  { mldummy = () }
instance rilang_either (pi:monitorable_prop) t1 {| d1:rilang t1 pi |} t2 {| d2:rilang t2 pi |} : rilang (either t1 t2) pi =
  { mldummy = () }
instance rilang_resexn (pi:monitorable_prop) t1 {| d1:rilang t1 pi |} : rilang (resexn t1) pi =
  { mldummy = () }

type rilang_dm (pi:monitorable_prop) (a:Type) = c:(IO.Sig.iio a){pi_as_hist pi `Hist.hist_ord` IIO.dm_iio_theta c} 

let as_rilang_dm (w:IIO.dm_iio 'a (pi_as_hist 'p)) : rilang_dm 'p 'a = w

let as_iio_dm (w:rilang_dm 'p 'a) : IIO.dm_iio 'a (pi_as_hist 'p) = 
  let tree : IO.Sig.iio 'a = w in
  assert (pi_as_hist 'p `Hist.hist_ord` IIO.dm_iio_theta tree);
  tree

type rilang_arrow_typ (t1 t2:Type) pi = t1 -> rilang_dm pi t2

instance rilang_arrow (#pi1 #pi2 pi:monitorable_prop) #t1 (d1:rilang t1 pi1) #t2 (d2:rilang t2 pi2) : rilang (rilang_arrow_typ t1 t2 pi) pi =
  { mldummy = () }
