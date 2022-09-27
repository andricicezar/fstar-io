module Compile.RILang.To.MLang

open FStar.List.Tot
open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open TC.Monitorable.Hist

open Compile.RILang
open Compile.MLang

let dm_mon (pi:monitorable_prop) : monad = {
  m = rilang_dm pi;
  ret = (fun (x:'a) -> IIO.dm_iio_return 'a x);
  bind = (fun (m:rilang_dm pi 'a) (k:'a -> rilang_dm pi 'b) -> 
    let wp : Hist.hist 'b = Hist.hist_bind (pi_as_hist #'a pi) (fun _ -> pi_as_hist pi) in 
    let tr : IIO.dm_iio 'b wp = IIO.dm_iio_bind _ _ _ _ (as_iio_dm m) (fun x -> as_iio_dm (k x)) in
    lemma_bind_pi_implies_pi #'a #'b pi;
    let w = IIO.dm_iio_subcomp 'b wp (pi_as_hist pi) tr in
    as_rilang_dm w)
}

assume val dm_acts (pi:monitorable_prop) : acts (dm_mon pi)

class compilable (comp_in:Type u#a) (pi:monitorable_prop) = {
  comp_out : Type u#b;
  compile: comp_in -> comp_out;

  [@@@no_method]
  rilang_comp_in : rilang comp_in pi;
  [@@@no_method]
  mlang_comp_out : mlang comp_out;
}

(** *** Compilable arrows **)
instance compile_arrow
  pi
  (ct:((Type->Type)->Type)) {| d1:rilang (ct (dm_mon pi).m) pi |} {| d1':mlang (ct free.m) |}
  (t2:Type) {| d2:compilable t2 pi |} :
  Tot (compilable ((ct (dm_mon pi).m) -> rilang_dm pi t2) pi) = {
  rilang_comp_in = rilang_arrow pi d1 d2.rilang_comp_in;

  comp_out = (mon:monad -> acts mon -> ct mon.m) -> free.m d2.comp_out;
  mlang_comp_out = mlang_free_arrow (mlang_effectpoly d1') d2.mlang_comp_out;

  compile = (fun (f:((ct (dm_mon pi).m) -> rilang_dm pi t2)) (tgt_x:(mon:monad -> acts mon -> ct mon.m)) ->
    let src_x : ct (dm_mon pi).m = tgt_x (dm_mon pi) (dm_acts pi) in
    let r : rilang_dm pi t2 = f src_x in
    let r = as_iio_dm r in 
    let w = IIO.dm_iio_bind _ _ _ (fun _ -> (pi_as_hist pi)) r (fun x -> IIO.dm_iio_return _ (d2.compile x)) in
    w
  );
}
