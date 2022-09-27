module Compile.ILang.To.RILang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open TC.Monitorable.Hist

open Compile.ILang
open Compile.RILang

class is_reifiable (reify_in:Type u#a) (pi:monitorable_prop) = {
  [@@@no_method]
  reify_out : Type u#a;

  [@@@no_method]
  _reify: reify_in -> reify_out;

  [@@@no_method]
  ilang_reify_in : ilang reify_in pi;
  [@@@no_method]
  rilang_reify_out : rilang reify_out pi;
}

class is_reflectable (reflect_out:Type u#a) (pi:monitorable_prop) = {
  [@@@no_method]
  reflect_in : Type u#a;
  [@@@no_method]
  _reflect: reflect_in -> reflect_out;

  [@@@no_method]
  ilang_reflect_out : ilang reflect_out pi;
  [@@@no_method]
  rilang_reflect_in : rilang reflect_in pi;
}

assume val reify_IIOwp (#a:Type) (#wp:Hist.hist a) ($f:unit -> IIO.IIOwp a wp) : IIO.dm_iio a wp

#set-options "--print_implicits"

instance reify_ilang_arrow
  pi
  (t1:Type) {| d1:is_reflectable t1 pi |} 
  (t2:Type) {| d2:is_reifiable t2 pi |} :
  Tot (is_reifiable (t1 -> IIOpi t2 pi) pi) = {
    ilang_reify_in = ilang_arrow pi d1.ilang_reflect_out d2.ilang_reify_in;
    
    reify_out = d1.reflect_in -> rilang_dm pi d2.reify_out;

    rilang_reify_out = rilang_arrow pi d1.rilang_reflect_in d2.rilang_reify_out;

    _reify = (fun (src_f:t1 -> IIOpi t2 pi) (tgt_x:d1.reflect_in) -> 
      let src_x : t1 = d1._reflect tgt_x in
      let src_f' : unit -> IIOpi t2 pi = (fun () -> src_f src_x) in
      let tgt_f : IIO.dm_iio t2 (pi_as_hist pi) = reify_IIOwp src_f' in
      
      (* these are just casts *)
      let k : t2 -> IIO.dm_iio d2.reify_out (pi_as_hist pi) = (fun r -> IIO.dm_iio_return _ (d2._reify r)) in
      let wp : IO.Sig.hist d2.reify_out = Hist.hist_bind (pi_as_hist #t2 pi) (fun _ -> pi_as_hist pi) in 
      let tgt_w : IIO.dm_iio d2.reify_out wp = IIO.dm_iio_bind _ _ _ _ tgt_f k in
      lemma_bind_pi_implies_pi #t2 #d2.reify_out pi;
      let tgt_w : IIO.dm_iio d2.reify_out (pi_as_hist pi) = IIO.dm_iio_subcomp _ _ _ tgt_w in
      as_rilang_dm tgt_w
    );
  }

instance reflect_ilang_arrow
  pi 
  t1 {| d1:is_reifiable t1 pi |}
  t2 {| d2:is_reflectable t2 pi |} : 
  is_reflectable (t1 -> IIOpi t2 pi) pi = {
  ilang_reflect_out = ilang_arrow pi d1.ilang_reify_in d2.ilang_reflect_out; 
  
  reflect_in = d1.reify_out -> rilang_dm pi d2.reflect_in;
  rilang_reflect_in = rilang_arrow pi d1.rilang_reify_out d2.rilang_reflect_in;

  _reflect = (fun tgt_f (src_x:t1) -> 
    (let tgt_x : d1.reify_out = d1._reify src_x in
    let tree_f : rilang_dm pi d2.reflect_in = tgt_f tgt_x in
    let tree_f' : IO.Sig.iio d2.reflect_in = tree_f in

    (* these are just casts *)
    assert (pi_as_hist pi `Hist.hist_ord` IIO.dm_iio_theta tree_f');
    let tree_f : IIO.dm_iio d2.reflect_in (pi_as_hist pi) = tree_f' in
    let k : d2.reflect_in -> IIO.dm_iio t2 (pi_as_hist pi) = (fun r -> IIO.dm_iio_return _ (d2._reflect r)) in
    let wp : IO.Sig.hist t2 = Hist.hist_bind (pi_as_hist #d2.reflect_in pi) (fun _ -> pi_as_hist pi) in 
    let tree_w : IIO.dm_iio t2 wp = IIO.dm_iio_bind _ _ _ _ tree_f k in
    lemma_bind_pi_implies_pi #d2.reflect_in #t2 pi;
    let tree_w : IIO.dm_iio t2 (pi_as_hist pi) = IIO.dm_iio_subcomp _ _ _ tree_w in
    IIO.IIOwp?.reflect tree_w) <: IIOpi t2 pi
  )
}
