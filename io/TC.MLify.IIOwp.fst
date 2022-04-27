module TC.MLify.IIOwp

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.All
open FStar.Classical.Sugar

open Common
open TC.ML
open TC.ML.HO
open TC.Export
open TC.Monitorable.Hist

open Free
open IO.Sig
open DM.IIO

exception Something_went_really_bad

instance mlifyable_iiowp
  t1 t2 {| ml t1 |} {| ml t2 |} :
  Tot (mlifyable (t1 -> IIOwp t2 (trivial_hist ()))) =
  mk_mlifyable
    #(t1 -> IIOwp t2 (trivial_hist ()))
    (t1 -> MIIO t2)
    (fun f x -> f x)

(** Ideas to improve mlifyable_iio_miio:
1. What if instead of Tot, we use Ex, to be able to internalize try_catch.
   This implies writing a lift from Ex to IIOwp. To do that, we also have to 
   write elim_ex (similar to elim_pure). I did not try to write it yet.
   But what does exactly means to use Ex? 
   Why Ex and not another effect? Answer: well, Ex has native extraction,
     therefore the try_with block will be extracted to the OCaml's native
     try/with.
   Maybe to not create more confusion & to not tie things too much to F*,
   it is better to not use Ex since it may be just a hack (check with Catalin). 
**)

instance mlifyable_inst_iiowp
  t1 t2
  {| d1:instrumentable t1 |} {| d2:ml t2 |} :
  Tot (mlifyable (t1 -> IIOwp t2 (trivial_hist ()))) =
  mk_mlifyable
    #_
    (d1.inst_type -> MIIO t2)
    #(ml_arrow_miio d1.inst_type t2 #(ML_INST d1.cinst_type) #d2)
    (fun (p:t1 -> IIOwp t2 (trivial_hist ())) (ct:d1.inst_type) ->
      p (d1.strengthen ct))


class mlifyable_guarded (a b:Type) pre post pi =
  { cmlifyable : mlifyable ((x:a) -> IIO b (pre x) (post x));
    cpi : squash (forall (x:a) h lt r. pre x h /\ post x h r lt ==> enforced_locally pi h lt) }
  
instance hooooo
  a b c fpre fpost cpre cpost pi 
  {| d0: ml (maybe c) |}
  {| d1:mlifyable_guarded a b fpre fpost pi |}
  {| d2:monitorable_post (fun x -> cpre) (fun x -> cpost) pi |} : 
  instrumentable ((x:a -> IIO b (fpre x) (fpost x)) -> DM.IIO.IIO (maybe c) cpre cpost) =
  {
    inst_type = d1.cmlifyable.matype -> IIOpi (maybe c) pi;
    cinst_type = ml_instrumented_iio d1.cmlifyable.matype (maybe c) #(ML_ARROW d1.cmlifyable.cmatype) #d0 pi;
    strengthen = (fun (ctx:(d1.cmlifyable.matype -> IIOpi (maybe c) pi)) -> 
      (fun (f:(x:a -> IIO b (fpre x) (fpost x))) -> 
      
        TC.Instrumentable.IIOwp.enforce_post #(d1.cmlifyable.matype) #c pi (fun x -> cpre) (fun x -> cpost) #d2 ctx (d1.cmlifyable.mlify f) <: IIO (maybe c) cpre cpost))
  }
