module TC.MLify.MIIO

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.All

open Common
open TC.Export
include TC.MLify
open TC.Instrumentable

open Free
open IO.Sig
open DM.IIO

exception Something_went_really_bad
 
instance mlifyable_miio
  t1 t2 {| ml t1 |} {| ml t2 |} :
  Tot (mlifyable (t1 -> IIOwp t2 (fun _ _ -> True))) =
  mk_mlifyable
    #(t1 -> IIOwp t2 (fun _ _ -> True))
    (t1 -> ML t2)
    (fun f x -> 
     let tree : iio t2 = reify (f x) in
     match tree with
     | Return y -> y
     (** during extraction, Free.IO.Call is replaced with an actual
     implementation of the commands, therefore, the `Call` constructor
     does not exist **)
     | _ -> FStar.All.raise Something_went_really_bad)

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
2. can I move enforcing the post-condition here? It should be possible.
**)

instance mlifyable_inst_miio
  t1 t3
  {| d1:instrumentable t1 |} {| d2:ml t3 |} :
  Tot (mlifyable (t1 -> IIOwp t3 (fun _ _ -> True))) =
  mk_mlifyable
    #_
    (d1.start_type -> ML t3)
    #(ml_ml_arrow_1 d1.start_type t3 #d1.start_type_c #d2)
    (fun (p:t1 -> IIOwp t3 (fun _ _ -> True)) (ct:d1.start_type) ->
     let tree : iio t3 = reify (p (d1.instrument ct)) in
     match tree with
     | Return y -> y
     (** during extraction, Free.IO.Call is replaced with an actual
     implementation of the commands, therefore, the `Call` constructor
     does not exist **)
     | _ -> FStar.All.raise Something_went_really_bad)
