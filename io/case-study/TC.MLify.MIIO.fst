module TC.MLify.MIIO

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.All

open Common
open TC.Export
include TC.MLify
open TC.Weaken.MIIO
open TC.Trivialize.MIIO

open Free
open Free.IO
open DM.MIIO

exception Something_went_really_bad
 
instance mlifyable_miio
  t1 t2 {| ml t1 |} {| ml t2 |} :
  Tot (mlifyable (t1 -> MIIO t2)) =
  mk_mlifyable
    #(t1 -> MIIO t2)
    (t1 -> ML t2)
    (fun f x -> 
     let tree : iio t2 = reify (f x) [] (fun _ _ -> True) in
     match tree with
     | Return y -> y
     (** during extraction, Free.IO.Call is replaced with an actual
     implementation of the commands, therefore, the `Call` constructor
     does not exist **)
     | _ -> FStar.All.raise Something_went_really_bad)
