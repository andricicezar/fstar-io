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
open DM.IIO
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


(** this is necessary, because F* does not add at extraction the lift from Tot to IIO. **)
let wrap (f:'a -> Tot 'b) pi (x:'a) : IIO 'b pi (fun _ -> True) (fun _ _ _ -> True) = f x
  
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

instance mlifyable_iio_miio
  t1 t2 t3 (pi:monitorable_prop)
  {| ml t1 |} {| ml t2 |} {| ml t3 |} :
  Tot (mlifyable ((t1 -> IIO t2 pi (fun _ -> True) (fun _ _ _ -> True)) -> MIIO t3)) =
  mk_mlifyable
    #_
    #(trivial_MIIO (t1 -> IIO t2 pi (fun _ -> True) (fun _ _ _ -> True)) _)
    #(weak_iio_miio t1 t2 t3 pi)
    ((t1 -> Tot t2) -> ML t3)
    (fun p (ct:t1 -> Tot t2) ->
     let tree : iio t3 = reify (p (wrap ct pi)) [] (fun _ _ -> True) in
     match tree with
     | Return y -> y
     (** during extraction, Free.IO.Call is replaced with an actual
     implementation of the commands, therefore, the `Call` constructor
     does not exist **)
     | _ -> FStar.All.raise Something_went_really_bad)
