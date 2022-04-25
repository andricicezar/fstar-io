module TC.MLify.IIOwp

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.All
open FStar.Classical.Sugar

open Common
open TC.Export
include TC.MLify
open TC.Instrumentable

open Free
open IO.Sig
open DM.IIO

exception Something_went_really_bad

(** the_p is used at the spec level and they are used to instantiate later the 
    refinement of the DM: wp `hist_ord` theta m. By instantiating the refinement, we get:
    forall h. True ==> theta m (the_p ()) h, thus getting theta m. 
    It is important that the_p is defined as such to get True as pre-condition. **)
let the_p #a () : hist_post #event a = fun _ _ -> True

let rec skip_partial_calls (tree:iio 'a) (_:squash (forall h. dm_iio_theta tree (the_p ()) h)) : ML 'a =
  match tree with
  | Return y -> y
  | PartialCall pre k -> begin
    (** The intuition here is that the pre-condition is true,
    thus, all asserts are true **)
   assert (dm_iio_theta tree (the_p ()) []);
   assert pre;
   skip_partial_calls (k ()) ()
  end
  (** during extraction, Free.IO.Call is replaced with an actual
  implementation of the commands, therefore, the `Call` constructor
  does not exist **)
  | _ -> FStar.All.raise Something_went_really_bad


instance mlifyable_iiowp
  t1 t2 {| ml t1 |} {| ml t2 |} :
  Tot (mlifyable (t1 -> IIOwp t2 (trivial_hist ()))) =
  mk_mlifyable
    #(t1 -> IIOwp t2 (trivial_hist ()))
    (t1 -> ML t2)
    (fun f x -> 
     let tree : dm_iio t2 (trivial_hist ()) = reify (f x) in
     skip_partial_calls tree ())

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

instance mlifyable_inst_iiowp
  t1 t3
  {| d1:instrumentable t1 |} {| d2:ml t3 |} :
  Tot (mlifyable (t1 -> IIOwp t3 (trivial_hist ()))) =
  mk_mlifyable
    #_
    (d1.start_type -> ML t3)
    #(ml_ml_arrow_1 d1.start_type t3 #d1.start_type_c #d2)
    (fun (p:t1 -> IIOwp t3 (trivial_hist ())) (ct:d1.start_type) ->
     let tree : dm_iio t3 (trivial_hist ()) = reify (p (d1.instrument ct)) in
     skip_partial_calls tree ())
