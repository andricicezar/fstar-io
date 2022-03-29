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

let lemma_all_continuations_are_weak (tree:dm_iio 'a (weakest_hist ())) (pre:pure_pre) (proof:squash pre) (k:(squash pre -> iio 'a)) :
  Lemma
    (requires (PartialCall? tree /\ PartialCall?.pre tree == pre /\ PartialCall?.cont tree == k))
    (ensures (weakest_hist () `hist_ord` (dm_iio_theta (k proof)))) =
  calc (hist_ord #event #'a) {
    weakest_hist ();
    `hist_ord` {}
    dm_iio_theta tree;
    `hist_ord` {}
    dm_iio_theta (PartialCall pre k);
    `hist_ord` {}
    hist_bind (DMFree.partial_call_wp pre) (fun r -> dm_iio_theta (k r));
    `hist_ord` {}
    dm_iio_theta (k proof);
  }

let rec skip_partial_calls (tree:dm_iio 'a (weakest_hist ())) : ML 'a =
  match tree with
  | Return y -> y
  | PartialCall pre k -> begin
    (** The intuition here is that the pre-condition is true,
    thus, all asserts are true **)
    (** the following assert is the refinement hidden by the dm **)
    assert (forall p h. weakest_hist #'a #event () p h ==> dm_iio_theta tree p h);
    assert (forall p h. dm_iio_theta tree p h);
    assert (forall p h. dm_iio_theta tree p h ==> pre);
    assert (forall (p:hist_post #event 'a) (h:trace). pre) by (
      let p = FStar.Tactics.forall_intro () in
      let h = FStar.Tactics.forall_intro () in
      mapply (ExtraTactics.instantiate_multiple_foralls (nth_binder (-7)) [binder_to_term p;binder_to_term h]);
      ignore (ExtraTactics.instantiate_multiple_foralls (nth_binder (-14)) [binder_to_term p;binder_to_term h]);
      assumption ());
    assert (pre) by (
      ignore (ExtraTactics.instantiate_multiple_foralls (nth_binder (-1)) [(`(fun _ _ -> True)); (`[])]);
      assumption ()
    );
    let proof : squash pre = () in
    lemma_all_continuations_are_weak tree pre proof k;
    let tree' : dm_iio 'a (weakest_hist ()) = k proof in
   skip_partial_calls tree'
  end
  (** during extraction, Free.IO.Call is replaced with an actual
  implementation of the commands, therefore, the `Call` constructor
  does not exist **)
  | _ -> FStar.All.raise Something_went_really_bad


instance mlifyable_iiowp
  t1 t2 {| ml t1 |} {| ml t2 |} :
  Tot (mlifyable (t1 -> IIOwp t2 (weakest_hist ()))) =
  mk_mlifyable
    #(t1 -> IIOwp t2 (weakest_hist ()))
    (t1 -> ML t2)
    (fun f x -> 
     let tree : dm_iio t2 (weakest_hist ()) = reify (f x) in
     skip_partial_calls tree)

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
  Tot (mlifyable (t1 -> IIOwp t3 (weakest_hist ()))) =
  mk_mlifyable
    #_
    (d1.start_type -> ML t3)
    #(ml_ml_arrow_1 d1.start_type t3 #d1.start_type_c #d2)
    (fun (p:t1 -> IIOwp t3 (weakest_hist ())) (ct:d1.start_type) ->
     let tree : dm_iio t3 (weakest_hist ()) = reify (p (d1.instrument ct)) in
     skip_partial_calls tree)
