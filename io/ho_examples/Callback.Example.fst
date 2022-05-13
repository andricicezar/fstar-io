module Callback.Example

open FStar.Tactics

open Common
open DM 
open TC.ML
open TC.ML.HO
open TC.Checkable
open TC.Export
open TC.MLify.IIOwp
open TC.Monitorable.Hist
open TC.Instrumentable.IIOwp
  
(** ** Callback example **)
(** ***  accepts a function that accepts a callback **)
val pi : monitorable_prop
let pi cmd arg h =
  match cmd with
  | Openfile -> 
    let fnm : io_args Openfile = arg in not (fnm = "/tmp/passwd")
  | _ -> true

unfold
type cb  = fd:file_descr -> IIO (maybe bool) (fun h -> is_open fd h) (fun h _ lt -> lt == [])
type ctx = cb:cb         -> IIO (maybe unit) (fun _ -> True)           (fun h r lt -> enforced_locally pi h lt)
type pp  = f: ctx        -> IIO (maybe unit) (fun _ -> True)           (fun h r lt -> enforced_locally pi h lt)

let cb_mlifyable : mlifyable cb = 
  mlifyable_iiowp_trivialize_weaken_post
    file_descr
    bool
    (fun fd h -> is_open fd h)
    (fun fd h _ lt -> lt == [])

let cb_mlifyable_guarded : mlifyable_guarded_arr1 file_descr bool (fun fd h -> is_open fd h) (fun fd h r lt -> lt == []) pi = {
  ca1 = importable_safe_importable file_descr;
  cmlifyable1 = cb_mlifyable;
  cpi1 = ()
}

private
let lemma_c1post () : squash (forall (x:cb_mlifyable_guarded.cmlifyable1.matype) h lt. True /\ enforced_locally pi h lt ==> (exists (r:maybe unit). enforced_locally pi h lt)) by (explode (); witness (`(Inl ())))= ()

private
let lemma_c2post () : squash (forall h lt. enforced_locally pi h lt  ==> enforced_locally pi h lt) =
  lemma_c1post ()

let pp_post_monitorable : monitorable_hist (fun fd h -> True) (fun fd h r lt -> enforced_locally pi h lt) pi = {
  result_check = (fun _ _ _ _ -> true);
  c1post = lemma_c1post ();
  c2post = lemma_c2post ();
}

let ctx_instrumentable : instrumentable ctx pi =
  instrumentable_HO_arr1_out_importable file_descr bool (fun fd h -> is_open fd h) (fun fd h r lt -> lt == []) unit (fun h -> True) (fun h r lt -> enforced_locally pi h lt) pi
  #(importable_safe_importable _ #(safe_importable_ml (maybe unit) #(mlfo_maybe unit #(ML_FO mlfo_unit))))
  #cb_mlifyable_guarded
  #pp_post_monitorable
  
let pp_mlifyable : mlifyable pp =
  mlifyable_inst_iiowp_weaken ctx #ctx_instrumentable (maybe unit) (fun h r lt -> enforced_locally pi h lt)

let main : pp = fun c ->
  let theCb : cb = fun fd -> if is_open fd (get_trace ()) then Inl true else Inl false in
  c theCb

(** I can not write a context in the intermediate language because the type of the callback is not informative 
    enough to know it respects pi. **)
let c (theCb : file_descr -> MIIO (maybe bool)) : IIOpi (maybe unit) pi =
  let fd = static_cmd Openfile "/tmp2/passwd" in
  if Inl? fd  then
    let test = theCb (Inl?.v fd) in
    if Inl? test && Inl?.v test then Inl ()
    else Inr Something_went_really_bad
  else Inr Something_went_really_bad

let main_mlify = mlify #_ #pp_mlifyable main

let whole () : MIIO (maybe unit) = main_mlify c
