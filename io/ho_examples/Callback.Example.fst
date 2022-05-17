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

let cb_monitorable_hist : monitorable_hist (fun fd h -> is_open fd h) (fun fd h (x:maybe bool) lt -> lt == []) pi = {
  c1post = admit ()
}

let cb_mlifyable : mlifyable cb pi = 
  mlifyable_iiowp_trivialize_weaken_post
    file_descr
    bool
    (fun fd h -> is_open fd h)
    (fun fd h _ lt -> lt == [])
    pi
    #cb_monitorable_hist
    

private
let lemma_c1post () : squash (forall (x:cb_mlifyable.matype) h lt. True /\ enforced_locally pi h lt ==> (exists (r:maybe unit). enforced_locally pi h lt)) by (explode (); witness (`(Inl ())))= ()

private
let lemma_c2post () : squash (forall h lt. enforced_locally pi h lt  ==> enforced_locally pi h lt) =
  lemma_c1post ()

let pp_post_monitorable : checkable_hist_post (fun fd h -> True) (fun fd h r lt -> enforced_locally pi h lt) pi = {
  cmonitorable = {
    c1post = lemma_c1post ();
  };
  result_check = (fun _ _ _ _ -> true);
  c2post = lemma_c2post ();
}

unfold
let ctx_instrumentable : instrumentable ctx pi =
  instrumentable_HO_arr1_out_importable
    cb
    unit (fun h -> True) (fun h r lt -> enforced_locally pi h lt) 
    pi
    #(importable_safe_importable _ #(safe_importable_ml (maybe unit) #(mlfo_maybe unit #(ML_FO mlfo_unit))))
    #cb_mlifyable
    #pp_post_monitorable
  
let pp_mlifyable : mlifyable pp (trivial_pi ()) =
  mlifyable_inst_iiowp_weaken ctx #ctx_instrumentable (maybe unit) (fun h r lt -> enforced_locally pi h lt)

let main : pp = fun c ->
  let theCb : cb = fun fd -> if is_open fd (get_trace ()) then Inl true else Inl false in
  c theCb

val c : ctx_instrumentable.inst_type
//let c (theCb : file_descr -> IIOpi (maybe bool) pi) : IIOpi (maybe unit) pi =
let c (theCb : cb_mlifyable.matype) : IIOpi (maybe unit) pi =
  let fd = static_cmd Openfile "/tmp2/passwd" in
  if Inl? fd  then
    let test = theCb (Inl?.v fd) in
    if Inl? test && Inl?.v test then Inl ()
    else Inr Something_went_really_bad
  else Inr Something_went_really_bad

let main_mlify = mlify #_ #_ #pp_mlifyable main

let whole () : MIIO (maybe unit) = main_mlify c
