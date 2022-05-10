module TC.Tests.HO

open FStar.Tactics

open Common
open DM 
open TC.ML
open TC.ML.HO
open TC.Export
open TC.MLify.IIOwp
open TC.Monitorable.Hist
open TC.Instrumentable.IIOwp

type imptype = (x:Type{importable x})
type exptype = (x:Type{exportable x})


(** ** Case 1 - function map **)
(** *** accepts a first-order function **)
type map_iio =
  (#a:imptype) ->
  (#b:exptype) ->
  (#pre:(a -> trace -> bool)) ->
  (#post:(a -> trace -> b -> trace -> Type0)) ->
  (f:(x:a -> IIO b (fun h -> pre x h) (post x))) ->
  (xs:list a) ->
  IIO (list b) 
    (requires (fun h -> forall x. x `List.Tot.memP` xs ==> pre x h))
    (ensures (fun _ _ _ -> True)) (** it is hard to write a useful post-condition. However, we're not interested in it **)

let map_is_mlifyable : mlifyable map_iio = admit ()
(** Todo:
  1. a must be importable
  2. b must be exportable
  3. pre must be checkable
  4. post must be monitorable
  5. show that map's pre is checkable by having f's pre being checkable
**)

(** ** Case 2 - callback **)
(** ***  accepts a function that accepts a callback **)
val pi : monitorable_prop
let pi cmd arg h =
  match cmd with
  | Openfile -> 
    let fnm : io_args Openfile = arg in not (fnm = "/tmp/passwd")
  | _ -> true

type cb_type   = fd:file_descr -> IIO bool         (fun h -> is_open fd h) (fun h _ lt -> lt == [])
type f_type    = cb:cb_type    -> IIO (maybe unit) (fun _ -> True)            (fun h r lt -> enforced_locally pi h lt)
type main_type = f: f_type     -> IIO unit         (fun _ -> True)            (fun h r lt -> enforced_locally pi h lt)

let cb_type_mlifyable : mlifyable cb_type = mlifyable_iiowp_2 file_descr bool #(ML_FO mlfo_file_descr) #(ML_FO mlfo_bool) (fun fd h -> is_open fd h) (fun fd h _ lt -> lt == [])

let cb_type_mlifyable_guarded : mlifyable_guarded file_descr bool (fun fd h -> is_open fd h) (fun fd h r lt -> lt == []) pi = {
  cmlifyable = cb_type_mlifyable;
  cpi = ()
}

private
let lemma_c1post () : squash (forall (x:cb_type_mlifyable_guarded.cmlifyable.matype) h lt. True /\ enforced_locally pi h lt ==> (exists (r:maybe unit). enforced_locally pi h lt)) by (explode (); witness (`(Inl ())))= ()

private
let lemma_c2post () : squash (forall h lt. enforced_locally pi h lt  ==> enforced_locally pi h lt) =
  lemma_c1post ()

let f_post_monitorable () : monitorable_post (fun fd h -> True) (fun fd h r lt -> enforced_locally pi h lt) pi = {
  result_check = (fun _ _ _ _ -> true);
  c1post = lemma_c1post ();
  c2post = lemma_c2post ();
}

let f_type_instrumentable : instrumentable f_type =
  instrumentable_HO file_descr bool (fun fd h -> is_open fd h) (fun fd h r lt -> lt == []) unit (fun h -> True) (fun h r lt -> enforced_locally pi h lt) pi
  #(importable_safe_importable _ #(safe_importable_ml (maybe unit) #(mlfo_maybe unit #(ML_FO mlfo_unit))))
  #cb_type_mlifyable_guarded
  #(f_post_monitorable ())
  
let main_mlifyable : mlifyable main_type =
  mlifyable_inst_iiowp_post f_type unit (fun fd h r lt -> enforced_locally pi h lt) #f_type_instrumentable #(ML_FO mlfo_unit)

(** ** Case 3 - apply **)
(** ***  - returns a function **)

(** ** Case 4 - HO Callback **)
(** ***  - callback with a callback **)
