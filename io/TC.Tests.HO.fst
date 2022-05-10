module TC.Tests.HO

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

(** ** Case 1 - function map **)
(** *** accepts a first-order function **)
type map_iio =
  (#a:Type) ->
  (#b:Type) ->
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

(** ** Case 2 (General) - callback **)
(** ***  accepts a function that accepts a callback **)
assume val cb_in  : Type
assume val cb_in_importable : importable cb_in
assume val cb_out : Type
(** TODO: for sure the pre and the import of the in can fail, therefore the cb for sure can fail **)
assume val cb_out_exportable : exportable cb_out
assume val cb_pre : cb_in -> trace -> Type0
assume val cb_post : cb_in -> trace -> cb_out -> trace -> Type0

assume val f_out : Type
assume val f_out_importable : importable (maybe f_out)
assume val f_pre : trace -> Type0
assume val f_post : trace -> maybe f_out -> trace -> Type0

assume val main_out : Type
assume val main_out_exportable : exportable main_out
assume val main_pre : trace -> Type0
assume val main_post : trace -> main_out -> trace -> Type0

type cb_type   = x:cb_in       -> IIO cb_out       (cb_pre x)    (cb_post x) 
type f_type    = cb:cb_type -> IIO (maybe f_out)        f_pre f_post 
(** TODO: the pre should be genral here. it is not general because I did not write an mlify instance for a checkable pre **)
type main_type = f: f_type  -> IIO main_out (fun _ -> True) main_post

assume val pi : monitorable_prop
assume val cb_pre_checkable : checkable2 cb_pre
assume val cb_post_cpi : squash (forall x h lt r. cb_pre x h /\ cb_post x h r lt ==> enforced_locally pi h lt)

let cb_type_mlifyable_guarded : mlifyable_guarded cb_in cb_out cb_pre cb_post pi = {
  cmlifyable = mlifyable_iiowp_3 cb_in cb_out #cb_in_importable #cb_out_exportable cb_pre #cb_pre_checkable cb_post;
  cpi = cb_post_cpi
}

assume val f_post_monitorable : monitorable_post #cb_type_mlifyable_guarded.cmlifyable.matype (fun x -> f_pre) (fun x -> f_post) pi

let f_type_instrumentable : instrumentable f_type =
  instrumentable_HO cb_in cb_out cb_pre cb_post f_out f_pre f_post pi
  #f_out_importable
  #cb_type_mlifyable_guarded
  #f_post_monitorable
  
let main_mlifyable : mlifyable main_type =
  mlifyable_inst_iiowp_post_2 f_type main_out main_post #f_type_instrumentable #main_out_exportable 

let test_output_type (main:main_type) : (((cb_in_importable.itype -> MIIO (maybe (cb_out_exportable.etype))) -> IIOpi (f_out_importable.itype) pi) -> MIIO (main_out_exportable.etype)) by (unfold_def (`Mkmlifyable?.matype); unfold_def (`Mkmlifyable_guarded?.cmlifyable); rewrite_eqs_from_context (); norm [iota]; 
  explode ();
  bump_nth 5;
  dump "H";
  tadmit () (** not sure how to unfold more **)
  )=
  mlify #_ #(mlifyable_inst_iiowp_post_2 f_type main_out main_post #f_type_instrumentable #main_out_exportable) main

(** ** Case 3 - apply **)
(** ***  - returns a function **)

(** ** Case 4 - HO Callback **)
(** ***  - callback with a callback **)
