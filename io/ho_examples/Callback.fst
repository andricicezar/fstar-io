module Callback

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

(** ** Case 2 (General) - callback **)
(** ***  accepts a function that accepts a callback **)
assume val pi : monitorable_prop

(** The type of the callback function.
    The callback function in this example has non-higher-order types as input and output.
    The callback is TRUSTED and it is passed by the main function to the UNTRUSTED side.
    Thus, callback must be mlified before being past to the UNTRUSTED side.
    Because the callback function is mlified, it means that the runtime checks can fail.
    Because the UNTRUSTED side is instrumented to respect pi --- meaning that the post-conditon
    of the UNTRUSTED side guarantees pi is respected --- the callback has also to respect pi.
    Therefore, the callback function can be mlified only if it is part of the class mlifyable_guarded.
**)
assume val cb_in  : Type
assume val cb_in_importable : importable cb_in
assume val cb_out : Type
assume val cb_out_exportable : exportable cb_out
assume val cb_pre : cb_in -> trace -> Type0
assume val cb_post : cb_in -> trace -> maybe cb_out -> trace -> Type0
type cb_type = x:cb_in -> IIO (maybe cb_out) (cb_pre x) (cb_post x) 

assume val cb_pre_checkable : checkable2 cb_pre
assume val cb_post_cpi : squash (forall x h lt r. cb_pre x h /\ cb_post x h r lt ==> enforced_locally pi h lt)

let cb_type_mlifyable_guarded : mlifyable_guarded cb_in cb_out cb_pre cb_post pi = {
  cmlifyable = mlifyable_iiowp_trivialize_weaken_post cb_in #cb_in_importable cb_out #cb_out_exportable cb_pre #cb_pre_checkable cb_post;
  cpi = cb_post_cpi
}

(** The UNTRUSTED side accepts the callback.
    The UNTRUSTED side expects a callback that can fail.
    Its pre-condition is a promise, thus is not verified dynamically.
    Since the UNTRUSTED side is instrumented and its post-condition is dynamically
    enforced, its output type must reflect the possibility of a contract failure.
**)
assume val f_out : Type
assume val f_out_importable : importable (maybe f_out)
assume val f_pre : trace -> Type0
assume val f_post : trace -> maybe f_out -> trace -> Type0
type f_type = cb:cb_type -> IIO (maybe f_out) f_pre  f_post 

assume val f_post_monitorable : monitorable_post #cb_type_mlifyable_guarded.cmlifyable.matype (fun x -> f_pre) (fun x -> f_post) pi

let f_type_instrumentable : instrumentable f_type =
  instrumentable_HO cb_in cb_out cb_pre cb_post f_out f_pre f_post pi
  #f_out_importable
  #cb_type_mlifyable_guarded
  #f_post_monitorable

assume val main_out : Type
assume val main_out_exportable : exportable main_out
assume val main_pre : trace -> Type0
assume val main_post : trace -> maybe main_out -> trace -> Type0
type main_type = f: f_type -> IIO (maybe main_out) main_pre main_post

assume val main_pre_checkable : checkable main_pre
  
let main_mlifyable : mlifyable main_type =
  mlifyable_inst_iiowp_trivialize_weaken f_type #f_type_instrumentable main_out #main_out_exportable main_pre #main_pre_checkable main_post 

let test_output_type (main:main_type) : (((cb_in_importable.itype -> MIIO (maybe (cb_out_exportable.etype))) -> IIOpi (f_out_importable.itype) pi) -> MIIO (maybe (main_out_exportable.etype)))
  by (unfold_def (`Mkmlifyable?.matype); unfold_def (`Mkmlifyable_guarded?.cmlifyable); rewrite_eqs_from_context (); norm [iota]; 
  explode ();
  bump_nth 5;
//  dump "H";
  tadmit ()
  )=
  mlify #_ #(mlifyable_inst_iiowp_trivialize_weaken f_type #f_type_instrumentable main_out #main_out_exportable main_pre #main_pre_checkable main_post) main

(** CA: I don't like in this example that every output type contains maybe.
    It is necessary to have this for cb and f because our effect does not support halting the execution
    when a contract failure occurs. **)
