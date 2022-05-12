module Callback.Level1

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

(** ***  accepts a function that accepts a callback **)
(** pp  - partial program (TRUSTED)
    ctx - context         (UNTRUSTED)
    pp_cb - callback of partial program (TRUSTED) **)

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
assume val pp_cb_in  : Type
assume val pp_cb_in_importable : importable pp_cb_in
assume val pp_cb_out : Type
assume val pp_cb_out_exportable : exportable pp_cb_out
assume val pp_cb_pre : pp_cb_in -> trace -> Type0
assume val pp_cb_post : pp_cb_in -> trace -> maybe pp_cb_out -> trace -> Type0
type pp_cb = x:pp_cb_in -> IIO (maybe pp_cb_out) (pp_cb_pre x) (pp_cb_post x) 

(** The UNTRUSTED side accepts the callback.
    The UNTRUSTED side expects a callback that can fail.
    Its pre-condition is a promise, thus is not verified dynamically.
    Since the UNTRUSTED side is instrumented and its post-condition is dynamically
    enforced, its output type must reflect the possibility of a contract failure.
**)
assume val ctx_out : Type
assume val ctx_out_importable : importable (maybe ctx_out)
assume val ctx_pre : trace -> Type0
assume val ctx_post : trace -> maybe ctx_out -> trace -> Type0
type ctx = pp_cb -> IIO (maybe ctx_out) ctx_pre ctx_post 

assume val pp_out : Type
assume val pp_out_exportable : exportable pp_out
assume val pp_pre : trace -> Type0
assume val pp_post : trace -> maybe pp_out -> trace -> Type0
type pp = ctx -> IIO (maybe pp_out) pp_pre pp_post

assume val pp_cb_pre_checkable : checkable2 pp_cb_pre
assume val pp_cb_post_cpi : squash (forall x h lt r. pp_cb_pre x h /\ pp_cb_post x h r lt ==> enforced_locally pi h lt)


let pp_cb_mlifyable_guarded : mlifyable_guarded pp_cb_in pp_cb_out pp_cb_pre pp_cb_post pi = {
  cmlifyable = mlifyable_iiowp_trivialize_weaken_post pp_cb_in #pp_cb_in_importable pp_cb_out #pp_cb_out_exportable pp_cb_pre #pp_cb_pre_checkable pp_cb_post;
  cpi = pp_cb_post_cpi
}

assume val ctx_post_monitorable : monitorable_post #pp_cb_mlifyable_guarded.cmlifyable.matype (fun x -> ctx_pre) (fun x -> ctx_post) pi

let ctx_instrumentable : instrumentable ctx =
  instrumentable_HO pp_cb_in pp_cb_out pp_cb_pre pp_cb_post ctx_out ctx_pre ctx_post pi
  #ctx_out_importable
  #pp_cb_mlifyable_guarded
  #ctx_post_monitorable


assume val pp_pre_checkable : checkable pp_pre
  
let pp_mlifyable : mlifyable pp =
  mlifyable_inst_iiowp_trivialize_weaken ctx #ctx_instrumentable pp_out #pp_out_exportable pp_pre #pp_pre_checkable pp_post 

let test_output_type (main:pp) : (((pp_cb_in_importable.itype -> MIIO (maybe (pp_cb_out_exportable.etype))) -> IIOpi (ctx_out_importable.itype) pi) -> MIIO (maybe (pp_out_exportable.etype)))
  by (unfold_def (`Mkmlifyable?.matype); unfold_def (`Mkmlifyable_guarded?.cmlifyable); rewrite_eqs_from_context (); norm [iota]; 
  explode ();
  bump_nth 5;
//  dump "H";
  tadmit ()
  )=
  mlify #_ #(mlifyable_inst_iiowp_trivialize_weaken ctx #ctx_instrumentable pp_out #pp_out_exportable pp_pre #pp_pre_checkable pp_post) main

(** CA: I don't like in this example that every output type contains maybe.
    It is necessary to have this for cb and f because our effect does not support halting the execution
    when a contract failure occurs. **)
