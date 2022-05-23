module Callback.Level1

open FStar.Tactics

open Common
open DM 
open ILang
open IIO.Compile.Export
open TC.Checkable

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
    Therefore, the callback function can be mlified only if it is part of the class mlifyable_in.
**)
assume val pp_cb_in  : Type
assume val pp_cb_in_importable : importable pp_cb_in pi
assume val pp_cb_out : Type
assume val pp_cb_out_exportable : exportable pp_cb_out pi
assume val pp_cb_pre : pp_cb_in -> trace -> Type0
assume val pp_cb_post : pp_cb_in -> trace -> resexn pp_cb_out -> trace -> Type0
type pp_cb = x:pp_cb_in -> IIO (resexn pp_cb_out) (pp_cb_pre x) (pp_cb_post x) 

(** The UNTRUSTED side accepts the callback.
    The UNTRUSTED side expects a callback that can fail.
    Its pre-condition is a promise, thus is not verified dynamically.
    Since the UNTRUSTED side is instrumented and its post-condition is dynamically
    enforced, its output type must reflect the possibility of a contract failure.
**)
assume val ctx_out : Type
assume val ctx_out_importable : importable ctx_out pi
assume val ctx_pre : pp_cb -> trace -> Type0
assume val ctx_post : pp_cb -> trace -> resexn ctx_out -> trace -> Type0
type ctx = x:pp_cb -> IIO (resexn ctx_out) (ctx_pre x) (ctx_post x)

assume val pp_out : Type
assume val pp_out_exportable : exportable pp_out pi
assume val pp_pre : ctx -> trace -> Type0
assume val pp_post : ctx -> trace -> resexn pp_out -> trace -> Type0
type pp = x:ctx -> IIO (resexn pp_out) (pp_pre x) (pp_post x)


assume val pp_cb_pre_checkable : checkable2 pp_cb_pre

assume val pp_monitorable_hist : monitorable_hist pp_cb_pre pp_cb_post pi

let pp_cb_exportable : exportable pp_cb pi =
  exportable_arrow_with_pre_post
    pp_cb_in #pp_cb_in_importable
    pp_cb_out #pp_cb_out_exportable
    pp_cb_pre #pp_cb_pre_checkable
    pp_cb_post
    #pp_monitorable_hist

assume val ctx_post_monitorable : checkable_hist_post #pp_cb ctx_pre ctx_post pi

let ctx_importable : importable ctx pi =
  safe_importable_is_importable ctx #(
    safe_importable_arrow_pre_post
      pp_cb #pp_cb_exportable
      ctx_out #ctx_out_importable
      ctx_pre
      ctx_post
      #ctx_post_monitorable)

assume val pp_pre_checkable : checkable2 pp_pre
  
assume val pp_hist_monitorable : monitorable_hist pp_pre pp_post pi

let pp_exportable: exportable pp pi =
  exportable_arrow_with_pre_post
    ctx #ctx_importable
    pp_out #pp_out_exportable
    pp_pre #pp_pre_checkable
    pp_post
    #pp_hist_monitorable
