module Callback.Level2

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

(** ***  accepts a function that accepts a callback that also accepts a callback **)
(** pp  - partial program (TRUSTED)
    ctx - context         (UNTRUSTED)
    pp_cb - callback of partial program (TRUSTED)
    ctx_cb - callback of context (UNTRUSTRED) **)

assume val ctx_cb_in  : Type
assume val ctx_cb_in_exportable : exportable ctx_cb_in
assume val ctx_cb_out : Type
assume val ctx_cb_out_importable : importable ctx_cb_out
assume val ctx_cb_pre : ctx_cb_in -> trace -> Type0
assume val ctx_cb_post : ctx_cb_in -> trace -> maybe ctx_cb_out -> trace -> Type0
type ctx_cb = x:ctx_cb_in -> IIO (maybe ctx_cb_out) (ctx_cb_pre x) (ctx_cb_post x)

assume val pp_cb_out : Type
assume val pp_cb_out_exportable : exportable pp_cb_out
assume val pp_cb_pre : trace -> Type0
assume val pp_cb_post : trace -> maybe pp_cb_out -> trace -> Type0
type pp_cb = ctx_cb -> IIO (maybe pp_cb_out) pp_cb_pre pp_cb_post 

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

assume val pi2 : monitorable_prop
assume val pi : monitorable_prop

(** the problem I suspected exists. **)

assume val ctx_cb_post_monitorable : checkable_hist_post ctx_cb_pre ctx_cb_post pi

let ctx_cb_instrumentable : instrumentable ctx_cb pi =
  instrumentable_IIO_strengthen
    ctx_cb_in #ctx_cb_in_exportable
    ctx_cb_out #ctx_cb_out_importable
    ctx_cb_pre ctx_cb_post pi #ctx_cb_post_monitorable

assume val pp_cb_pre_checkable : checkable pp_cb_pre
assume val pp_cb_monitorable_hist : monitorable_hist #ctx_cb (fun _ -> pp_cb_pre) (fun _ -> pp_cb_post) pi 
 
let pp_cb_mlifyable : mlifyable pp_cb pi =
  mlifyable_inst_iiowp_trivialize_weaken'
    ctx_cb #ctx_cb_instrumentable
    pp_cb_out #pp_cb_out_exportable
    pp_cb_pre #pp_cb_pre_checkable
    pp_cb_post
    #pp_cb_monitorable_hist

assume val ctx_post_monitorable : checkable_hist_post #pp_cb_mlifyable.matype (fun x -> ctx_pre) (fun x -> ctx_post) pi

let ctx_instrumentable : instrumentable ctx pi =
  instrumentable_HO_arr0_out_importable
    pp_cb
    ctx_out ctx_pre ctx_post
    pi
    #ctx_out_importable
    #pp_cb_mlifyable
    #ctx_post_monitorable
  
assume val pp_pre_checkable : checkable pp_pre

let pp_mlifyable : mlifyable pp (trivial_pi ())=
  mlifyable_inst_iiowp_trivialize_weaken
    ctx #ctx_instrumentable
    pp_out #pp_out_exportable
    pp_pre #pp_pre_checkable
    pp_post 
