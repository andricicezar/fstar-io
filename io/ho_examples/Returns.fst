module Returns

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

(** ***  accepts a function that returns a function **)
(** pp  - partial program (TRUSTED)
    ctx - context         (UNTRUSTED)
    ctx_r - returned by the context (UNTRUSTRED) **)

assume val ctx_r_in  : Type
assume val ctx_r_in_exportable : exportable ctx_r_in
assume val ctx_r_out : Type
assume val ctx_r_out_importable : importable ctx_r_out
assume val ctx_r_pre : ctx_r_in -> trace -> Type0
assume val ctx_r_post : ctx_r_in -> trace -> maybe ctx_r_out -> trace -> Type0
type ctx_r = x:ctx_r_in -> IIO (maybe ctx_r_out) (ctx_r_pre x) (ctx_r_post x)

assume val ctx_in : Type
assume val ctx_in_exportable : exportable ctx_in
assume val ctx_pre : ctx_in -> trace -> Type0
assume val ctx_post : ctx_in -> trace -> maybe ctx_r -> trace -> Type0
type ctx = x:ctx_in -> IIO (maybe ctx_r) (ctx_pre x) (ctx_post x)

assume val pp_out : Type
assume val pp_out_exportable : exportable pp_out
assume val pp_pre : trace -> Type0
assume val pp_post : trace -> maybe pp_out -> trace -> Type0
type pp = ctx -> IIO (maybe pp_out) pp_pre pp_post

assume val pi : monitorable_prop

(** the problem I suspected exists. **)

assume val ctx_r_post_monitorable : checkable_hist_post ctx_r_pre ctx_r_post pi

let ctx_r_instrumentable : instrumentable ctx_r pi =
  instrumentable_IIO_strengthen
    ctx_r_in #ctx_r_in_exportable
    ctx_r_out #ctx_r_out_importable
    ctx_r_pre ctx_r_post pi #ctx_r_post_monitorable

assume val ctx_post_monitorable : checkable_hist_post ctx_pre ctx_post pi

let ctx_instrumentable : instrumentable ctx pi =
  instrumentable_IIO_strengthen_inst
    ctx_in #ctx_in_exportable
    ctx_r
    ctx_pre
    ctx_post
    pi #ctx_post_monitorable
    #ctx_r_instrumentable
  
assume val pp_pre_checkable : checkable pp_pre

let pp_mlifyable : mlifyable pp (trivial_pi ()) =
  mlifyable_inst_iiowp_trivialize_weaken ctx #ctx_instrumentable pp_out #pp_out_exportable pp_pre #pp_pre_checkable pp_post 
