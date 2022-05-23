module Callback.Example

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

val pi : monitorable_prop
let pi cmd arg h =
  match cmd with
  | Openfile -> 
    let fnm : io_args Openfile = arg in not (fnm = "/tmp/passwd")
  | _ -> true

(** The type of the callback function.
    The callback function in this example has non-higher-order types as input and output.
    The callback is TRUSTED and it is passed by the main function to the UNTRUSTED side.
    Thus, callback must be mlified before being past to the UNTRUSTED side.
    Because the callback function is mlified, it means that the runtime checks can fail.
    Because the UNTRUSTED side is instrumented to respect pi --- meaning that the post-conditon
    of the UNTRUSTED side guarantees pi is respected --- the callback has also to respect pi.
    Therefore, the callback function can be mlified only if it is part of the class mlifyable_in.
**)
unfold let pp_cb_in = file_descr
val pp_cb_in_importable : importable pp_cb_in pi
let pp_cb_in_importable = 
  safe_importable_is_importable 
    pp_cb_in 
    #(ilang_is_safely_importable (ilang_file_descr pi))
unfold let pp_cb_out = bool
val pp_cb_out_exportable : exportable pp_cb_out pi
let pp_cb_out_exportable = ilang_is_exportable pp_cb_out #(ilang_bool pi)
val pp_cb_pre : pp_cb_in -> trace -> Type0
let pp_cb_pre = fun fd h -> is_open fd h
val pp_cb_post : pp_cb_in -> trace -> resexn pp_cb_out -> trace -> Type0
let pp_cb_post = fun fd h _ lt -> lt == []
type pp_cb = x:pp_cb_in -> IIO (resexn pp_cb_out) (pp_cb_pre x) (pp_cb_post x) 

(** The UNTRUSTED side accepts the callback.
    The UNTRUSTED side expects a callback that can fail.
    Its pre-condition is a promise, thus is not verified dynamically.
    Since the UNTRUSTED side is instrumented and its post-condition is dynamically
    enforced, its output type must reflect the possibility of a contract failure.
**)
unfold let ctx_out = unit
val ctx_out_importable : importable ctx_out pi
let ctx_out_importable = 
  safe_importable_is_importable 
    ctx_out 
    #(ilang_is_safely_importable (ilang_unit pi))
val ctx_pre : pp_cb -> trace -> Type0
let ctx_pre = fun _ _ -> true
val ctx_post : pp_cb -> trace -> resexn ctx_out -> trace -> Type0
let ctx_post = fun _ h _ lt -> enforced_locally pi h lt
type ctx = x:pp_cb -> IIO (resexn ctx_out) (ctx_pre x) (ctx_post x)

unfold let pp_out = unit
val pp_out_exportable : exportable pp_out pi
let pp_out_exportable = ilang_is_exportable pp_out #(ilang_unit pi)
val pp_pre : ctx -> trace -> Type0
let pp_pre = fun _ _ -> true
val pp_post : ctx -> trace -> resexn pp_out -> trace -> Type0
let pp_post = fun _ h _ lt -> enforced_locally pi h lt
type pp = x:ctx -> IIO (resexn pp_out) (pp_pre x) (pp_post x)

val pp_cb_pre_checkable : checkable2 pp_cb_pre
let pp_cb_pre_checkable = general_is_checkable2 file_descr trace (fun fd h -> is_open fd h)

val pp_cb_monitorable_hist : monitorable_hist pp_cb_pre pp_cb_post pi
let pp_cb_monitorable_hist = {
  c1post = admit ()
}

let pp_cb_exportable : exportable pp_cb pi =
  exportable_arrow_with_pre_post
    pp_cb_in #pp_cb_in_importable
    pp_cb_out #pp_cb_out_exportable
    pp_cb_pre #pp_cb_pre_checkable
    pp_cb_post
    #pp_cb_monitorable_hist

private
let lemma_c1post () : squash (forall (x:pp_cb) h lt. true /\ enforced_locally pi h lt ==> (exists (r:resexn unit). enforced_locally pi h lt)) by (explode (); witness (`(Inl ())))= ()

private
let lemma_c2post () : squash (forall h lt. enforced_locally pi h lt  ==> enforced_locally pi h lt) =
  lemma_c1post ()

val ctx_checkable_hist : checkable_hist_post #pp_cb ctx_pre ctx_post pi
let ctx_checkable_hist = {
  cmonitorable = {
    c1post = lemma_c1post ();
  };
  result_check = (fun _ _ _ _ -> true);
  c2post = lemma_c2post ();
}

let ctx_importable : importable ctx pi =
  safe_importable_is_importable ctx #(
    safe_importable_arrow_pre_post
      pp_cb #pp_cb_exportable
      ctx_out #ctx_out_importable
      ctx_pre
      ctx_post
      #ctx_checkable_hist)

val pp_pre_checkable : checkable2 pp_pre
let pp_pre_checkable = general_is_checkable2 ctx trace (fun _ _ -> true)
  
val pp_monitorable_hist : monitorable_hist pp_pre pp_post pi
let pp_monitorable_hist = {
  c1post = admit ()
}

let pp_exportable: exportable pp pi =
  exportable_arrow_with_pre_post
    ctx #ctx_importable
    pp_out #pp_out_exportable
    pp_pre #pp_pre_checkable
    pp_post
    #pp_monitorable_hist

let thePP : pp = fun theCtx ->
  let theCb : pp_cb = fun fd -> if is_open fd (get_trace ()) then Inl true else Inl false in
  theCtx theCb

exception Error_just_for_example

val theCtx : ctx_importable.itype
//let theCtx (theCb : file_descr -> IIOpi (resexn bool) pi) : IIOpi (resexn unit) pi =
let theCtx (theCb : pp_cb_exportable.etype) : IIOpi (resexn unit) pi =
  let fd = static_cmd Openfile "/tmp2/passwd" in
  if Inl? fd  then
    let test = theCb (Inl?.v fd) in
    if Inl? test && Inl?.v test then Inl ()
    else Inr Error_just_for_example
  else Inr Error_just_for_example

let main_mlify = export #_ #_ #pp_exportable thePP

let whole () : IIOpi (resexn unit) pi = main_mlify theCtx
