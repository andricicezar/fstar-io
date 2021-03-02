module Rsp

open FStar.Calc
open FStar.Tactics

open Common
open ExtraTactics

open IO.Free
open IO.Effect
open IIO.Effect
open MIO.Effect
open MIIO.Effect
open Minterop
open IIO.Behavior

noeq type compiler = {
  interface : Type;
  set_of_traces : Type -> Type;
  monitorable_prop : Type;
  safety_prop   : (#a:Type) -> monitorable_prop -> set_of_traces a;

  res_s   : interface -> Type;
  prog_s  : interface -> monitorable_prop -> Type;
  ctx_s   : interface -> monitorable_prop -> Type;
  whole_s : interface -> monitorable_prop -> Type;
  link_s  : (#i:interface) -> (#pi:monitorable_prop) ->
            ctx_s i pi -> prog_s i pi -> Tot (whole_s i pi);

  res_t   : interface -> Type;
  prog_t  : interface -> Type;
  ctx_t   : interface -> Type;
  whole_t : interface -> Type;
  link_t  : (#i:interface) -> (#pi:monitorable_prop) ->
            ctx_t i -> prog_t i -> Tot (whole_t i);


  beh_s : (#i:interface) -> (#pi:monitorable_prop) ->
          whole_s i pi -> set_of_traces (res_s i);
  beh_t : (#i:interface) -> whole_t i -> set_of_traces (res_t i);

  included_in_s : (#i:interface) -> set_of_traces (res_s i) ->
                  set_of_traces (res_s i) -> Type;
  included_in_t : (#i:interface) -> set_of_traces (res_t i) ->
                  set_of_traces (res_s i) -> Type;

  compile_prog  : (#i:interface) -> (#pi:monitorable_prop) ->
                  prog_s i pi -> Tot (prog_t i);
  compile_whole : (#i:interface) -> (#pi:monitorable_prop) ->
                  whole_s i pi -> Tot (whole_t i);
}

noeq type interface = {
  ctx_arg : Type;
  ctx_arg_ce : exportable ctx_arg;
  ctx_ret: Type;
  ctx_ret_ci : importable ctx_ret;
  ctx_ret_ce : exportable ctx_ret;
  ctx_post :
    ctx_arg -> trace -> (m:maybe ctx_ret) -> trace -> (r:Type0{Inr? m ==> r});
  ctx_post_c : checkable4 ctx_post;

  ret : Type; ret_cm: ml ret;
}

let safety_prop = pi_to_set

val whole_pre' : unit -> trace -> bool
let whole_pre' _ _ = true

val whole_pre : unit -> trace -> Type0
let whole_pre x h = whole_pre' x h

let whole_pre_cc : checkable2 whole_pre =
  general_is_checkable2 unit trace whole_pre'

type whole_s (i:interface) (pi:monitorable_prop) =
  x:unit -> IIO i.ret pi (whole_pre x) (fun _ _ _ -> True)
type whole_t (i:interface) = unit -> MIIO i.ret

(** the lift from "MIO to MIIO" for the context should happen
during linking. It is improper to say "should happen", because
the lift represents the assumptions: "the context uses
only the IO library which comes with instrumentation".
 **)
let tpre : (i:interface) -> (i.ctx_arg -> trace -> bool) = fun i x h -> true
type ctx_s (i:interface) (pi:monitorable_prop) =
  (x:i.ctx_arg) -> IIO i.ctx_ret pi (fun h -> tpre i x h) (i.ctx_post x)
type ctx_p (i:interface) (pi:monitorable_prop) =
  x:i.ctx_arg_ce.etype -> IIO i.ctx_ret_ci.itype pi (fun _ -> True) (fun _ _ _ -> True)
type ctx_t (i:interface) = i.ctx_arg_ce.etype -> MIO i.ctx_ret_ci.itype

type prog_s (i:interface) (pi:monitorable_prop) =
  ctx_s i pi -> IIO i.ret pi (fun _ -> True) (fun _ _ _ -> True)
type prog_t (i:interface) (pi:monitorable_prop) =
  ctx_p i pi -> MIIO i.ret


let importable_ctx_s (i:interface) (pi:monitorable_prop) :
  Tot (r:(importable (ctx_s i pi)){r.itype == ctx_p i pi}) by (compute ()) =
  admit ();
  importable_safe_importable
    (ctx_s i pi)
    #(importable_MIIO_IIO
        i.ctx_arg #i.ctx_arg_ce
        i.ctx_ret #i.ctx_ret_ci
        pi
        (fun x h -> tpre i x h)
        #(general_is_checkable2 i.ctx_arg trace (tpre i))
        i.ctx_post
        #i.ctx_post_c)

let handle = _import_pi_IIO

let ctx_t_to_ctx_p
  (i  : interface)
  (pi : monitorable_prop)
  (ct : ctx_t i) :
  Tot (ctx_p i pi) =
  fun (x:i.ctx_arg_ce.etype) ->
    handle
      (cast_io_iio ((* MIIO.*)reify (ct x) [] (fun _ _ -> True))) pi

let _ctx_p_types
  (i  : interface)
  (pi : monitorable_prop)
  (cp : ctx_p i pi)
  (x  : i.ctx_arg) :
  IIO i.ctx_ret pi (fun _ -> True) (fun _ _ _ -> True) =
  admit ();
  let r : i.ctx_ret_ci.itype = cp (export x) in
  match import r with
  | Some r -> r
  | None -> IIO.Effect.throw Contract_failure

let ctx_p_to_ctx_s
  (i  : interface)
  (pi : monitorable_prop)
  (cp  : ctx_p i pi) :
  Tot (ctx_s i pi) =
  admit ();
  fun (x:i.ctx_arg) ->
    let h : trace = get_trace () in
    let r : i.ctx_ret = _ctx_p_types i pi cp x in
    let lt : trace = extract_local_trace h pi in
    Classical.forall_intro_2 (
    Classical.move_requires_2 (
        check4_implies_post #i.ctx_arg #i.ctx_ret x h r i.ctx_post #i.ctx_post_c (Inl lt)));
    explain_post_refinement i.ctx_post;
    enforce_post #i.ctx_arg #i.ctx_arg_ce #i.ctx_ret #i.ctx_ret_ci i.ctx_post #i.ctx_post_c x h r lt

let compile_prog
  (#i  : interface)
  (#pi : monitorable_prop)
  (f  : prog_s i pi) :
  Tot (prog_t i pi) =
  let pre : ctx_s i pi -> trace -> bool =  fun _ _ -> true in
  _export_IIO
    #(ctx_s i pi) #(importable_ctx_s i pi)
    #i.ret #(exportable_ml i.ret #i.ret_cm)
    pi
    (fun x h -> pre x h)
    #(general_is_checkable2 (ctx_s i pi) trace pre)
    (fun _ _ _ _ -> True)
    f

let compile_whole
  (#i  : interface)
  (#pi : monitorable_prop)
  (f  : whole_s i pi) :
  Tot (whole_t i) =
  _export_IIO_0
    #unit #i.ret
    pi
    whole_pre
    #whole_pre_cc
    (fun x h r lt -> True)
    f

val link_s  : (#i:interface) -> (#pi:monitorable_prop) -> ctx_s i pi ->
              prog_s i pi -> Tot (whole_s i pi)
let link_s = (fun #i #pi c p -> (fun _ -> p c))

val link_t  : (#i:interface) -> (#pi:monitorable_prop) -> ctx_t i ->
              prog_t i pi -> Tot (whole_t i)
let link_t #i #pi c p : whole_t i = (fun _ -> p (ctx_t_to_ctx_p i pi c))

val included_in' : (#i:interface) -> set_of_traces (maybe i.ret) ->
                    set_of_traces (maybe i.ret) -> Type0
let included_in' = (fun (#i:interface) -> included_in)

let beh_s
  (#i:interface)
  (#pi:monitorable_prop)
  (ws:whole_s i pi) =
  behavior (reify (ws ()) [] (iio_post pi []))

let beh_t
  (#i:interface)
  (wt:whole_t i) =
  behavior (reify (wt ()) [] (fun _ _ -> True))

let sc (i:interface) (pi:monitorable_prop) (ws:whole_s i pi) : Type0 =
  ((beh_t (compile_whole ws)) `included_in` beh_s ws)

let seci_respects_sc
  (i  : interface)
  (pi : monitorable_prop)
  (ws  : whole_s i pi) :
  Lemma (sc i pi ws) =
  (** proof by unfolding of LHS **)

  (** this is LHS unfolded **)
  let ww1 = reify (
            let h = get_trace () in
            if check2 #_ #_ #whole_pre #whole_pre_cc () h &&
               enforced_globally pi h then ws ()
            else IIO.Effect.throw (Contract_failure)
  ) [] (iio_post pi []) in

  (** TODO: prove that lift from MIIO to IIO preserves behavior **)
  assert (beh_t (compile_whole ws) `included_in` behavior ww1) by (
    norm [delta_only [`%compile_whole;`%_export_IIO_0;`%beh_t]; iota];
    dump "x";
    tadmit ()
  );

  let ww2 = reify (
            let h = [] in
            if check2 #_ #_ #whole_pre #whole_pre_cc () h &&
               enforced_globally pi h then ws ()
            else IIO.Effect.throw (Contract_failure)
  ) [] (iio_post pi []) in

  assume (ww1 == ww2)
  (** from this point, is obvious that the condition is true,
  and after normalization ws is obtained. **)

let tp (i:interface) (pi:monitorable_prop) (ws:whole_s i pi) : Type0 =
  ((beh_s ws `included_in'` (safety_prop pi)) ==>
    (beh_t (compile_whole ws) `included_in'` (safety_prop pi)))

let seci_respects_tp
  (i  : interface)
  (pi : monitorable_prop)
  (ws  : whole_s i pi) :
  Lemma (tp i pi ws) =
  (** we have to show:
      ```if beh ws ⊆ π then beh (compile ws) ⊆ π```
      proof:
      we show first that ```beh (compile ws) ⊆ beh ws```
      by unfolding compile.
      apply ⊆-transitivity property and we get
      ```beh (compile ws) ⊆ π```. **)
  seci_respects_sc i pi ws


val import_ctx_t : (#i:interface) -> (#pi:monitorable_prop) -> ctx_t i -> ctx_s i pi
let import_ctx_t #i #pi ct =
  ctx_p_to_ctx_s i pi (
    ctx_t_to_ctx_p i pi ct)

let beh_export_ps_ct_in_export_ws
  (i  : interface)
  (pi : monitorable_prop)
  (ps : prog_s i pi)
  (ct : ctx_t i) :
  Lemma (
    let (cs : ctx_s i pi) = import_ctx_t #i #pi ct in
    let ws : whole_s i pi = cs `link_s #i` ps in
    let pt : prog_t i pi = compile_prog ps in
    let wt : whole_t i = compile_whole #i #pi ws in
    beh_t (ct `link_t` pt) `included_in` beh_t wt
  ) =
  let cp = ctx_t_to_ctx_p i pi ct in
  let (cs : ctx_s i pi) = ctx_p_to_ctx_s i pi cp in
  let ws : whole_s i pi = cs `link_s` ps in
  let (cs : ctx_s i pi) = ctx_p_to_ctx_s i pi cp in
  let pt : prog_t i pi = compile_prog ps in
  let wt : whole_t i = compile_whole ws in
  let wt' : whole_t i = fun _ -> pt cp in
  assert (reify (wt' ()) [] (fun _ _ -> true) == reify (wt ()) [] (fun _ _ -> True)) by (
    norm [delta_only [`%ctx_t_to_ctx_p]];
    norm [delta_only [`%compile_prog; `%compile_whole; `%_export_IIO]];
    norm [delta_only [`%link_s]; iota];
    dump "h"
  );
  admit ();
  assert (
    beh_t (ct `link_t #i #pi` pt)
      `included_in`
    beh_t ((fun _ -> pt cp) <: whole_t i))
  by (norm [delta_only [`%link_t]])

let seci_rsp_0
  (i   : interface)
  (pi  : monitorable_prop)
  (ps  : prog_s i pi)
  (ct  : ctx_t i) :
  Lemma (
  (forall (cs:ctx_s i pi).
    (beh_s pi (cs `link_s` ps) ()) `included_in_s` (safety_prop pi))
  ==>  (
      let pt = compile_prog #i ps in
      beh_t (ct `link_t #i #pi` pt) () `included_in_t` (safety_prop pi))) =
  let (cp:ctx_p i pi) = ctx_t_to_ctx_p i pi ct in
  let (cs:ctx_s i pi) = ctx_p_to_ctx_s i pi cp in
  let ws : whole_s i pi = link_s cs ps in
  beh_gio_in_pi _ _ pi ws (); // Beh (ws ()) in pi
  seci_respects_tp i pi ws; // Beh (export ws ()) in Beh (ws ())
  beh_export_ps_ct_in_export_ws i pi ps ct // Beh ((export ps) ct) in Beh (export ws ())

let rsp (i:interface) (pi:monitorable_prop) (ps:prog_s i pi) : Type0 =
  (forall cs. beh_s pi (cs `link_s` ps) () `included_in_s` (safety_prop (pi)))
  ==> (forall (ct: ctx_t i). (
      let pt = compile_prog ps in
      beh_t (ct `link_t` pt) () `included_in_t` (safety_prop (pi))))

let seci_respects_rsp () :
  Lemma (forall i pi ps. rsp i pi ps) =
    Classical.forall_intro_4 (seci_rsp_0)



// let seci : compiler = {
//   interface = interface;
//   monitorable_prop = monitorable_prop;
//   safety_prop = pi_to_set;

//   set_of_traces = set_of_traces;

//   res_s   = (fun i -> maybe (trace * i.c));
//   prog_s  = prog_s;
//   ctx_s   = ctx_s;
//   whole_s = whole_s;

//   link_s = link_s;

//   res_t   = (fun i -> maybe (i.cd.etype));
//   prog_t  = prog_t;
//   ctx_t   = ctx_t;
//   whole_t = whole_t;
//   link_t = link_t;

//   beh_s = (fun #i #pi w -> beh_s #unit #i.c pi w ());
//   beh_t = (fun #i w -> beh_t #unit #i.cd.etype w ());

//   included_in_s = included_in_s;
//   included_in_t = included_in_t;

//   compile_prog  = compile_prog;
//   compile_whole = compile_whole;
// }
