module Rsp

open FStar.Calc
open FStar.Tactics

open Common
open IOStHist
open M4
open Minterop
open IO.Behavior

noeq type compiler = {
  interface : Type;
  set_of_traces : Type -> Type;
  monitorable_prop : Type;
  safety_prop   : (#a:Type) -> monitorable_prop -> set_of_traces a;

  res_s   : interface -> Type;
  prog_s  : interface -> monitorable_prop -> Type;
  ctx_s   : interface -> monitorable_prop -> Type;
  whole_s : interface -> monitorable_prop -> Type;
  link_s  : (#i:interface) -> (#pi:monitorable_prop) -> ctx_s i pi -> prog_s i pi -> Tot (whole_s i pi);

  res_t   : interface -> Type;
  prog_t  : interface -> monitorable_prop -> Type;
  ctx_t   : interface -> Type;
  whole_t : interface -> Type;
  link_t  : (#i:interface) -> (#pi:monitorable_prop) -> ctx_t i -> prog_t i pi -> Tot (whole_t i);


  beh_s : (#i:interface) -> (#pi:monitorable_prop) -> whole_s i pi -> set_of_traces (res_s i);
  beh_t : (#i:interface) -> whole_t i -> set_of_traces (res_t i);

  included_in_s : (#i:interface) -> set_of_traces (res_s i) -> set_of_traces (res_s i) -> Type;
  included_in_t : (#i:interface) -> set_of_traces (res_t i) -> set_of_traces (res_s i) -> Type;

  compile_prog  : (#i:interface) -> (#pi:monitorable_prop) -> prog_s i pi -> Tot (prog_t i pi);
  compile_whole : (#i:interface) -> (#pi:monitorable_prop) -> whole_s i pi -> Tot (whole_t i);
}
  
let rsp (op:compiler) (i:op.interface) (pi:op.monitorable_prop) (ps:op.prog_s i pi) : Type0 =
  (forall cs. op.beh_s (cs `op.link_s` ps) `op.included_in_s` (op.safety_prop pi))
  ==> (forall (ct: op.ctx_t i). (
      let pt = op.compile_prog ps in
      op.beh_t (ct `op.link_t` pt) `op.included_in_t` (op.safety_prop pi)))

let tp (op:compiler) (i:op.interface) (pi:op.monitorable_prop) (ws:op.whole_s i pi) : Type0 =
    ((op.beh_s ws `op.included_in_s` (op.safety_prop pi)) ==>  
      (op.beh_t (op.compile_whole ws) `op.included_in_t` (op.safety_prop pi)))

noeq type interface = {
  a : Type;  ad : exportable a;
  b : Type;  bd : ml b;         // b has to be importable and exportable
  c : Type;  cd : exportable c;
  post : a -> events_trace -> maybe (events_trace * b) -> events_trace -> Type; 
  cpost : checkable4 post;
}

type whole_s (i:interface) (pi:check_type) = unit -> M4wp i.c pi (fun _ _ _ -> True)
type whole_t (i:interface) = unit -> M4 i.cd.etype

type ctx_s (i:interface) (pi:check_type) = (x:i.a) -> M4wp i.b pi (i.post x)
type ctx_p (i:interface) (pi:check_type) = i.ad.etype -> M4wp i.b pi (fun _ _ _ -> True)
type ctx_t (i:interface) = i.ad.etype -> M4 i.b

type prog_s (i:interface) (pi:check_type) = ctx_s i pi -> M4wp i.c pi (fun _ _ _ -> True)
type prog_t (i:interface) (pi:check_type) = ctx_p i pi -> M4 i.cd.etype

unfold 
let beh_s 
  #a
  #b
  (pi:check_type) 
  (ws:(x:a -> M4wp b pi (fun _ _ _ -> True))) 
  (x:a) =
  behavior (reify (ws x) (gio_post pi []) [])

unfold
let beh_t #a #b (wt:a -> M4 b) (x:a) =
  behavior (reify (wt x) (fun _ -> True))

let rec handle #t2 (tree : io (t2)) (pi:check_type) : M4wp t2 pi (fun _ _ _ -> True) = begin
  match tree with
  | Return r -> r 
  | Throw r -> IOStHist.throw r
  | Cont (Call cmd argz fnc) ->
      let rez : res cmd = IOStHist.dynamic_cmd cmd pi argz in
      FStar.WellFounded.axiom1 fnc (Inl rez);
      let z' : sys io_cmds io_cmd_sig t2 = fnc (Inl rez) in
      rev_append_rev_append ();
      handle z' pi
end

let extract_local_events (s0 s1:events_trace) :
  Pure events_trace
    (requires (exists le. s1 == apply_changes s0 le))
    (ensures (fun le -> s1 == apply_changes s0 le)) = 
  admit ();
  assert (List.length s1 >= List.length s0);
  let n : nat = (List.length s1) - (List.length s0) in
  let (le, _) = List.Tot.Base.splitAt n s1 in
  List.rev le

let ctx_p_to_ctx_s
  (i  : interface)
  (pi : check_type)
  (cp  : ctx_p i pi) : 
  Tot (ctx_s i pi) =
  fun (x:i.a) -> 
    admit ();
    let s0 : events_trace = IOStHist.get () in
    let result : i.b = cp x in
    let s1 : events_trace = IOStHist.get () in
    let le = extract_local_events s0 s1 in

    if check4 #i.a #i.b #i.post #i.cpost x s0 (Inl (s1, result)) le then (
      assert (i.post x s0 (Inl (s1, result)) le);
      result
    ) else IOStHist.throw Contract_failure

let ctx_t_to_ctx_p
  (i  : interface)
  (pi : check_type)
  (ct : ctx_t i) :
  Tot (ctx_p i pi) =
  fun (x:i.ad.etype) -> handle (reify (ct x) (fun _ -> True)) pi

let export_prog_s
  (i  : interface)
  (pi : check_type)
  (f  : prog_s i pi) : 
  Tot (prog_t i pi) =
    (fun (ct:ctx_p i pi) ->
      let cs = ctx_p_to_ctx_s i pi ct in
      let tree : io (events_trace * i.c) = reify (f cs) (gio_post pi []) [] in
      export (MFOUR?.reflect (fun _ -> iost_to_io tree) <: MFOUR i.c (fun p -> forall res. p res)))

let seci : compiler = {
  interface = interface;
  monitorable_prop = check_type;
  safety_prop = pi_to_set;

  set_of_traces = set_of_traces;

  res_s   = (fun i -> maybe (events_trace * i.c));
  prog_s  = (fun i pi -> prog_s i pi);
  ctx_s   = (fun i pi -> ctx_s i pi);
  whole_s = (fun i pi -> whole_s i pi);
  
  link_s = (fun #i #pi c p -> (fun _ -> p c) <: whole_s i pi);

  res_t   = (fun i -> maybe (i.cd.etype));
  prog_t  = (fun i pi -> prog_t i pi);
  ctx_t   = (fun i -> ctx_t i);
  whole_t = (fun i -> whole_t i);
  link_t = (fun #i #pi c p -> (fun _ -> p (ctx_t_to_ctx_p i pi c)) <: whole_t i);

  beh_s = (fun #i #pi w -> beh_s #unit #i.c pi w ());
  beh_t = (fun #i w -> beh_t #unit #i.cd.etype w ());
  
  included_in_s = (fun #i -> included_in id);
  included_in_t = (fun #i -> included_in #(maybe i.cd.etype) #(maybe (events_trace * i.c)) (inl_app (compose export cdr)));

  compile_prog  = (fun #i #pi -> export_prog_s i pi);
  compile_whole = (fun #i #pi -> _export_GIO_arrow_spec pi);
}

let _export_whole_lemma
  #t1 {| d1:importable t1 |} 
  #t2 {| d2:exportable t2 |}
  (pi : check_type) 
  (f:(x:t1 -> M4wp t2 pi (fun _ _ _ -> True))) 
  (x':d1.itype) : 
  Lemma (
    let ef : d1.itype -> M4 d2.etype = _export_GIO_arrow_spec pi f in
    match import x' with
    | Some x -> (
       beh_t ef x' `included_in (inl_app (compose export cdr))` beh_s pi f x)
    | None -> beh_t ef x' `included_in id` empty_set ()) =

  let ef : d1.itype -> M4 d2.etype = _export_GIO_arrow_spec pi f in
  let included_in_id #a = included_in #a #a (id #a) in
  match import x' with
  | Some x -> begin
    let l = reify (ef x') (fun _ -> True) in
    let __ll : unit -> MFOUR d2.etype (fun p -> forall res. p res) = (fun _ -> 
            let tree : io (events_trace * t2) = reify (f x) (gio_post pi []) [] in
            export (MFOUR?.reflect (fun _ -> iost_to_io tree) <: MFOUR t2 (fun p -> forall res. p res))) in
    let ll = reify (__ll ()) (fun _ -> True) in
    // TODO: Cezar: The idea behind this is to get rid of the `match`  
    // because we did it already in the proof.
    // Related github issues: https://github.com/FStarLang/FStar/issues/2169
    assert (l == ll) by (
      unfold_def (`_export_GIO_arrow_spec);
      let xkkk = (match (List.Tot.nth (cur_binders ()) 12) with
      | Some y -> y | None -> fail "asdf") in
      // l_to_r [`xkkk];
      tadmit ()//;
      // dump "h"
    );
    assert (behavior l `included_in_id` behavior ll);

    calc (included_in_id) {
        behavior ll;
        `included_in_id` {}
        behavior (reify (
            (export (MFOUR?.reflect (ref (iost_to_io (reify (f x) (gio_post pi []) []))) <: MFOUR t2 (fun p -> forall res. p res)) <: d2.etype)) (fun _ -> True));
        // TODO: Cezar: this should be just an unfolding of `reify`. I talked with Guido
        // and it seems using tactics is not a solution to unfold `reify` for 
        // layered effects because: "reification of layered effects is explicitly disabled
        // since it requires producing the indices for the bind, and we do not store them
        // anywhere". I tried to manually unfold looking at EMF* (Dijkstra Monads for
        // Free), but it seems that F* does not accept this proof. I created a new file only
        // for this problem: `UnfoldReify.fst`.
        // Related github issue: https://github.com/FStarLang/FStar/issues/2163
        `included_in_id` { admit () }
        // TODO: Cezar: is the 3rd argument correct? I suppose it should use pre and post
        behavior (M4.ibind t2 d2.etype (fun p -> forall res. p res) (fun x -> m4_return_wp (d2.etype) (export x))
            (reify (MFOUR?.reflect (ref (iost_to_io (reify (f x) (gio_post pi []) []))) <: MFOUR t2 (fun p -> forall res. p res)))
            (fun x -> lift_pure_mfour d2.etype (fun p -> p (export x)) (fun _ -> export x)) (fun _ -> True));
    };

    beh_included_bind_tot #t2 #d2.etype
        (reify (MFOUR?.reflect (ref (iost_to_io (reify (f x) (gio_post pi []) []))) <: MFOUR t2 (fun p -> forall res. p res)) (compute_post t2 (Mkexportable?.etype d2) (fun x -> m4_return_wp (Mkexportable?.etype d2) (export x)) (fun _ -> True)))
        export;

    assert (
        (behavior (M4.ibind t2 d2.etype (fun p -> forall res. p res) (fun x -> m4_return_wp (d2.etype) (export x))
            (reify (MFOUR?.reflect (ref (iost_to_io (reify (f x) (gio_post pi []) []))) <: MFOUR t2 (fun p -> forall res. p res)))
            (fun x -> lift_pure_mfour d2.etype (fun p -> p (export x)) (fun _ -> export x)) (fun _ -> True)))
        `included_in (inl_app export)`
        (behavior (reify (MFOUR?.reflect (ref (iost_to_io (reify (f x) (gio_post pi []) []))) <: MFOUR t2 (fun p -> forall res. p res)) (fun _ -> True)))
    ) by (unfold_def (`ibind));

    calc (included_in_id) {
        behavior (reify (MFOUR?.reflect (ref (iost_to_io (reify (f x) (gio_post pi []) []))) <: MFOUR t2 (fun p -> forall res. p res)) (fun _ -> True));
        `included_in_id` {}
        behavior (iost_to_io (reify (f x) (gio_post pi []) []));
    };

    beh_iost_to_io t2 (reify (f x) (gio_post pi []) []);

    assert (
        behavior (iost_to_io (reify (f x) (gio_post pi []) []))
        `included_in (inl_app cdr)` 
        beh_s pi f x)
  end
  | None -> begin
    calc (==) {
        reify (ef x') (fun _ -> True);
        == {}
        reify ((_export_GIO_arrow_spec pi f <: (d1.itype -> M4 d2.etype)) x') (fun _ -> True);
        // TODO: Cezar: two admits here.
        == { 
          _ by (unfold_def(`_export_IOStHist_arrow_spec); norm [iota]; tadmit ()) }
        reify (M4.raise Contract_failure) (fun _ -> True);
        == { admit () }
        Throw Contract_failure;
    }
  end

let export_whole_lemma 
  #t1 {| d1:importable t1 |} 
  #t2 {| d2:exportable t2 |}
  (pi:check_type)
  (f:(x:t1 -> M4wp t2 pi (fun _ _ _ -> True))) : 
  Lemma (forall (x':d1.itype). (
    let ef : d1.itype -> M4 d2.etype = export f in
    match import x' with
    | Some x -> (
        beh_t ef x' `included_in (inl_app (compose export cdr))` beh_s pi f x)
    | None ->  beh_t ef x' `included_in id` empty_set ())) =
  admit ();
  Classical.forall_intro (_export_whole_lemma pi f)

let beh_export_unit_whole_lemma
  #t2 {| d2:exportable t2 |}
  (pi:check_type)
  (f:(unit -> M4wp t2 pi (fun _ _ _ -> True))) : 
  Lemma (
    let ef : unit -> M4 d2.etype = _export_GIO_arrow_spec pi f in
    beh_t ef () `included_in (inl_app (compose export cdr))` beh_s pi f ()) =
  _export_whole_lemma pi f ()

val import_ctx_t : (#i:interface) -> (#pi:check_type) -> ctx_t i -> ctx_s i pi
let import_ctx_t #i #pi ct =
  ctx_p_to_ctx_s i pi (
    ctx_t_to_ctx_p i pi ct)

let beh_export_ps_ct_in_export_ws
  (i  : interface)
  (pi : check_type)
  (ps : prog_s i pi)
  (cp : ctx_p i pi) : 
  Lemma (
    let (cs : ctx_s i pi) = ctx_p_to_ctx_s i pi cp in
    let ws : whole_s i pi = fun _ -> ps cs in
    let pt : prog_t i pi = export_prog_s i pi ps in
    let wt : whole_t i = _export_GIO_arrow_spec pi ws in
    beh_t pt cp `included_in id` beh_t wt ()
  ) = 
  let (cs : ctx_s i pi) = ctx_p_to_ctx_s i pi cp in
  let ws : whole_s i pi = fun _ -> ps cs in
  let pt : prog_t i pi = export_prog_s i pi ps in
  let wt : whole_t i = _export_GIO_arrow_spec pi ws in
  
  let included_in_id #a = included_in #a #a (id #a) in
  // assert (import () == Some ());
  // TODO: apply l_to_r for: import () == Some ()
  //       apply l_to_r for: import_ctx_t ct == Some b
  //       Qed.
  // Related github issue: https://github.com/FStarLang/FStar/issues/2169
  assert (reify (pt cp) (fun _ -> True) == reify (wt ()) (fun _ -> True)) by (
    unfold_def (`export_prog_s);
    unfold_def (`_export_GIO_arrow_spec)
    // dump "x"
    // tadmit ()
  )

let seci_rsp_0
  (i   : seci.interface)
  (pi  : seci.monitorable_prop)
  (ps  : seci.prog_s i pi)
  (ct  : seci.ctx_t i) :
  Lemma (
  (forall (cs:seci.ctx_s i pi). 
    (seci.beh_s #i #pi (cs `seci.link_s #i #pi` ps)) `seci.included_in_s #i` (seci.safety_prop pi))
  ==>  (
      let pt = seci.compile_prog #i ps in
      seci.beh_t #i (ct `seci.link_t #i #pi` pt) `seci.included_in_t #i` (seci.safety_prop pi))) =
  admit ();
  let (cp:ctx_p i pi) = ctx_t_to_ctx_p i pi ct in
  let (cs:seci.ctx_s i pi) = ctx_p_to_ctx_s i pi cp in
  let ws : seci.whole_s i pi = seci.link_s #i #pi cs ps in
  assert (seci.beh_s #i #pi ws `seci.included_in_s #i` (seci.safety_prop pi));
  beh_export_unit_whole_lemma #i.c #i.cd pi ws; // Beh (export ws ()) in Beh (ws ())
  beh_export_ps_ct_in_export_ws i pi ps cp // Beh ((export ps) ct) in Beh (export ws ())

let seci_rsp
  (i  : seci.interface)
  (pi : seci.monitorable_prop)
  (ps : seci.prog_s i pi) :
  Lemma (rsp seci i pi ps) =
    Classical.forall_intro (seci_rsp_0 i pi ps)
  

// let rsp_premise
//   (i:interface)
//   (pi : check_type)
//   (ps : prog_s i pi)
//   (ct : ctx_t i) :
//   Lemma (
//     let (cs : ctx_s i pi) = import_ctx_t ct in
//     beh_s pi ps cs `included_in id` (pi_to_set pi)) =
//   let (cs : ctx_s i pi) = import_ctx_t ct in
//   beh_gio_in_pi (ctx_s i pi) i.c pi ps cs
    
// let rsp_conclusion 
//   (i  : interface)
//   (pi : check_type)
//   (ps : prog_s pi i)
//   (ct : ctx_t i) :
//   Lemma (
//     let pt : prog_t i = export_prog_s i pi ps in
//     beh_t pt ct `included_in #_ #(maybe (events_trace * i.c)) (inl_app (compose export cdr))` (pi_to_set pi)) = 
//   let Some (cs : ctx_s pi i) = import_ctx_t ct in
//   let ws : whole_s pi i = fun _ -> ps cs in
//   beh_gio_in_pi unit i.c pi ws (); // Beh (ws ()) in pi
//   beh_export_unit_GIO_lemma #i.c #i.cd pi ws; // Beh (export ws ()) in Beh (ws ())
//   beh_export_ps_ct_in_export_ws i pi ps ct // Beh ((export ps) ct) in Beh (export ws ())

// let rsp_variant
//   (i  : interface)
//   (pi : check_type)
//   (ps : prog_s pi i)
//   (ct : ctx_t i) :
//   Lemma(
//     (forall (cs:(ctx_s pi i)). beh_s pi ps cs `included_in id` (pi_to_set pi)) 
//     ==> 
//     (let pt : prog_t i = export_prog_s i pi ps in
//      beh_t pt ct `included_in #_ #(maybe (events_trace * i.c)) (inl_app (compose export cdr))` (pi_to_set pi))) = 
//   rsp_conclusion i pi ps ct


// let si = secure_interop
 
// let rsp_lemma
//   (pi : check_type)
//   (i  : (si pi).source.interface)
//   (ps : (si pi).source.prog i) :
//   Lemma (forall pi_set. rsp (secure_interop pi) i ps pi_set) =
//     Classical.forall_intro_2 (rsp_simple_linking'' pi i ps)
  
// let tp_lemma
//   (pi : check_type)
//   (i : (si pi).source.interface)
//   (ws : (si pi).source.whole i) : 
//   Lemma (forall pi_set. tp (si pi) (i) (ws) pi_set)  = 
//   beh_export_unit_GIO_lemma #i.c #i.cd pi ws

// let secure_linker_respects_rsp () : 
//   Lemma (forall pi i ps pi_set. rsp (secure_interop pi) i ps pi_set)
//   by (
//     unfold_def(`rsp);
//     explode ();
//     rewrite_lemma 2 3;
//     norm [iota]
//   ) =
//   Classical.forall_intro_3 (rsp_lemma)
  
// let secure_linker_respects_tp () :
//   Lemma (forall pi i ws pi_set. tp (si pi) i ws pi_set) = 
//     Classical.forall_intro_3 tp_lemma
