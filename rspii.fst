module Rspii

open FStar.Calc
open FStar.Tactics

open Common
open IOStHist
open M4
open Minterop
open IO.Behavior

noeq type language = {
  interface : Type;

  res : interface -> Type;
  
  prog: interface -> Type;
  ctx : interface -> Type;
  whole : interface -> Type;

  link : (i:interface) -> ctx i -> prog i -> whole i;
}

noeq type compiler = {
  source : language;
  target : language;

  set_of_traces : Type -> Type;
  beh_s : (i:source.interface) -> source.whole i -> set_of_traces (source.res i);
  beh_t : (i:target.interface) -> target.whole i -> set_of_traces (target.res i);

  cint : source.interface -> target.interface;
  
  included_in_s : (i:source.interface) -> set_of_traces (source.res i) -> set_of_traces (source.res i) -> Type;
  included_in_t : (i:source.interface) -> set_of_traces (target.res (cint i)) -> set_of_traces (source.res i) -> Type;

  compile_prog : i:source.interface -> source.prog i -> target.prog (cint i);
  compile_whole : i:source.interface -> source.whole i -> target.whole (cint i);
}
  
let rsp (op:compiler) : Type0 =
  forall (i:op.source.interface) (ps:op.source.prog i) (pi:op.set_of_traces (op.source.res i)). (
    (forall cs. op.beh_s i (cs `op.source.link i` ps) `op.included_in_s i` pi)
    ==> (forall (ct: op.target.ctx (op.cint i)). (
        let pt = op.compile_prog i ps in
        op.beh_t (op.cint i) (ct `op.target.link (op.cint i)` pt) `op.included_in_t i` pi)))

noeq type interface = {
  a : Type;  ad : exportable a;
  b : Type;  bd : ml b;         // b has to be importable and exportable
  c : Type;  cd : exportable c;
}

type whole_s (pi:check_type) (i:interface) = unit -> GIO i.c pi
type whole_t (i:interface) = unit -> M4 i.cd.etype

type ctx_s (pi:check_type) (i:interface) = i.a -> GIO i.b pi
type ctx_t (i:interface) = i.ad.etype -> M4 i.b

type prog_s (pi:check_type) (i:interface) = ctx_s pi i -> GIO i.c pi
type prog_t (i:interface) = ctx_t i -> M4 i.cd.etype

unfold 
let beh_s #a #b (pi:check_type) (ws:a -> GIO b pi) (x:a) =
  behavior (reify (ws x) (gio_post pi []) [])

unfold
let beh_t #a #b (wt:a -> M4 b) (x:a) =
  behavior (reify (wt x) (fun _ -> True))

val import_ctx_t : (#pi:check_type) -> (#i:interface) -> ctx_t i -> option (ctx_s pi i)
let import_ctx_t #pi #i f =
  let f' : (ctx_s pi i) = (
    fun (x:i.a) ->
      let x : i.ad.etype = export x in
      let tree = reify (f x) (fun r -> True) in
      _import_M4_to_GIO #i.b tree pi <: GIO i.b pi) in 
  Some f'

let export_prog_s
  (i  : interface)
  (pi : check_type)
  (f  : prog_s pi i) : 
  Tot (prog_t i) =
    (fun (ct:ctx_t i) ->
      let Some (cs : ctx_s pi i) = import_ctx_t ct in
      let tree : io (events_trace * i.c) = reify (f cs) (gio_post pi []) [] in
      export (M4wp?.reflect (fun _ -> iost_to_io tree) <: M4wp i.c (fun p -> forall res. p res)))

let secure_interop (pi:check_type) : compiler = {
  source = {
    interface = interface;
    res   = (fun i -> maybe (events_trace * i.c));
    prog  = (fun i -> prog_s pi i);
    ctx   = (fun i -> ctx_s pi i);
    whole = (fun i -> whole_s pi i);
  
    link = (fun i c p -> (fun _ -> p c) <: whole_s pi i);
  };

  target = {
    interface = interface;
    res   = (fun i -> maybe (i.cd.etype));
    prog  = (fun i -> prog_t i);
    ctx   = (fun i -> ctx_t i);
    whole = (fun i -> whole_t i);
  
    link = (fun i c p -> (fun _ -> p c) <: whole_t i);
  };

  cint = (fun i -> i);
  
  set_of_traces = set_of_traces;

  beh_s = (fun i w -> beh_s #unit #i.c pi w ());
  beh_t = (fun i w -> beh_t #unit #i.cd.etype w ());
  
  included_in_s = (fun i -> included_in id);
  included_in_t = (fun i -> included_in #(maybe i.cd.etype) #(maybe (events_trace * i.c)) (inl_app (compose export cdr)));
  
  compile_prog  = (fun i -> export_prog_s i pi);
  compile_whole = (fun i -> _export_GIO_arrow_spec pi);
}

let _export_GIO_lemma
  #t1 {| d1:importable t1 |} 
  #t2 {| d2:exportable t2 |}
  (pi : check_type) 
  (f:(x:t1 -> GIO t2 pi)) 
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
    let l : io (d2.etype) = reify (ef x') (fun _ -> True) in
    let ll : io (d2.etype) = reify (
            let tree : io (events_trace * t2) = reify (f x) (gio_post pi []) [] in
            export (M4wp?.reflect (fun _ -> iost_to_io tree) <: M4wp t2 (fun p -> forall res. p res))
        ) (fun _ -> True) in
    // TODO: Cezar: The idea behind this is to get rid of the `match`  
    // because we did it already in the proof.
    assert (l == ll) by (
      unfold_def (`_export_GIO_arrow_spec);
      let xkkk = (match (List.Tot.nth (cur_binders ()) 12) with
      | Some y -> y | None -> fail "asdf") in
      // l_to_r [`xkkk];
      tadmit ();
      dump "h");
    assert (behavior l `included_in_id` behavior ll);

    calc (included_in_id) {
        behavior ll;
        `included_in_id` {}
        behavior (reify (
            (export (M4wp?.reflect (ref (iost_to_io (reify (f x) (gio_post pi []) []))) <: M4wp t2 (fun p -> forall res. p res)) <: d2.etype)) (fun _ -> True));
        // TODO: Cezar: this should be just an unfolding of `reify`. I talked with Guido
        // and it seems using tactics is not a solution to unfold `reify` for 
        // layered effects because: "reification of layered effects is explicitly disabled
        // since it requires producing the indices for the bind, and we do not store them
        // anywhere". I tried to manually unfold looking at EMF* (Dijkstra Monads for
        // Free), but it seems that F* does not accept this proof. I created a new file only
        // for this problem: `UnfoldReify.fst`.
        `included_in_id` { admit () }
        // TODO: Cezar: is the 3rd argument correct? I suppose it should use pre and post
        behavior (M4.ibind t2 d2.etype (fun p -> forall res. p res) (fun x -> m4_return_wp (d2.etype) (export x))
            (reify (M4wp?.reflect (ref (iost_to_io (reify (f x) (gio_post pi []) []))) <: M4wp t2 (fun p -> forall res. p res)))
            (fun x -> lift_pure_m4wp d2.etype (fun p -> p (export x)) (fun _ -> export x)) (fun _ -> True));
    };

    beh_included_bind_tot #t2 #d2.etype
        (reify (M4wp?.reflect (ref (iost_to_io (reify (f x) (gio_post pi []) []))) <: M4wp t2 (fun p -> forall res. p res)) (compute_post t2 (Mkexportable?.etype d2) (fun x -> m4_return_wp (Mkexportable?.etype d2) (export x)) (fun _ -> True)))
        export;

    assert (
        (behavior (M4.ibind t2 d2.etype (fun p -> forall res. p res) (fun x -> m4_return_wp (d2.etype) (export x))
            (reify (M4wp?.reflect (ref (iost_to_io (reify (f x) (gio_post pi []) []))) <: M4wp t2 (fun p -> forall res. p res)))
            (fun x -> lift_pure_m4wp d2.etype (fun p -> p (export x)) (fun _ -> export x)) (fun _ -> True)))
        `included_in (inl_app export)`
        (behavior (reify (M4wp?.reflect (ref (iost_to_io (reify (f x) (gio_post pi []) []))) <: M4wp t2 (fun p -> forall res. p res)) (fun _ -> True)))
    ) by (unfold_def (`ibind));

    calc (included_in_id) {
        behavior (reify (M4wp?.reflect (ref (iost_to_io (reify (f x) (gio_post pi []) []))) <: M4wp t2 (fun p -> forall res. p res)) (fun _ -> True));
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

let export_GIO_lemma 
  #t1 {| d1:importable t1 |} 
  #t2 {| d2:exportable t2 |}
  (pi:check_type)
  (f:(x:t1 -> GIO t2 pi)) : 
  Lemma (forall (x':d1.itype). (
    let ef : d1.itype -> M4 d2.etype = export f in
    match import x' with
    | Some x -> (
      (check2 #t1 #events_trace #(fun _ -> gio_pre pi) x [] ==>  
        beh_t ef x' `included_in (inl_app (compose export cdr))` beh_s pi f x) /\
      (~(check2 #t1 #events_trace #(fun _ -> gio_pre pi) x []) ==>  
        beh_t ef x' `included_in id` empty_set ()))
    | None ->  beh_t ef x' `included_in id` empty_set ())) =
  Classical.forall_intro (_export_GIO_lemma pi f)

let beh_export_unit_GIO_lemma
  #t2 {| d2:exportable t2 |}
  (pi:check_type)
  (f:(unit -> GIO t2 pi)) : 
  Lemma (
    let ef : unit -> M4 d2.etype = _export_GIO_arrow_spec pi f in
    (check2 #unit #events_trace #(fun _ -> gio_pre pi) () [] ==>  
      beh_t ef () `included_in (inl_app (compose export cdr))` beh_s pi f ()) /\
    (~(check2 #unit #events_trace #(fun _ -> gio_pre pi) () []) ==>  
      beh_t ef () `included_in id` empty_set ())) =
  _export_GIO_lemma pi f ()

  
let rsp_premise
  (i:interface)
  (pi : check_type)
  (ps : prog_s pi i)
  (ct : ctx_t i) :
  Lemma (
    let Some (cs : ctx_s pi i) = import_ctx_t ct in
    beh_s pi ps cs `included_in id` (pi_to_set pi)) =
  let Some (cs : ctx_s pi i) = import_ctx_t ct in
  beh_gio_in_pi (ctx_s pi i) i.c pi ps cs

let beh_export_ps_ct_in_export_ws
  (i  : interface)
  (pi : check_type)
  (ps : prog_s pi i)
  (ct : ctx_t i) : 
  Lemma (
    let Some (cs : ctx_s pi i) = import_ctx_t ct in
    let ws : unit -> GIO i.c pi = fun _ -> ps cs in
    let pt : (ctx_t i) -> M4 i.cd.etype = export_prog_s i pi ps in
    let wt : unit -> M4 i.cd.etype = _export_GIO_arrow_spec pi ws in
    beh_t pt ct `included_in id` beh_t wt ()
  ) = 
  let Some (cs : ctx_s pi i) = import_ctx_t ct in
  let ws : whole_s pi i = fun _ -> ps cs in
  let pt : (ctx_t i) -> M4 i.cd.etype = export_prog_s i pi ps in
  let wt : whole_t i = _export_GIO_arrow_spec pi ws in
  
  let included_in_id #a = included_in #a #a (id #a) in
  assert (import () == Some ());
  // TODO: apply l_to_r for: import () == Some ()
  //       apply l_to_r for: import_ctx_t ct == Some b
  //       Qed.
  assert (reify (pt ct) (fun _ -> True) == reify (wt ()) (fun _ -> True)) by (
    unfold_def (`export_prog_s);
    unfold_def (`_export_GIO_arrow_spec);
    // dump "x"
    tadmit ()
  )
    
let rsp_conclusion 
  (i  : interface)
  (pi : check_type)
  (ps : prog_s pi i)
  (ct : ctx_t i) :
  Lemma (
    let pt : prog_t i = export_prog_s i pi ps in
    beh_t pt ct `included_in #_ #(maybe (events_trace * i.c)) (inl_app (compose export cdr))` (pi_to_set pi)) = 
  let Some (cs : ctx_s pi i) = import_ctx_t ct in
  let ws : whole_s pi i = fun _ -> ps cs in
  beh_gio_in_pi unit i.c pi ws (); // Beh (ws ()) in pi
  beh_export_unit_GIO_lemma #i.c #i.cd pi ws; // Beh (export ws ()) in Beh (ws ())
  beh_export_ps_ct_in_export_ws i pi ps ct // Beh ((export ps) ct) in Beh (export ws ())

let rsp_variant
  (i  : interface)
  (pi : check_type)
  (ps : prog_s pi i)
  (ct : ctx_t i) :
  Lemma(
    (forall (cs:(ctx_s pi i)). beh_s pi ps cs `included_in id` (pi_to_set pi)) 
    ==> 
    (let pt : prog_t i = export_prog_s i pi ps in
     beh_t pt ct `included_in #_ #(maybe (events_trace * i.c)) (inl_app (compose export cdr))` (pi_to_set pi))) = 
  rsp_conclusion i pi ps ct

let rsp_simple_linking''
  (i  : interface)
  (pi : check_type)
  (ps : prog_s pi i)
  (pi' : set_of_traces (maybe (events_trace * i.c)))
  (ct:ctx_t i) :
  Lemma (
    (forall (cs:(ctx_s pi i)). beh_s pi ps cs `included_in id` pi') 
    ==>  (
    let pt : prog_t i = export_prog_s i pi ps in
    beh_t pt ct `included_in #_ #(maybe (events_trace * i.c)) (inl_app (compose export cdr))` pi')) = 
  let Some (cs:ctx_s pi i) = import_ctx_t ct in
  let ws : whole_s pi i = fun _ -> ps cs in
  assert (beh_s pi ws () `included_in id` beh_s pi ps cs);
  beh_export_unit_GIO_lemma #i.c #i.cd pi ws; // Beh (export ws ()) in Beh (ws ())
  beh_export_ps_ct_in_export_ws i pi ps ct // Beh ((export ps) ct) in Beh (export ws ())
 
let rsp_simple_linking'
  (pi : check_type)
  (i  : interface)
  (ps : prog_s pi i)
  (pi' : set_of_traces (maybe (events_trace * i.c))) :
  Lemma(
    (forall (cs:(ctx_s pi i)). beh_s pi ps cs `included_in id` pi') 
    ==> 
    (forall (ct:ctx_t i). (
      let pt : prog_t i = export_prog_s i pi ps in
      beh_t pt ct `included_in #(maybe i.cd.etype) #(maybe (events_trace * i.c)) (inl_app (compose export cdr))` pi'))) = 
    Classical.forall_intro (rsp_simple_linking'' i pi ps pi')


let secure_linker_respects_rsp () : 
  Lemma (forall pi. rsp (secure_interop pi)) =
  let aux pi : Lemma (rsp (secure_interop pi)) by (
    unfold_def(`rsp);
    explode ();
    rewrite_lemma 5 6;
    assumption ()) = begin
    Classical.forall_intro_3 (rsp_simple_linking' pi)
  end in Classical.forall_intro (aux)
