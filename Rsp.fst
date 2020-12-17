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
  
noeq type interface = {
  a : Type; ad : exportable a;
  b : Type; bdi : importable b; bde : exportable b;         // b has to be importable and exportable
  c : Type; cd : exportable c;
  post:a -> trace -> (m:maybe b) -> trace -> (r:Type0{Inr? m ==> r});
  cpost : checkable4 post;
}

let safety_prop = (#a:Type) -> a -> Type0
// let safety_prop = pi_to_set

type whole_s (i:interface) (pi:monitorable_prop) = unit -> IIO i.c pi (fun _ -> True) (fun _ _ _ -> True)
type whole_t (i:interface) = unit -> MIIO i.cd.etype

(** the lift from "MIO to MIIO" for the context should happen
during linking. It is improper to say "should happen", because
the lift represents the assumptions: "the context uses
only the IO library which comes with instrumentation".
 **)
type ctx_s (i:interface) (pi:monitorable_prop) = (x:i.a) -> IIO i.b pi (fun _ -> True) (i.post x)
type ctx_p (i:interface) (pi:monitorable_prop) = i.ad.etype -> IIO i.bdi.itype pi (fun _ -> True) (fun _ _ _ -> True)
type ctx_t (i:interface) = i.ad.etype -> MIO i.bdi.itype

type prog_s (i:interface) (pi:monitorable_prop) = ctx_s i pi -> IIO i.c pi (fun _ -> True) (fun _ _ _ -> True)
type prog_t (i:interface) (pi:monitorable_prop) = ctx_p i pi -> MIIO i.cd.etype

let rec handle #t2 (tree : iio (t2)) (pi:monitorable_prop) : IIO t2 pi (fun _ -> True) (fun _ _ _ -> True) = begin
  match tree with
  | Return r -> r 
  | Throw r -> IIO.Effect.throw r
  | Cont (Call GetTrace argz fnc) ->
      let h = IIO.Effect.get_trace () in
      FStar.WellFounded.axiom1 fnc (Inl h);
      let z' = fnc (Inl h) in
      handle z' pi
  | Cont (Call cmd argz fnc) ->
      let rez : res cmd = IIO.Effect.dynamic_cmd pi cmd argz in
      FStar.WellFounded.axiom1 fnc (Inl rez);
      let z' : iio t2 = fnc (Inl rez) in
      rev_append_rev_append ();
      handle z' pi
end

let ctx_t_to_ctx_p
  (i  : interface)
  (pi : monitorable_prop)
  (ct : ctx_t i) :
  Tot (ctx_p i pi) =
  fun (x:i.ad.etype) -> 
    let h = get_trace () in
    // Cezar: I don't think post unfolded like that is ok.
    handle (cast_io_iio (reify (ct x) h (fun _ _ -> True))) pi

let ctx_p_to_ctx_s
  (i  : interface)
  (pi : monitorable_prop)
  (cp  : ctx_p i pi) : 
  Tot (ctx_s i pi) =
  admit ();
  fun (x:i.a) -> 
    let h : trace = get_trace () in
    let f = _import_pre_pi_IIO pi (fun _ _ -> true) cp in 
    let r : i.b = f x in
    let lt : trace = extract_local_trace h in
    if (check4 #i.a #trace #(maybe i.b) #trace #i.post #i.cpost x h (Inl r) lt) then r
    else IIO.Effect.throw Contract_failure

unfold 
let beh_s 
  #a
  #b
  (pi:monitorable_prop) 
  (ws:(x:a -> M4wp b pi (fun _ _ _ -> True))) 
  (x:a) =
  behavior (reify (ws x) (m4wp_invariant_post pi []) [])

unfold
let beh_t #a #b (wt:a -> M4 b) (x:a) =
  behavior (reify (wt x) (fun _ -> True))

let compile_prog
  (#i  : interface)
  (#pi : monitorable_prop)
  (f  : prog_s i pi) : 
  Tot (prog_t i pi) =
    (fun (ct:ctx_p i pi) ->
      let cs = ctx_p_to_ctx_s i pi ct in
      let tree : io (trace * i.c) = reify (f cs) (m4wp_invariant_post pi []) [] in
      export (M4?.reflect (fun _ -> iost_to_io tree) <: MFOUR i.c (fun p -> forall res. p res)))

let compile_whole 
  (#i  : interface)
  (#pi : monitorable_prop)
  (f  : whole_s i pi) : 
  Tot (whole_t i) =
    (fun _ ->
      let tree : io (trace * i.c) = reify (f ()) (m4wp_invariant_post pi []) [] in
      export (M4?.reflect (fun _ -> iost_to_io tree) <: MFOUR i.c (fun p -> forall res. p res)))
 
val link_s  : (#i:interface) -> (#pi:monitorable_prop) -> ctx_s i pi -> prog_s i pi -> Tot (whole_s i pi)
let link_s = (fun #i #pi c p -> (fun _ -> p c))

val link_t  : (#i:interface) -> (#pi:monitorable_prop) -> ctx_t i -> prog_t i pi -> Tot (whole_t i)
let link_t #i #pi c p : whole_t i = (fun _ -> p (ctx_t_to_ctx_p i pi c))
  
let res_s   = (fun i -> maybe (trace * i.c))
let res_t   = (fun i -> maybe (i.cd.etype))
  
val included_in_s : (#i:interface) -> set_of_traces (res_s i) -> set_of_traces (res_s i) -> Type0
let included_in_s = (fun (#i:interface) -> included_in #(res_s i) #(res_s i) id)
let included_in_t = (fun (#i:interface) -> included_in #(maybe i.cd.etype) #(maybe (trace * i.c)) (inl_app (compose export cdr)))

let tp (i:interface) (pi:monitorable_prop) (ws:whole_s i pi) : Type0 =
  ((beh_s pi ws () `included_in_s` (safety_prop pi)) ==>  
    (beh_t (compile_whole ws) () `included_in_t` (safety_prop pi)))
  
let seci_respects_tp
  (i  : interface)
  (pi : monitorable_prop) 
  (ws  : whole_s i pi) :
  Lemma (tp i pi ws) = 

  let wt : whole_t i = compile_whole ws in
  let included_in_id #a = included_in #a #a (id #a) in
  let l1 = reify (wt ()) (fun _ -> True) in

  let l2 = reify (
          (export (M4?.reflect (ref (iost_to_io (reify (ws ()) (m4wp_invariant_post pi []) []))) <: MFOUR i.c (fun p -> forall res. p res)) <: i.cd.etype)) (fun _ -> True) in 

  let l3s = reify (M4?.reflect (ref (iost_to_io (reify (ws ()) (m4wp_invariant_post pi []) []))) <: MFOUR i.c (fun p -> forall res. p res)) in
  // TODO: Cezar: is the 3rd argument correct? I suppose it should use pre and post
  // behavior (M4.ibind i.c i.cd.etype (fun p -> forall res. p res) (fun x -> m4_return_wp (i.cd.etype) (export x))
  let l3 = (M4.ibind i.c i.cd.etype (fun p -> forall res. p res) (fun x -> m4_return_wp (i.cd.etype) (export x))
          (l3s)
          (fun x -> lift_pure_mfour i.cd.etype (fun p -> p (export x)) (fun _ -> export x)) (fun _ -> True)) in

  assert (l1 == l2) by (norm [delta_only [`%compile_whole]]);
  assert (behavior l1 `included_in id` behavior l2);
  // TODO: Cezar: this should be just an unfolding of `reify`. I talked with Guido
  // and it seems using tactics is not a solution to unfold `reify` for 
  // layered effects because: "reification of layered effects is explicitly disabled
  // since it requires producing the indices for the bind, and we do not store them
  // anywhere". I tried to manually unfold looking at EMF* (Dijkstra Monads for
  // Free), but it seems that F* does not accept this proof. I created a new file only
  // for this problem: `UnfoldReify.fst`.
  // Related github issue: https://github.com/FStarLang/FStar/issues/2163
  assume (behavior l2 `included_in id` behavior l3);

  beh_included_bind_tot #i.c #i.cd.etype
      (l3s (compute_post i.c (Mkexportable?.etype i.cd) (fun x -> m4_return_wp (Mkexportable?.etype i.cd) (export x)) (fun _ -> True)))
      export;

  assert (
      behavior l3
      `included_in (inl_app export)`
      behavior (l3s (fun _ -> True))
  ) by (norm [delta_only [`%ibind]]);

  assert (
      behavior (l3s (fun _ -> True))
      `included_in id`
      behavior (iost_to_io (reify (ws ()) (m4wp_invariant_post pi []) []))
  );

  beh_iost_to_io i.c (reify (ws ()) (m4wp_invariant_post pi []) []);

  assert (
      behavior (iost_to_io (reify (ws ()) (m4wp_invariant_post pi []) []))
      `included_in (inl_app cdr)` 
      beh_s pi ws ())

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
    beh_t (ct `link_t` pt) () `included_in id` beh_t wt ()
  ) = 
  let cp = ctx_t_to_ctx_p i pi ct in
  let (cs : ctx_s i pi) = ctx_p_to_ctx_s i pi cp in
  let ws : whole_s i pi = cs `link_s` ps in
  let (cs : ctx_s i pi) = ctx_p_to_ctx_s i pi cp in
  let pt : prog_t i pi = compile_prog ps in
  let wt : whole_t i = compile_whole ws in
  assert (reify (pt cp) (fun _ -> True) == reify (wt ()) (fun _ -> True)) by (
    norm [delta_only [`%compile_prog]];
    norm [delta_only [`%compile_whole]];
    norm [delta_only [`%link_s]]
  );
  assert (
    beh_t (ct `link_t #i #pi` pt) ()
      `included_in id`
    beh_t ((fun _ -> pt cp) <: whole_t i) ()) 
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
