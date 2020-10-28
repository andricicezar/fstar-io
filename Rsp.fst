module Rsp

open FStar.Calc
open FStar.Tactics

open Common

open IO.Behavior
open IOStHist
open M4
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
  a : Type;  ad : exportable a;
  b : Type;  bd : ml b;         // b has to be importable and exportable
  c : Type;  cd : exportable c;
  post : a -> events_trace -> maybe (events_trace * b) -> events_trace -> Type; 
  cpost : checkable4 post;
}

let monitorable_prop = check_type
let safety_prop = pi_to_set

type whole_s (i:interface) (pi:monitorable_prop) = unit -> M4wp i.c pi (fun _ _ _ -> True)
type whole_t (i:interface) = unit -> M4 i.cd.etype

type ctx_s (i:interface) (pi:monitorable_prop) = (x:i.a) -> M4wp i.b pi (i.post x)
type ctx_p (i:interface) (pi:monitorable_prop) = i.ad.etype -> M4wp i.b pi (fun _ _ _ -> True)
type ctx_t (i:interface) = i.ad.etype -> M4 i.b

type prog_s (i:interface) (pi:monitorable_prop) = ctx_s i pi -> M4wp i.c pi (fun _ _ _ -> True)
type prog_t (i:interface) (pi:monitorable_prop) = ctx_p i pi -> M4 i.cd.etype

unfold 
let beh_s 
  #a
  #b
  (pi:monitorable_prop) 
  (ws:(x:a -> M4wp b pi (fun _ _ _ -> True))) 
  (x:a) =
  behavior (reify (ws x) (gio_post pi []) [])

unfold
let beh_t #a #b (wt:a -> M4 b) (x:a) =
  behavior (reify (wt x) (fun _ -> True))

let rec handle #t2 (tree : io (t2)) (pi:monitorable_prop) : M4wp t2 pi (fun _ _ _ -> True) = begin
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
  (pi : monitorable_prop)
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
  (pi : monitorable_prop)
  (ct : ctx_t i) :
  Tot (ctx_p i pi) =
  fun (x:i.ad.etype) -> handle (reify (ct x) (fun _ -> True)) pi

let compile_prog
  (#i  : interface)
  (#pi : monitorable_prop)
  (f  : prog_s i pi) : 
  Tot (prog_t i pi) =
    (fun (ct:ctx_p i pi) ->
      let cs = ctx_p_to_ctx_s i pi ct in
      let tree : io (events_trace * i.c) = reify (f cs) (gio_post pi []) [] in
      export (M4?.reflect (fun _ -> iost_to_io tree) <: MFOUR i.c (fun p -> forall res. p res)))

let compile_whole 
  (#i  : interface)
  (#pi : monitorable_prop)
  (f  : whole_s i pi) : 
  Tot (whole_t i) =
    (fun _ ->
      let tree : io (events_trace * i.c) = reify (f ()) (gio_post pi []) [] in
      export (M4?.reflect (fun _ -> iost_to_io tree) <: MFOUR i.c (fun p -> forall res. p res)))
 
val link_s  : (#i:interface) -> (#pi:check_type) -> ctx_s i pi -> prog_s i pi -> Tot (whole_s i pi)
let link_s = (fun #i #pi c p -> (fun _ -> p c))

val link_t  : (#i:interface) -> (#pi:check_type) -> ctx_t i -> prog_t i pi -> Tot (whole_t i)
let link_t #i #pi c p : whole_t i = (fun _ -> p (ctx_t_to_ctx_p i pi c))
  
let res_s   = (fun i -> maybe (events_trace * i.c))
let res_t   = (fun i -> maybe (i.cd.etype))
  
val included_in_s : (#i:interface) -> set_of_traces (res_s i) -> set_of_traces (res_s i) -> Type0
let included_in_s = (fun (#i:interface) -> included_in #(res_s i) #(res_s i) id)
let included_in_t = (fun (#i:interface) -> included_in #(maybe i.cd.etype) #(maybe (events_trace * i.c)) (inl_app (compose export cdr)))

let seci : compiler = {
  interface = interface;
  monitorable_prop = check_type;
  safety_prop = pi_to_set;

  set_of_traces = set_of_traces;

  res_s   = (fun i -> maybe (events_trace * i.c));
  prog_s  = prog_s;
  ctx_s   = ctx_s;
  whole_s = whole_s;
  
  link_s = link_s;

  res_t   = (fun i -> maybe (i.cd.etype));
  prog_t  = prog_t;
  ctx_t   = ctx_t;
  whole_t = whole_t;
  link_t = link_t;

  beh_s = (fun #i #pi w -> beh_s #unit #i.c pi w ());
  beh_t = (fun #i w -> beh_t #unit #i.cd.etype w ());
  
  included_in_s = included_in_s;
  included_in_t = included_in_t;

  compile_prog  = compile_prog;
  compile_whole = compile_whole;
}


let beh_export_whole
  (i  : interface)
  (pi : check_type) 
  (f  : whole_s i pi) :
  Lemma (
    let ef : whole_t i = compile_whole f in
    beh_t ef () `included_in (inl_app (compose export cdr))` beh_s pi f ()) =

  let ef : whole_t i = compile_whole f in
  let included_in_id #a = included_in #a #a (id #a) in
  let l1 = reify (ef ()) (fun _ -> True) in

  let l2 = reify (
          (export (M4?.reflect (ref (iost_to_io (reify (f ()) (gio_post pi []) []))) <: MFOUR i.c (fun p -> forall res. p res)) <: i.cd.etype)) (fun _ -> True) in 

  let l3s = reify (M4?.reflect (ref (iost_to_io (reify (f ()) (gio_post pi []) []))) <: MFOUR i.c (fun p -> forall res. p res)) in
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
  // `included_in_id` { admit () }
  // TODO: Cezar: is the 3rd argument correct? I suppose it should use pre and post
  // behavior (M4.ibind i.c i.cd.etype (fun p -> forall res. p res) (fun x -> m4_return_wp (i.cd.etype) (export x))
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
      behavior (iost_to_io (reify (f ()) (gio_post pi []) []))
  );

  beh_iost_to_io i.c (reify (f ()) (gio_post pi []) []);

  assert (
      behavior (iost_to_io (reify (f ()) (gio_post pi []) []))
      `included_in (inl_app cdr)` 
      beh_s pi f ())

val import_ctx_t : (#i:interface) -> (#pi:check_type) -> ctx_t i -> ctx_s i pi
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
  beh_export_whole i pi ws; // Beh (export ws ()) in Beh (ws ())
  beh_export_ps_ct_in_export_ws i pi ps ct // Beh ((export ps) ct) in Beh (export ws ())

let rsp (i:interface) (pi:monitorable_prop) (ps:prog_s i pi) : Type0 =
  (forall cs. beh_s pi (cs `link_s` ps) () `included_in_s` (safety_prop (pi)))
  ==> (forall (ct: ctx_t i). (
      let pt = compile_prog ps in
      beh_t (ct `link_t` pt) () `included_in_t` (safety_prop (pi))))

let seci_respects_rsp () :
  Lemma (forall i pi ps. rsp i pi ps) =
    Classical.forall_intro_4 (seci_rsp_0)
  
let tp (i:interface) (pi:monitorable_prop) (ws:whole_s i pi) : Type0 =
    ((beh_s pi ws () `included_in_s` (safety_prop pi)) ==>  
      (beh_t (compile_whole ws) () `included_in_t` (safety_prop pi)))
  
let seci_respects_tp () :
  Lemma (forall pi i ws. tp i pi ws) = 
    Classical.forall_intro_3 beh_export_whole
