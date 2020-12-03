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
  a : Type; // ad : exportable a;
  ad : Type;
  b : Type; // bd : ml b;         // b has to be importable and exportable
  c : Type; // cd : exportable c;
  cd : Type;
  post : a -> trace -> maybe b -> trace -> Type; 
  //cpost : checkable4 post;
}

let safety_prop = (#a:Type) -> a -> Type0
// let safety_prop = pi_to_set

type whole_s (i:interface) (pi:monitorable_prop) = unit -> IIO i.c pi (fun _ _ _ -> True)
type whole_t (i:interface) = unit -> MIIO i.cd

type ctx_s (i:interface) (pi:monitorable_prop) = (x:i.a) -> IIO i.b pi (i.post x)
type ctx_p (i:interface) (pi:monitorable_prop) = i.ad -> IIO i.b pi (fun _ _ _ -> True)
type ctx_t (i:interface) = i.ad -> MIO i.b

type prog_s (i:interface) (pi:monitorable_prop) = ctx_s i pi -> IIO i.c pi (fun _ _ _ -> True)
type prog_t (i:interface) (pi:monitorable_prop) = ctx_p i pi -> MIIO i.cd


let rev_append_rev_append () : Lemma (
  forall (s0 le1 le2:trace). ((List.rev le2) @ (List.rev le1) @ s0) ==
     ((List.rev (le1@le2)) @ s0)) =
  let aux (s0 le1 le2:trace) : Lemma (
    ((List.rev le2) @ (List.rev le1) @ s0) ==
       ((List.rev (le1@le2)) @ s0)) = begin
    List.rev_append le1 le2;
    List.append_assoc (List.rev le2) (List.rev le1) s0
  end in Classical.forall_intro_3 aux


let rec handle #t2 (tree : iio (t2)) (pi:monitorable_prop) : IIO t2 pi (fun _ _ _ -> True) = begin
  match tree with
  | Return r -> r 
  | Throw r -> IIO.Effect.throw r
  | Cont (Call GetTrace argz fnc) ->
      let h = IIO.Effect.get_trace () in
      FStar.WellFounded.axiom1 fnc (Inl h);
      let z' = fnc (Inl h) in
      handle z' pi
  | Cont (Call cmd argz fnc) ->
      let rez : res cmd = IIO.Effect.dynamic_cmd cmd pi argz in
      FStar.WellFounded.axiom1 fnc (Inl rez);
      let z' : sys cmds all_sig t2 = fnc (Inl rez) in
      rev_append_rev_append ();
      handle z' pi
end
  
let import_mio
  (a b : Type)
  (pi : monitorable_prop)
  (f : a -> MIO b) :
  Tot (a -> IIO b pi (fun _ _ _ -> True)) =
    fun (x:a) -> 
        let h = get_trace () in
        // Cezar: I don't think this is ok.
        handle (cast_io_iio (reify (f x) h (fun _ _ -> True))) pi


let ctx_t_to_ctx_p
  (i  : interface)
  (pi : monitorable_prop)
  (ct : ctx_t i) :
  Tot (ctx_p i pi) =
  fun (x:i.ad) -> 
    let h = get_trace () in
    // Cezar: I don't think post unfolded like that is ok.
    handle (cast_io_iio (reify (ct x) h (fun _ _ -> True))) pi

let extract_local_events (s0 s1:trace) :
  Pure trace
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
  Tot (ctx_s i pi) by (
    explode ();
    smt ();
    let zz = get_binder 9 in 
    focus (fun () ->
      let _ = t_destruct zz in
      iterAll (fun () ->
        let bs = repeat intro in
        let b = last bs in (* this one is the equality *)
        rewrite_eqs_from_context ();
        norm [iota];
        ())
    );
    let aq = get_binder 12 in
    focus (fun () -> 
      let _ = t_destruct aq in
      let bs1 = intro () in
      let br = intro () in
      let b = intro () in (* this one is the equality *)
      rewrite_eqs_from_context ();
      // l_to_r [`b];
      norm [iota];
      ()
    );
    explode ();
    tadmit ();
    tadmit ();
    dump "h"
  ) =
  fun (x:i.a) -> 
    assume (forall x err s0 le. i.post x s0 (Inr err) le == true);
    let s0 : trace = IIO.Effect.get_trace () in
    let result : i.b = cp (export x) in
    let s1 : trace = IIO.Effect.get_trace () in
    let le = extract_local_events s0 s1 in

    if check4 #i.a #i.b #i.post #i.cpost x s0 (Inl (s1, result)) le then (
      assert (i.post x s0 (Inl (s1, result)) le);
      result
    ) else IOStHist.throw Contract_failure

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
