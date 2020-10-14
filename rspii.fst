module Rspii

open FStar.Calc
open FStar.Tactics

open Common
open IOStHist
open M4
open Minterop

type set_of_traces (a:Type) = events_trace * a -> Type0

val included_in : (#a:Type) -> (#b:Type) -> (b -> a) -> set_of_traces a -> set_of_traces b -> Type0
let included_in rel s1 s2 = forall t r1. s1 (t, r1) ==>  (exists r2. rel r2 == r1 /\ s2 (t, r2))

let rec behavior #a
  (m : io a) : set_of_traces (maybe a) =
  match m with
  | Return x -> fun t -> t == ([], Inl x)
  | Throw err -> fun t -> t == ([], Inr err)
  | Cont t -> begin
    match t with
    | Call cmd args fnc -> (fun (t', r') -> 
      (exists (res:resm cmd) t. (
         FStar.WellFounded.axiom1 fnc res;
         (behavior (fnc res) (t,r')) /\
         t' == (convert_call_to_event cmd args res)::t)))
  end

unfold 
let beh_s #a #b (pi:check_type) (ws:a -> GIO b pi) (x:a) =
  behavior (reify (ws x) (gio_post pi []) [])

unfold
let beh_t #a #b (wt:a -> M4 b) (x:a) =
  behavior (reify (wt x) (fun _ -> True))

let empty_set (#a:Type) () : set_of_traces a = fun (t,r) -> t == []

let beh_shift_trace
  #a
  (cmd : io_cmds)
  (argz : args cmd)
  (rez : resm cmd)
  (fnc : resm cmd -> io a)
  (t:events_trace)
  (r:maybe a) :
  Lemma 
    (requires (behavior (Cont (Call cmd argz fnc)) ((convert_call_to_event cmd argz rez :: t), r)))
    (ensures (behavior (fnc rez) (t, r))) = 
  () 

let beh_extend_trace 
  #a
  (cmd : io_cmds)
  (argz : args cmd)
  (rez : resm cmd)
  (fnc : resm cmd -> io a)
  (t:events_trace)
  (r:maybe a) :
  Lemma
    (requires (behavior (fnc rez) (t, r)))
    (ensures (behavior (Cont (Call cmd argz fnc)) ((convert_call_to_event cmd argz rez) :: t, r))) 
  by (compute ()) = 
  ()

let beh_extend_trace_d
  #a
  (cmd : io_cmds)
  (argz : args cmd)
  (rez : resm cmd)
  (fnc : resm cmd -> io a)
  (t:events_trace) :
  Lemma
    (forall r. (behavior (fnc rez) (t, r) ==>
      (behavior (Cont (Call cmd argz fnc)) ((convert_call_to_event cmd argz rez) :: t, r)))) =
  Classical.forall_intro (
    Classical.move_requires (beh_extend_trace cmd argz rez fnc t))

let beh_extend_trace_in_bind 
  #a #b
  (cmd : io_cmds)
  (argz : args cmd)
  (rez : resm cmd)
  (fnc : resm cmd -> io a)
  (k : a -> io b)
  (t:events_trace)
  (r:maybe b) :
  Lemma
    (requires (behavior (io_bind a b (fnc rez) k) (t, r))) 
    (ensures (behavior (io_bind a b (Cont (Call cmd argz fnc)) k) ((convert_call_to_event cmd argz rez) :: t, r))) =
  calc (==) {
    io_bind a b (Cont (Call cmd argz fnc)) k;
    == {}
    sys_bind io_cmds io_cmd_sig a b (Cont (Call cmd argz fnc)) k;
    == { _ by (norm [iota; delta]; compute ()) }
    Cont (sysf_fmap (fun fnci -> 
      sys_bind io_cmds io_cmd_sig a b fnci k) (Call cmd argz fnc));
    == { _ by (unfold_def(`sysf_fmap); norm [iota]; unfold_def(`io_bind)) }
    Cont (Call cmd argz (fun rez -> 
      io_bind a b (fnc rez) k));
  };
  beh_extend_trace cmd argz rez (fun rez -> io_bind a b (fnc rez) k) t r;
  assert (behavior (Cont (Call cmd argz (fun rez -> 
    io_bind a b (fnc rez) k))) ((convert_call_to_event cmd argz rez) :: t, r)) by (
    unfold_def (`convert_call_to_event); assumption ())

let extract_result (cmd:io_cmds) (event:io_event) : 
  Pure (resm cmd)
    (requires ((cmd == Openfile /\ EOpenfile? event) \/
               (cmd == Read /\ ERead? event) \/
               (cmd == Close /\ EClose? event)))
    (ensures (fun r -> True)) = 
  match cmd with 
  | Openfile -> EOpenfile?.r event 
  | Read -> ERead?.r event 
  | Close -> EClose?.r event 
    
let rec beh_bind_inl
  #a #b
  (m : io a)
  (k : a -> io b) 
  (r1:a) 
  (t1 t2 : events_trace)
  (r2:maybe b) :
  Lemma 
    (requires (behavior m (t1, (Inl r1)) /\ behavior (k r1) (t2, r2)))
    (ensures (behavior (io_bind _ _ m k) (t1 @ t2, r2))) =
  match m with
  | Return x -> ()
  | Throw err -> ()
  | Cont (Call cmd argz fnc) -> begin
    let (ht1 :: tt1) = t1 in
    let rez : resm cmd = extract_result cmd ht1 in
    FStar.WellFounded.axiom1 fnc rez;
    beh_shift_trace cmd argz rez fnc tt1 (Inl r1);
    beh_bind_inl (fnc rez) k r1 tt1 t2 r2;
    beh_extend_trace_in_bind cmd argz rez fnc k (tt1@t2) r2
  end
  
let rec beh_bind_inr
  #a #b
  (m : io a)
  (k : a -> io b)
  (r1:exn)
  (t1 : events_trace) :
  Lemma 
    (requires (behavior m (t1, (Inr r1))))
    (ensures (behavior (io_bind _ _ m k) (t1, (Inr r1)))) =
  match m with
  | Throw err -> ()
  | Cont (Call cmd argz fnc) -> begin
    let (ht1 :: tt1) = t1 in
    let rez : resm cmd = extract_result cmd ht1 in
    FStar.WellFounded.axiom1 fnc rez;
    beh_shift_trace cmd argz rez fnc tt1 (Inr r1);
    beh_bind_inr (fnc rez) k r1 tt1;
    beh_extend_trace_in_bind cmd argz rez fnc k (tt1) (Inr r1)
  end

let beh_bind_0 
  #a #b
  (m : io a)
  (k : a -> io b) 
  (r1:maybe a) :
  Lemma (forall t1.
    behavior m (t1, r1) ==>
      (Inr? r1 ==>  behavior (io_bind _ _ m k) (t1, (Inr (Inr?.v r1)))) /\
      (Inl? r1 ==>  (forall t2 r2. (behavior (k (Inl?.v r1)) (t2, r2) ==>  
                     behavior (io_bind _ _ m k) (t1 @ t2, r2))))) =
  if (Inr? r1) then (
    Classical.forall_intro (
      Classical.move_requires (beh_bind_inr m k (Inr?.v r1)))
  ) else (
    Classical.forall_intro_3 (
      Classical.move_requires_3 (beh_bind_inl m k (Inl?.v r1)))
  )

let beh_bind
  #a #b
  (m : io a)
  (k : a -> io b) :
  Lemma (forall (r1:maybe a) t1.
    behavior m (t1, r1) ==>
      (Inr? r1 ==>  behavior (io_bind _ _ m k) (t1, (Inr (Inr?.v r1)))) /\
      (Inl? r1 ==>  (forall t2 r2. behavior (k (Inl?.v r1)) (t2, r2) ==>  
                              behavior (io_bind _ _ m k) (t1 @ t2, r2)))) =
  Classical.forall_intro (beh_bind_0 m k)

let rec beh_bind_tot_0
  #a #b
  (f:io a) 
  (g:a -> Tot b)
  (r1:maybe b)
  (t:events_trace) :
  Lemma 
    (requires (behavior (io_bind a b f (fun x -> lift_pure_m4wp b (fun p -> p (g x)) (fun _ -> g x) (fun _ -> True))) (t, r1)))
    (ensures (exists r2. inl_app g r2 == r1 /\ behavior f (t, r2)))  =
  match f with
  | Return x -> 
      assert (inl_app g (Inl x) == r1);
      assert (behavior f (t, (Inl x)))
  | Throw err -> 
      assert (inl_app g (Inr err) == r1);
      assert (behavior f (t, (Inr err)))
  | Cont (Call cmd argz fnc) ->
    let (ht1 :: tt1) = t in
    let rez : resm cmd = extract_result cmd ht1 in
    FStar.WellFounded.axiom1 fnc rez;
    beh_bind_tot_0 (fnc rez) g r1 tt1;
    beh_extend_trace_d cmd argz rez fnc (tt1)
       
let beh_bind_tot
  #a #b
  (f:io a)
  (g:a -> Tot b) :
  Lemma 
    (forall r1 t. (behavior (io_bind a b f (fun x -> lift_pure_m4wp b (fun p -> p (g x)) (fun _ -> g x) (fun _ -> True))) (t, r1)) ==>  (exists r2. r1 == inl_app g r2 /\ behavior f (t,r2))) =
  Classical.forall_intro_2 (Classical.move_requires_2 (beh_bind_tot_0 f g))

let beh_included_bind_tot
  #a #b
  (f:io a) 
  (g:a -> Tot b) :
  Lemma
    (included_in (inl_app g)
      (behavior (io_bind a b f (fun x -> lift_pure_m4wp b (fun p -> p (g x)) (fun _ -> g x) (fun _ -> True))))
      (behavior f)) = 
  beh_bind_tot f g

let beh_iost_to_io (a:Type) (tree:io (events_trace * a)) :
  Lemma (behavior (iost_to_io tree) `included_in (inl_app cdr)` behavior tree) 
  by (unfold_def (`iost_to_io); norm [iota;delta]; compute ()) =
  beh_included_bind_tot #(events_trace * a) #a
    tree
    cdr

unfold let ref #a (x : io a) : M4.irepr a (fun p -> forall res. p res) = (fun _ -> x)

let beh_included_in_trans_id x y z :
  Lemma (
    (behavior x `included_in id` behavior y /\
    behavior y `included_in id` behavior z) ==>
      behavior x `included_in id` behavior z) = ()
  
let beh_included_in_trans_id_g x y z g:
  Lemma (
    (behavior x `included_in id` behavior y /\
    behavior y `included_in g` behavior z) ==>
      behavior x `included_in g` behavior z) = ()
  
let beh_included_in_trans_g_id x y z g:
  Lemma (
    (behavior x `included_in g` behavior y /\
    behavior y `included_in id` behavior z) ==>
      behavior x `included_in g` behavior z) = ()

let beh_included_in_merge_f_g x y z f g:
  Lemma (
    (behavior x `included_in f` behavior y /\
    behavior y `included_in g` behavior z) ==>
      behavior x `included_in (compose f g)` behavior z) = ()

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

let pi_to_set #a (pi : check_type) : set_of_traces a = fun (t, _) -> enforced_globally pi (List.rev t)

let gio_post_implies_set_of_traces 
  (a : Type)
  (b : Type)
  (pi : check_type)
  (t : events_trace)
  (r : maybe (events_trace * b)) :
  Lemma 
    (requires  (gio_post pi [] r t))
    (ensures (pi_to_set pi (t, r))) = 
    List.Tot.Properties.append_l_nil (List.rev t);
    ()

let iohist_interp_shift_trace
  #a
  (cmd : io_cmds)
  (argz : args cmd)
  (rez : resm cmd)
  (fnc : resm cmd -> io a)
  (h:events_trace)
  p:
  Lemma 
    (requires (iohist_interpretation (Cont (Call cmd argz fnc)) h p))
    (ensures (
      iohist_interpretation (fnc rez) (convert_call_to_event cmd argz rez :: h) (gen_post p (convert_call_to_event cmd argz rez)))) = 
  calc (==) {
    iohist_interpretation (Cont (Call cmd argz fnc)) h p;
    == { _ by (compute ())}
    (forall res. (
      let event : io_event = convert_call_to_event cmd argz res in
      iohist_interpretation (fnc res) (event :: h) (gen_post p event)));
  }

let rec gio_interpretation_implies_set_of_traces
  (a : Type)
  (pi : check_type)
  (m : io (events_trace * a)) 
  (h : events_trace)
  (le : events_trace)
  (r : maybe (events_trace * a)) 
  p :
  Lemma 
    (requires (iohist_interpretation m h p) /\ behavior m (le, r))
    (ensures (p r le)) =
  match m with
  | Return _ -> ()
  | Throw _ -> ()
  | Cont (Call cmd argz fnc) -> begin
    let (ht1 :: tt1) = le in
    let rez : resm cmd = extract_result cmd ht1 in
    FStar.WellFounded.axiom1 fnc rez;
    beh_shift_trace cmd argz rez fnc tt1 r;
    iohist_interp_shift_trace cmd argz rez fnc h p;
    gio_interpretation_implies_set_of_traces a pi (fnc rez) (convert_call_to_event cmd argz rez :: h) tt1 r (gen_post p (convert_call_to_event cmd argz rez))
  end

let beh_gio_implies_post 
  (a : Type)
  (b : Type)
  (pi : check_type)
  (ws : a -> GIO b pi) 
  (x : a)
  (t : events_trace)
  (r : maybe (events_trace * b)) :
  Lemma 
    (requires (beh_s pi ws x (t, r)))
    (ensures  (gio_post pi [] r t)) =
  let ws' = reify (ws x) (gio_post pi []) [] in
  gio_interpretation_implies_set_of_traces b pi ws' [] t r (gio_post pi []) 

noeq type interface = {
  a : Type;
  ad : exportable a;
  b : Type;
  bd : ml b;
  c : Type;
  cd : exportable c;
}

type whole_s (pi:check_type) (i:interface) = unit -> GIO i.c pi
type whole_t (i:interface) = unit -> M4 i.cd.etype

type ctx_s (pi:check_type) (i:interface) = i.a -> GIO i.b pi
type ctx_t (i:interface) = i.ad.etype -> M4 i.b

type prog_s (pi:check_type) (i:interface) = ctx_s pi i -> GIO i.c pi
type prog_t (i:interface) = ctx_t i -> M4 i.cd.etype

let beh_gio_in_pi_0 
  (a b : Type)
  (pi : check_type)
  (ws : a -> GIO b pi) 
  (x : a)
  (t : events_trace)
  (r : maybe (events_trace * b)) :
  Lemma 
    (requires ((beh_s pi ws x) (t, r)))
    (ensures  ((pi_to_set pi) (t, r))) =
  beh_gio_implies_post a b pi ws x t r;
  gio_post_implies_set_of_traces a b pi t r
  
let beh_gio_in_pi
  (a b : Type)
  (pi : check_type)
  (ws : a -> GIO b pi) 
  (x : a) :
  Lemma (beh_s pi ws x `included_in id` pi_to_set pi) =
  Classical.forall_intro_2 (Classical.move_requires_2 (beh_gio_in_pi_0 a b pi ws x))

val import_ctx_t : (#pi:check_type) -> (#i:interface) -> ctx_t i -> option (ctx_s pi i)
let import_ctx_t #pi #i f =
  let f' : (ctx_s pi i) = (
    fun (x:i.a) ->
      let x : i.ad.etype = export x in
      let tree = reify (f x) (fun r -> True) in
      _import_M4_to_GIO #i.b tree pi <: GIO i.b pi) in 
  Some f'
  
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

let export_prog_s
  (i  : interface)
  (pi : check_type)
  (f  : prog_s pi i) : 
  Tot (prog_t i) =
    (fun (ct:ctx_t i) ->
      let Some (cs : ctx_s pi i) = import_ctx_t ct in
      let tree : io (events_trace * i.c) = reify (f cs) (gio_post pi []) [] in
      export (M4wp?.reflect (fun _ -> iost_to_io tree) <: M4wp i.c (fun p -> forall res. p res)))

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

let rsp_simple_linking
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


let rec beh_implies_iohist_interp 
  (a : Type)
  (m : io (events_trace * a)) 
  (h : events_trace)
  (t : events_trace)
  (r : maybe (events_trace * a)) :
  Lemma 
    (requires (behavior m (t,r)))
    (ensures (iohist_interpretation m h (fun res le -> (t,res) == (le,r)))) = 
  match m with
  | Return _ -> ()
  | Throw _ -> ()
  | Cont (Call cmd argz fnc) -> admit ()
