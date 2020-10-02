module Rsp

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

let _export_IOStHist_lemma
  #t1 {| d1:importable t1 |} 
  #t2 {| d2:exportable t2 |}
  (pre : t1 -> events_trace -> Type0) {| checkable2 pre |}
  (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
  (f:(x:t1 -> IOStHist t2 (pre x) (post x))) 
  (x':d1.itype) : 
  Lemma (
    let ef : d1.itype -> M4 d2.etype = _export_IOStHist_arrow_spec pre post f in
    let res' = reify (ef x') (fun _ -> True) in
    match import x' with
    | Some x -> (
      let f' = reify (f x) (post x []) in
      (check2 #t1 #events_trace #pre x [] ==>  
        behavior res' `included_in (inl_app (compose export cdr))` behavior (f' [])) /\
      (~(check2 #t1 #events_trace #pre x []) ==>  
        behavior res' `included_in id` empty_set ()))
    | None -> behavior res' `included_in id` empty_set ()) =

  let ef : d1.itype -> M4 d2.etype = _export_IOStHist_arrow_spec pre post f in
  let included_in_id #a = included_in #a #a (id #a) in
  match import x' with
  | Some x -> begin
    if (check2 #t1 #events_trace #pre x []) then (
        calc (included_in_id) {
            behavior (reify (ef x') (fun _ -> True));
            `included_in_id` {}
            behavior (reify ((_export_IOStHist_arrow_spec pre post f <: (d1.itype -> M4 d2.etype)) x') (fun _ -> True));
            // TODO: Cezar: The idea behind this is to get rid of the `match` and the `if` 
            // because we did them already in the proof.
            `included_in_id` { _ by (unfold_def(`_export_IOStHist_arrow_spec); norm [delta]; tadmit ()) }
            behavior (reify (
              (export (M4wp?.reflect (ref (iost_to_io (reify (f x) (post x []) []))) <: M4wp t2 (fun p -> forall res. p res)) <: d2.etype)) (fun _ -> True));
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
                (reify (M4wp?.reflect (ref (iost_to_io (reify (f x) (post x []) []))) <: M4wp t2 (fun p -> forall res. p res)))
                (fun x -> lift_pure_m4wp d2.etype (fun p -> p (export x)) (fun _ -> export x)) (fun _ -> True));
        };

        beh_included_bind_tot #t2 #d2.etype
          (reify (M4wp?.reflect (ref (iost_to_io (reify (f x) (post x []) []))) <: M4wp t2 (fun p -> forall res. p res)) (compute_post t2 (Mkexportable?.etype d2) (fun x -> m4_return_wp (Mkexportable?.etype d2) (export x)) (fun _ -> True)))
            export;

        assert (
            (behavior (M4.ibind t2 d2.etype (fun p -> forall res. p res) (fun x -> m4_return_wp (d2.etype) (export x))
                (reify (M4wp?.reflect (ref (iost_to_io (reify (f x) (post x []) []))) <: M4wp t2 (fun p -> forall res. p res)))
                (fun x -> lift_pure_m4wp d2.etype (fun p -> p (export x)) (fun _ -> export x)) (fun _ -> True)))
          `included_in (inl_app export)`
            (behavior (reify (M4wp?.reflect (ref (iost_to_io (reify (f x) (post x []) []))) <: M4wp t2 (fun p -> forall res. p res)) (fun _ -> True)))
        ) by (unfold_def (`ibind));

       calc (included_in_id) {
         behavior (reify (M4wp?.reflect (ref (iost_to_io (reify (f x) (post x []) []))) <: M4wp t2 (fun p -> forall res. p res)) (fun _ -> True));
         `included_in_id` {}
         behavior (iost_to_io (reify (f x) (post x []) []));
       };

       beh_iost_to_io t2 (reify (f x) (post x []) []);

       assert (
         behavior (iost_to_io (reify (f x) (post x []) []))
         `included_in (inl_app cdr)` 
         behavior (reify (f x) (post x []) []))
    ) else begin
        calc (==) {
            reify (ef x') (fun _ -> True);
            == {}
            reify ((_export_IOStHist_arrow_spec pre post f <: (d1.itype -> M4 d2.etype)) x') (fun _ -> True);
            == { 
            _ by (unfold_def(`_export_IOStHist_arrow_spec); norm [iota]; tadmit ()) }
            reify (M4.raise Contract_failure) (fun _ -> True);
            // TODO: Cezar: The idea behind this is to get rid of the `match` and the `if` 
            // because we did them already in the proof.
            == { admit () }
            Throw Contract_failure;
        }
    end
  end
  | None -> begin
    calc (==) {
        reify (ef x') (fun _ -> True);
        == {}
        reify ((_export_IOStHist_arrow_spec pre post f <: (d1.itype -> M4 d2.etype)) x') (fun _ -> True);
        // TODO: Cezar: two admits here.
        == { 
          _ by (unfold_def(`_export_IOStHist_arrow_spec); norm [iota]; tadmit ()) }
        reify (M4.raise Contract_failure) (fun _ -> True);
        == { admit () }
        Throw Contract_failure;
    }
  end


let export_IOStHist_lemma 
  #t1 {| d1:importable t1 |} 
  #t2 {| d2:exportable t2 |}
  (pre : t1 -> events_trace -> Type0) {| checkable2 pre |}
  (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
  (f:(x:t1 -> IOStHist t2 (pre x) (post x))) : 
  Lemma (forall (x':d1.itype). (
    let ef : d1.itype -> M4 d2.etype = _export_IOStHist_arrow_spec pre post f in
    let res' = reify (ef x') (fun _ -> True) in
    match import x' with
    | Some x -> (
      let f' = reify (f x) (post x []) in
      (check2 #t1 #events_trace #pre x [] ==>  
        behavior res' `included_in (inl_app (compose export cdr))` behavior (f' [])) /\
      (~(check2 #t1 #events_trace #pre x []) ==>  
        behavior res' `included_in id` empty_set ()))
    | None -> behavior res' `included_in id` empty_set ())) =
  Classical.forall_intro (_export_IOStHist_lemma #t1 #d1 #t2 #d2 pre post f)

let export_GIO_lemma 
  #t1 {| d1:importable t1 |} 
  #t2 {| d2:exportable t2 |}
  (pi:check_type)
  (f:(x:t1 -> GIO t2 pi)) : 
  Lemma (forall (x':d1.itype). (
    let ef : d1.itype -> M4 d2.etype = export f in
    let res' = reify (ef x') (fun _ -> True) in
    match import x' with
    | Some x -> (
      let f' = reify (f x) (gio_post pi []) in
      (check2 #t1 #events_trace #(fun _ -> gio_pre pi) x [] ==>  
        behavior res' `included_in (inl_app (compose export cdr))` behavior (f' [])) /\
      (~(check2 #t1 #events_trace #(fun _ -> gio_pre pi) x []) ==>  
        behavior res' `included_in id` empty_set ()))
    | None ->  behavior res' `included_in id` empty_set ())) =
  Classical.forall_intro (_export_IOStHist_lemma (fun _ -> gio_pre pi) (fun _ -> gio_post pi) f)

let export_unit_GIO_lemma
  #t2 {| d2:exportable t2 |}
  (pi:check_type)
  (f:(unit -> GIO t2 pi)) : 
  Lemma (
    let ef : unit -> M4 d2.etype = _export_IOStHist_arrow_spec (fun _ -> gio_pre pi) (fun _ -> gio_post pi) f in
    let res' = reify (ef ()) (fun _ -> True) in
      let f' = reify (f ()) (gio_post pi []) in
      (check2 #unit #events_trace #(fun _ -> gio_pre pi) () [] ==>  
        behavior res' `included_in (inl_app (compose export cdr))` behavior (f' [])) /\
      (~(check2 #unit #events_trace #(fun _ -> gio_pre pi) () []) ==>  
        behavior res' `included_in id` empty_set ())) =
  Classical.forall_intro (_export_IOStHist_lemma (fun _ -> gio_pre pi) (fun _ -> gio_post pi) f)

let rsp_simple_linking
  (a : Type) {| d1:exportable a |}
  (b : Type) {| d2:ml b |}
  (c : Type) {| d3:exportable c |}
  (pi_as_set : set_of_traces (maybe (events_trace * c)))
  (pi : check_type)
  (ps : (a -> GIO b pi) -> GIO c pi)
  (ct : d1.etype -> M4 b) :
  Lemma
    (requires (forall (cs:(a -> GIO b pi)). 
      behavior (reify (ps cs) (gio_post pi []) []) `included_in id` pi_as_set))
    (ensures (
      let pt : (d1.etype -> M4 b) -> M4 d3.etype = _export_IOStHist_arrow_spec (fun _ -> gio_pre pi) (fun _ -> gio_post pi) ps in
      behavior (reify (pt ct) (fun _ -> True)) `included_in (inl_app (compose export cdr))` pi_as_set)) = 
    match import ct with
    | Some (cs : a -> GIO b pi) -> 
      assert (behavior (reify (ps cs) (gio_post pi []) []) `included_in id` pi_as_set) by (
        let prepost = match (List.Tot.nth (cur_binders ()) 11) with
          | Some y -> y | None -> fail "no wp?" in
        let (pre, post) = destruct_and (binder_to_term prepost) in
        let pre = instantiate pre (fresh_uvar None) in
        apply pre);
      
        let pt : (d1.etype -> M4 b) -> M4 d3.etype = _export_IOStHist_arrow_spec (fun _ -> gio_pre pi) (fun _ -> gio_post pi) ps in
        let ws : unit -> GIO c pi = fun _ -> ps cs in
        assert (behavior (reify (ws ()) (gio_post pi []) []) `included_in id` 
          behavior (reify (ps cs) (gio_post pi []) []));
        let wt : unit -> M4 d3.etype = _export_IOStHist_arrow_spec (fun _ -> gio_pre pi) (fun _ -> gio_post pi) ws in
        let included_in_id #a = included_in #a #a (id #a) in
        calc (included_in_id) {
          behavior (reify (pt ct) (fun _ -> True));
          // TODO: Cezar: I try to show that ((export ps) ct) == (export (ps (import ct))).
          // I am not sure how to rewrite and unfold things.
          `included_in_id` { admit () }
          behavior (reify (wt ()) (fun _ -> True));
        };
        export_unit_GIO_lemma pi ws
    | None -> ()
