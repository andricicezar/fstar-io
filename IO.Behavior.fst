module IO.Behavior

open FStar.Calc
open FStar.Tactics

open Common
open IO.Free
open IO.Effect
open IIO.Effect
open MIO.Effect
open MIIO.Effect

type set_of_traces (a:Type) = trace * a -> Type0

val set_of_traces_ret : (#a:Type) -> a -> set_of_traces a
let set_of_traces_ret x (es, x') = x == x' /\ es == []

val set_of_traces_bind : (#a:Type) -> (#b:Type) -> set_of_traces a -> (a -> set_of_traces b) -> set_of_traces b
let set_of_traces_bind p f (es, b) = exists (es1 es2 : trace) . exists a . es == (es1 @ es2) /\ p (es1, a) /\ f a (es2, b)

val set_of_traces_map : (#a:Type) -> (#b:Type) -> (a -> b) -> set_of_traces a -> set_of_traces b
let set_of_traces_map f p (es, b) = exists a . f a == b /\ p (es, a)

let empty_set (#a:Type) () : set_of_traces a = fun (t,r) -> t == []
let pi_to_set #a (pi : monitorable_prop) : set_of_traces a = fun (t, _) -> enforced_globally pi (List.rev t)


val included_in : (#a:Type) -> (#b:Type) -> (b -> a) -> set_of_traces a -> set_of_traces b -> Type0
let included_in rel s1 s2 = forall t r1. s1 (t, r1) ==>  (exists r2. rel r2 == r1 /\ s2 (t, r2))

let rec behavior #a
  (m : io a) : set_of_traces (maybe a) =
  match m with
  | Return x -> fun t -> t == ([], Inl x)
  | Throw err -> fun t -> t == ([], Inr err)
  | Cont t -> begin
    match t with
    | Call cmd arg fnc -> (fun (t', r') -> 
      (exists (r:io_resm cmd) t. (
         FStar.WellFounded.axiom1 fnc r;
         (behavior (fnc r) (t,r')) /\
         t' == (convert_call_to_event cmd arg r)::t)))
  end

let beh_shift_trace
  #a
  (cmd : io_cmds)
  (arg : io_args cmd)
  (rez : io_resm cmd)
  (fnc : maybe (io_res cmd) -> io a)
  (t:trace)
  (r:maybe a) :
  Lemma 
    (requires (behavior (Cont (Call cmd arg fnc)) ((convert_call_to_event cmd arg rez :: t), r)))
    (ensures (behavior (fnc rez) (t, r))) = 
  () 

let beh_extend_trace 
  #a
  (cmd : io_cmds)
  (arg : io_args cmd)
  (rez : io_resm cmd)
  (fnc : maybe (io_res cmd) -> io a)
  (t:trace)
  (r:maybe a) :
  Lemma
    (requires (behavior (fnc rez) (t, r)))
    (ensures (behavior (Cont (Call cmd arg fnc)) ((convert_call_to_event cmd arg rez) :: t, r))) 
  by (compute ()) = 
  ()

let beh_extend_trace_d
  #a
  (cmd : io_cmds)
  (arg : io_args cmd)
  (rez : io_resm cmd)
  (fnc : maybe (io_res cmd) -> io a)
  (t:trace) :
  Lemma
    (forall r. (behavior (fnc rez) (t, r) ==>
      (behavior (Cont (Call cmd arg fnc)) ((convert_call_to_event cmd arg rez) :: t, r)))) =
  Classical.forall_intro (
    Classical.move_requires (beh_extend_trace cmd arg rez fnc t))

let beh_extend_trace_in_bind 
  #a #b
  (cmd : io_cmds)
  (arg : io_args cmd)
  (rez : io_resm cmd)
  (fnc : maybe (io_res cmd) -> io a)
  (k : a -> io b)
  (t:trace)
  (r:maybe b) :
  Lemma
    (requires (behavior (io_bind a b (fnc rez) k) (t, r))) 
    (ensures (behavior (io_bind a b (Cont (Call cmd arg fnc)) k) ((convert_call_to_event cmd arg rez) :: t, r))) =
  calc (==) {
    io_bind a b (Cont (Call cmd arg fnc)) k;
    == {}
    sys_bind io_cmds io_sig a b (Cont (Call cmd arg fnc)) k;
    == { _ by (norm [iota; delta]; compute ()) }
    Cont (sysf_fmap (Call cmd arg fnc) 
      (fun fnci -> sys_bind io_cmds io_sig a b fnci k));
    == { _ by (norm [delta_only [`%sysf_fmap]]; 
               norm [iota]; 
               norm [delta_only [`%io_bind]];
               compute ()) }
    Cont (Call cmd arg (fun rez -> 
      io_bind a b (fnc rez) k));
  };
  beh_extend_trace cmd arg rez (fun rez -> io_bind a b (fnc rez) k) t r;
  assert (behavior (Cont (Call cmd arg (fun rez -> 
    io_bind a b (fnc rez) k))) ((convert_call_to_event cmd arg rez) :: t, r)) by (
    unfold_def (`convert_call_to_event); assumption ())

let extract_result (cmd:io_cmds) (e:event) : 
  Pure (resm cmd)
    (requires ((cmd == Openfile /\ EOpenfile? e) \/
               (cmd == Read /\ ERead? e) \/
               (cmd == Close /\ EClose? e)))
    (ensures (fun r -> True)) = 
  match cmd with 
  | Openfile -> EOpenfile?.r e
  | Read -> ERead?.r e
  | Close -> EClose?.r e
    
let rec beh_bind_inl
  #a #b
  (m : io a)
  (k : a -> io b) 
  (r1:a) 
  (t1 t2 : trace)
  (r2:maybe b) :
  Lemma 
    (requires (behavior m (t1, (Inl r1)) /\ behavior (k r1) (t2, r2)))
    (ensures (behavior (io_bind _ _ m k) (t1 @ t2, r2))) =
  match m with
  | Return x -> ()
  | Throw err -> ()
  | Cont (Call cmd arg fnc) -> begin
    let (ht1 :: tt1) = t1 in
    let rez : resm cmd = extract_result cmd ht1 in
    FStar.WellFounded.axiom1 fnc rez;
    beh_shift_trace cmd arg rez fnc tt1 (Inl r1);
    beh_bind_inl (fnc rez) k r1 tt1 t2 r2;
    beh_extend_trace_in_bind cmd arg rez fnc k (tt1@t2) r2
  end
  
let rec beh_bind_inr
  #a #b
  (m : io a)
  (k : a -> io b)
  (r1:exn)
  (t1 : trace) :
  Lemma 
    (requires (behavior m (t1, (Inr r1))))
    (ensures (behavior (io_bind _ _ m k) (t1, (Inr r1)))) =
  match m with
  | Throw err -> ()
  | Cont (Call cmd arg fnc) -> begin
    let (ht1 :: tt1) = t1 in
    let rez : resm cmd = extract_result cmd ht1 in
    FStar.WellFounded.axiom1 fnc rez;
    beh_shift_trace cmd arg rez fnc tt1 (Inr r1);
    beh_bind_inr (fnc rez) k r1 tt1;
    beh_extend_trace_in_bind cmd arg rez fnc k (tt1) (Inr r1)
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

type set_of_traces' (a:Type) = set_of_traces (maybe a)
val set_of_traces_bind' : (#a:Type) -> (#b:Type) -> set_of_traces' a -> (a -> set_of_traces' b) -> set_of_traces' b
let set_of_traces_bind' p f (es, b) = exists es1 es2 . exists a . es == (es1 @ es2) /\ p (es1, a) /\ (Inr? a ==> es2 == [] /\ b == Inr (Inr?.v a)) /\ (Inl? a ==> f (Inl?.v a) (es2, b))

let beh_bind
  #a #b
  (m : io a)
  (k : a -> io b) :
  Lemma (
    set_of_traces_bind' (behavior m) (fun a -> behavior (k a)) 
      `included_in id` 
    behavior (io_bind _ _ m k)) 
  by (unfold_def (`included_in); unfold_def (`set_of_traces_bind')) =
  Classical.forall_intro (beh_bind_0 m k)

let rec beh_bind_tot_0
  #a #b
  (f:io a) 
  (g:a -> Tot b)
  (r1:maybe b)
  (t:trace) :
  Lemma 
    (requires (behavior (io_bind a b f (fun x -> M4.lift_pure_mfour b (fun p -> p (g x)) (fun _ -> g x) (fun _ -> True))) (t, r1)))
    (ensures (exists r2. inl_app g r2 == r1 /\ behavior f (t, r2)))  =
  match f with
  | Return x -> 
      assert (inl_app g (Inl x) == r1);
      assert (behavior f (t, (Inl x)))
  | Throw err -> 
      assert (inl_app g (Inr err) == r1);
      assert (behavior f (t, (Inr err)))
  | Cont (Call cmd arg fnc) ->
    let (ht1 :: tt1) = t in
    let rez : resm cmd = extract_result cmd ht1 in
    FStar.WellFounded.axiom1 fnc rez;
    beh_bind_tot_0 (fnc rez) g r1 tt1;
    beh_extend_trace_d cmd arg rez fnc (tt1)
       
let beh_bind_tot
  #a #b
  (f:io a)
  (g:a -> Tot b) :
  Lemma 
    (forall r1 t. (behavior (io_bind a b f (fun x -> M4.lift_pure_mfour b (fun p -> p (g x)) (fun _ -> g x) (fun _ -> True))) (t, r1)) ==>  (exists r2. r1 == inl_app g r2 /\ behavior f (t,r2))) =
  Classical.forall_intro_2 (Classical.move_requires_2 (beh_bind_tot_0 f g))

let beh_included_bind_tot
  #a #b
  (f:io a) 
  (g:a -> Tot b) :
  Lemma
    (included_in (inl_app g)
      (behavior (io_bind a b f (fun x -> M4.lift_pure_mfour b (fun p -> p (g x)) (fun _ -> g x) (fun _ -> True))))
      (behavior f)) = 
  beh_bind_tot f g

let beh_iost_to_io (a:Type) (tree:io (trace * a)) :
  Lemma (behavior (IOStHist.iost_to_io tree) `included_in (inl_app cdr)` behavior tree) 
  by (unfold_def (`IOStHist.iost_to_io); norm [iota;delta]; compute ()) =
  beh_included_bind_tot #(trace * a) #a
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


let beh_implies_iohist_interp 
  (a : Type)
  (m : io (trace * a)) 
  (t : trace)
  (r : maybe (trace * a)) :
  Lemma 
    (requires (behavior m (t,r)))
    (ensures (iohist_interpretation m (fun res le -> (t,res) == (le,r)))) = 
  match m with
  | Return _ -> ()
  | Throw _ -> ()
  | Cont (Call cmd arg fnc) -> admit ()

let gio_post_implies_set_of_traces 
  (a : Type)
  (b : Type)
  (pi : monitorable_prop)
  (t : trace)
  (r : maybe (trace * b)) :
  Lemma 
    (requires  (m4wp_invariant_post pi [] r t))
    (ensures (pi_to_set pi (t, r))) = 
    List.Tot.Properties.append_l_nil (List.rev t);
    ()

let iohist_interp_shift_trace
  #a
  (cmd : io_cmds)
  (arg : args cmd)
  (rez : resm cmd)
  (fnc : resm cmd -> io a)
  p:
  Lemma 
    (requires (iohist_interpretation (Cont (Call cmd arg fnc)) p))
    (ensures (
      iohist_interpretation (fnc rez) (gen_post p (convert_call_to_event cmd arg rez)))) = 
  calc (==) {
    iohist_interpretation (Cont (Call cmd arg fnc)) p;
    == { _ by (compute ())}
    (forall res. (
      let event : io_event = convert_call_to_event cmd arg res in
      iohist_interpretation (fnc res) (gen_post p event)));
  }

let rec gio_interpretation_implies_set_of_traces
  (a : Type)
  (pi : monitorable_prop)
  (m : io (trace * a)) 
  (le : trace)
  (r : maybe (trace * a)) 
  p :
  Lemma 
    (requires (iohist_interpretation m p) /\ behavior m (le, r))
    (ensures (p r le)) =
  match m with
  | Return _ -> ()
  | Throw _ -> ()
  | Cont (Call cmd arg fnc) -> begin
    let (ht1 :: tt1) = le in
    let rez : resm cmd = extract_result cmd ht1 in
    FStar.WellFounded.axiom1 fnc rez;
    beh_shift_trace cmd arg rez fnc tt1 r;
    iohist_interp_shift_trace cmd arg rez fnc p;
    gio_interpretation_implies_set_of_traces a pi (fnc rez) tt1 r (gen_post p (convert_call_to_event cmd arg rez))
  end


unfold 
let beh #a #b (pi:monitorable_prop) (ws:a -> M4wp b pi (fun _ _ _ -> True)) (x:a) =
  behavior (reify (ws x) (m4wp_invariant_post pi []) [])
  
let beh_gio_implies_post 
  (a : Type)
  (b : Type)
  (pi : monitorable_prop)
  (ws : a -> M4wp b pi (fun _ _ _ -> True)) 
  (x : a)
  (t : trace)
  (r : maybe (trace * b)) :
  Lemma 
    (requires (beh pi ws x (t, r)))
    (ensures  (m4wp_invariant_post pi [] r t)) =
  let ws' = reify (ws x) (m4wp_invariant_post pi []) [] in
  gio_interpretation_implies_set_of_traces b pi ws' t r (m4wp_invariant_post pi []) 

let beh_gio_in_pi_0 
  (a b : Type)
  (pi : monitorable_prop)
  (ws : a -> M4wp b pi (fun _ _ _ -> True)) 
  (x : a)
  (t : trace)
  (r : maybe (trace * b)) :
  Lemma 
    (requires ((beh pi ws x) (t, r)))
    (ensures  ((pi_to_set pi) (t, r))) =
  beh_gio_implies_post a b pi ws x t r;
  gio_post_implies_set_of_traces a b pi t r
  
let beh_gio_in_pi
  (a b : Type)
  (pi : monitorable_prop)
  (ws : a -> M4wp b pi (fun _ _ _ -> True))
  (x : a) :
  Lemma (beh pi ws x `included_in id` pi_to_set pi) =
  Classical.forall_intro_2 (Classical.move_requires_2 (beh_gio_in_pi_0 a b pi ws x))
  
