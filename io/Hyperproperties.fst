module Hyperproperties

open FStar.Tactics
open ExtraTactics
open FStar.Ghost
open FStar.String

open IIO
open IIO.Behavior
open BeyondCriteria

(** There are many difficulties on trying to state Hyperproperties
about whole/partial source programs. **)

(** Whole programs **)

let read_content (fnm:string) : IIO (r:(resexn string){~(r == Inr Contract_failure)}) IOActions
  (requires (fun _ -> True))
  (ensures (fun _ r lt -> 
    (Inr? r /\ lt == [EOpenfile fnm (Inr (Inr?.v r))]) \/
    (exists fd. lt == [EOpenfile fnm (Inl fd);ERead fd r])
    )) =
  match static_cmd Openfile fnm with
  | Inl fd -> static_cmd Read fd
  | Inr err -> Inr err

let rec get_fd_content (fd:file_descr) (t:IIO.Sig.trace) : option string =
  match t with
  | [] -> None
  | (ERead fd' (Inl msg')) :: tl -> if fd = fd' then (Some msg') else (get_fd_content fd tl)
  | (ERead fd' (Inr msg')) :: tl -> if fd = fd' then None else (get_fd_content fd tl)
  | _ :: tl -> get_fd_content fd tl
  
let rec get_content (fnm:string) (t:IIO.Sig.trace) : option string =
  match t with
  | [] -> None
  | (EOpenfile fnm' (Inl fd')) :: tl -> if fnm = fnm' then (get_fd_content fd' tl) else (get_content fnm tl)
  | (EOpenfile fnm' (Inr fd')) :: tl -> if fnm = fnm' then None else (get_content fnm tl)
  | _ :: tl -> get_content fnm tl

val tp1 : trace_property #event
let tp1 (tr:trace) =
  match tr with
  | Infinite_trace _ -> False
  | Finite_trace t r -> 
    match get_content "config.txt" t with
    | Some msg1 -> strlen msg1 == r
    | None -> r == 0

(** Non-interference of secret **)
val hyperprop_tp1 : unit ->  Lemma (
  forall (tr1 tr2:trace). tr1 `member_of` tp1 /\ tr2 `member_of` tp1 ==> 
  (match tr1, tr2 with
  | Finite_trace t1 r1, Finite_trace t2 r2 -> (
    get_content "config.txt" t1 == get_content "config.txt" t2 ==> r1 == r2)))
let hyperprop_tp1 () = ()

let whole1 () : IIO int AllActions 
  (requires (fun _ -> True))
  (ensures (fun _ r lt -> tp1 (Finite_trace lt r))) =
  let config = read_content "config.txt" in
  let secret = read_content "secret.txt" in
  match config with
  | Inl msg -> strlen msg
  | Inr err -> 0

(** Non-interference of secret **)
val hyperprop_whole1 : unit -> Lemma (
  forall (tr1 tr2:trace). tr1 `member_of` (beh whole1) /\ tr2 `member_of` (beh whole1) ==>
  (match tr1, tr2 with
  | Finite_trace t1 r1, Finite_trace t2 r2 -> (
    get_content "config.txt" t1 == get_content "config.txt" t2 ==> r1 == r2)
  | _, _ -> False))
let hyperprop_whole1 () = 
  assume (beh whole1 `subset_of` tp1);
  assert (forall (tr:trace). tr `member_of` (beh whole1) ==> tr `member_of` tp1);
  hyperprop_tp1 ();
  ()

(** ** partial programs **)

open FStar.Tactics

open Compiler.Model
open FStar.List.Tot

let make_rc_tree (#a:Type) (#b:Type) (rc:a -> trace -> b -> trace -> bool) : tree pck_rc =
  Node (| a, b, rc |) Leaf Leaf

let rec ni_traces (pi:monitorable_prop) (rc:('a -> trace -> 'b -> trace -> bool)) (r1 r2:int) (h1 h2 acc_lt lt1 lt2:trace) : 
  GTot Type0 (decreases lt1) =
  match lt1, lt2 with
  | [], [] -> r1 == r2
  | hd1::t1, hd2::t2 -> begin
    (forall cmd arg. pi cmd arg (rev acc_lt @ h1) == pi cmd arg (rev acc_lt @ h2)) /\
    (forall (i:nat) x y. i < length acc_lt ==> (
      let call1, call2 = splitAt i acc_lt in
      rc x (rev call1 @ h1) y call2 == rc x (rev call1 @ h2) y call2))
  ==> (
    let (| cmd1, arg1, res1 |) = destruct_event hd1 in
    let (| cmd2, arg2, res2 |) = destruct_event hd2 in 
    (cmd1 == cmd2 /\ arg1 == arg2 /\ (* output hd1 == output hd2 *)
      (res1 == res2 (* input hd1 == input hd2 *) ==> ni_traces pi rc r1 r2 h1 h2 (acc_lt@[hd1]) t1 t2)))
  end
  | _, _ -> False

val ni : 
  pi : monitorable_prop ->
  (** for any runtime check **)
  rc : ('a -> trace -> 'b -> trace -> bool) ->
  (** the ctx is in a first-order setting. I don't think it matters **)
  ctx: (fl:erased tflag -> pi:erased monitorable_prop -> typ_io_cmds fl pi -> typ_eff_rcs fl (make_rc_tree rc) -> unit -> IIO int fl (fun _ -> True) (fun _ _ _ -> True)) ->
  Lemma (
                                  (** one has to instantiate the ctx to be able to call beh **)
    let bh = beh_ctx #(fun _ -> True) (ctx AllActions pi (inst_io_cmds pi) (make_rcs_eff (make_rc_tree rc))) in
    forall h1 lt1 r1 h2 lt2 r2. 
      (h1, Finite_trace lt1 r1) `pt_mem` bh /\ 
      (h2, Finite_trace lt2 r2) `pt_mem` bh /\
      ni_traces pi rc r1 r2 h1 h2 [] lt1 lt2)

(* Termination-insensitive noninterference (TINI) definition took from Beyond Full Abstraction
    TINI = {b | ∀t1 t2∈b. (t1 terminating ∧ t2 terminating
                          ∧ pub-inputs(t1)=pub-inputs(t2))
                          ⇒ pub-events(t1)=pub-events(t2)} 
                          
                          
   The traces in our case have 2 components, the history and the local trace * result.

   Our notion of pub-inputs and pub-events is as follows:

   pub-inputs is our leak_the_same predicate.
   
   pub-events = all the events produced by the context (local trace) and its result.
   
   TODO:
   - [ ] is it the theorem we want?
   - [ ] can we write it in a more simple way to be easier to prove in F*?
   - [ ] prove *)
val leak_the_same : trace -> trace -> pi:monitorable_prop -> rc:('a -> trace -> 'b -> trace -> bool) -> Type0
let leak_the_same h1 h2 pi rc =
  // for each valid local trace of h1,
  // there exists a valid local trace for h2
  // both leaking the same information through pi and rc
  (forall lt1. enforced_locally pi h1 lt1 ==> 
    (exists lt2. enforced_locally pi h2 lt2 /\
      (forall cmd arg. pi cmd arg (rev lt1 @ h1) == pi cmd arg (rev lt2 @ h2)) /\
      (forall arg res. rc arg h1 res lt1 == rc arg h2 res lt2)))

val tini : 
  pi : monitorable_prop ->
  (** for any runtime check **)
  rc : ('a -> trace -> 'b -> trace -> bool) ->
  (** the ctx is in a first-order setting. I don't think it matters **)
  ctx: (fl:erased tflag -> pi:erased monitorable_prop -> typ_io_cmds fl pi -> typ_eff_rcs fl (make_rc_tree rc) -> unit -> IIO int fl (fun _ -> True) (fun _ _ _ -> True)) ->
  Lemma (
                                  (** one has to instantiate the ctx to be able to call beh **)
    let bh = beh_ctx #(fun _ -> True) (ctx AllActions pi (inst_io_cmds pi) (make_rcs_eff (make_rc_tree rc))) in
    forall h1 lt1 r1 h2 lt2 r2. 
      (h1, Finite_trace lt1 r1) `pt_mem` bh /\ 
      (h2, Finite_trace lt2 r2) `pt_mem` bh /\
      leak_the_same h1 h2 pi rc ==> 
        (* this is not true since the results of IO actions are different *)
        lt1 == lt2 /\ r1 == r2)

let tini pi rc ctx = admit ()

(* Generalized Non-Interference definition took from Hyperproperties, Michael R. Clarkson and
   Fred B. Schneider, specialized for our case. The original: 
   
   GNI = { T ∈ Prop | ∀t1,t2 ∈ T: (∃t3 ∈ T: evHin(t3) = evHin(t1) ∧ evL(t3) = evL(t2)) }

   The traces in our case have 2 components, the history and the local trace * result.

   Our notion of high events and low events is as follows:

   The high events are the events that happened before calling the context (the history)
   and we would like it to be non-interferent with the behavior of the context (local trace * result).
   However, this is not possible since pi and the runtime checks leak information,
   thus we had to add a relation between t1 and t2 as an assumption, that they leak
   the same amount of information.

   The low events are all the events produced by the context (local trace) and its result.

   !!!
   We do NOT want this theorem, because this is for nondeterministic programs,
   while our programs are determinstic, thus this is too complex! *)
val gni : 
  pi : monitorable_prop ->
  (** for any runtime check **)
  rc : ('a -> trace -> 'b -> trace -> bool) ->
  (** the ctx is in a first-order setting. I don't think it matters **)
  ctx: (fl:erased tflag -> pi:erased monitorable_prop -> typ_io_cmds fl pi -> typ_eff_rcs fl (make_rc_tree rc) -> unit -> IIO int fl (fun _ -> True) (fun _ _ _ -> True)) ->
  Lemma (
    let eff_rcs = make_rcs_eff (make_rc_tree rc) in
    let bh = beh_ctx #(fun _ -> True) (ctx AllActions pi (inst_io_cmds pi) eff_rcs) in
    forall h1 lt1 r1 h2 lt2 r2. 
      (h1, Finite_trace lt1 r1) `pt_mem` bh /\ 
      (h2, Finite_trace lt2 r2) `pt_mem` bh /\
      leak_the_same h1 h2 pi rc
    ==> (exists h3 lt3 r3. (h3, Finite_trace lt3 r3) `pt_mem` bh /\ 
                      h1 == h3 /\ lt2 == lt3 /\ r2  == r3))

(**
I thought I can make it more general by using the model directly.
However, this cannot be typed because we don't know the argument type of ctx,
thus ctx cannot be thunked to be reified.

val gni0 :
  i : src_interface ->
  ctx : ctx_src i ->
  Lemma (
    let eff_rcs = make_rcs_eff i.ct_rcs in 
    let bh = beh_ctx #(fun _ -> True) (ctx AllActions pi (inst_io_cmds pi) eff_rcs) in
    forall h1 lt1 r1 h2 lt2 r2. 
      (h1, Finite_trace lt1 r1) `pt_mem` bh /\ 
      (h2, Finite_trace lt2 r2) `pt_mem` bh /\
      leak_the_same h1 h2 pi rc
    ==> (exists h3 lt3 r3. (h3, Finite_trace lt3 r3) `pt_mem` bh /\ 
                      h1 == h3 /\ lt2 == lt3 /\ r2  == r3))
**)

(* h is non-interfering for flag polymorphic simplified ctx
  -- should be true since this ctx cannot do any actions

  the type of ctx is simplified here:
    * unit, int should be arbitrary types
    * it can be HO
    * ctx should also take instrumented actions
    * ctx should also take the contracts *)
val gni_v0 : 
  ctx:(fl:erased tflag -> unit -> IIO int fl (fun _ -> True) (fun _ _ _ -> True)) ->
  Lemma (
    let bh = beh_ctx #(fun _ -> True) (ctx AllActions) in
    forall t1 t2. t1 `pt_mem` bh /\ t2 `pt_mem` bh ==>
      (exists t3. t3 `pt_mem` bh /\ 
             fst t1 == fst t3 /\ // histories are equal
             snd t2 == snd t3   // local traces are equal
             ))
             
let gni_v0 ctx =
  let bh = beh_ctx #(fun _ -> True) (ctx AllActions) in
  let reified_ctx : dm_giio int AllActions (to_hist (fun _ -> True) (fun _ _ _ -> True)) = __reify_IIOwp (ctx AllActions) in
  introduce forall t1 t2.
  t1 `pt_mem` bh /\ t2 `pt_mem` bh 
  ==> (exists t3. t3 `pt_mem` bh /\ fst t1 == fst t3 /\ snd t2 == snd t3) 
  with begin
    introduce t1 `pt_mem` bh /\ t2 `pt_mem` bh
    ==> (exists t3. t3 `pt_mem` bh /\ fst t1 == fst t3 /\ snd t2 == snd t3)
    with _. begin
      let newH = (fst t1) in
      let t3 = (newH, snd t2) in 
      assert (t2 `pt_mem` bh); (** unfolds to: **)
      //assert ((snd t2) `member_of #event` beh_giio reified_ctx (fst t2)); (* not sure why it does not work *)
      assume ((snd t2) `member_of` beh_giio reified_ctx newH); (** folds into: **)
      assert (t3 `pt_mem` bh) by (
        binder_retype (nth_binder (-1)); norm [delta_only [`%member_of];iota]; trefl ();
        norm [delta_only [`%pt_mem;`%beh_ctx;`%_beh_ctx]; iota]; 
        // assumption (); -- not sure why it is failing
        tadmit ());
      assert (fst t1 == fst t3);
      assert (snd t2 == snd t3)
    end
  end

val pprog1 : 
  fl:erased tflag ->
  ctx:(unit -> IIO int fl (fun _ -> True) (fun _ _ _ -> True)) ->
  IIO int (fl + IOActions) (fun _ -> True) (fun _ _ _ -> True) 
let pprog1 fl ctx =
  let msg = read_content "secrets.txt" in  
 // let _ = ctx () in
  7

val hyperprop_pprog1 : ctx:_ -> tr1:_ -> tr2:_ -> 
  Lemma 
    (requires (
      let bh = beh (fun () -> pprog1 AllActions ctx) in (
      tr1 `member_of` bh /\ tr2 `member_of` bh)))
    (ensures (
       match tr1, tr2 with
       | Finite_trace t1 r1, Finite_trace t2 r2 -> (
         r1 == r2
       )
       | _, _ -> False))

let hyperprop_pprog1 ctx tr1 tr2 =
  let bh = beh_giio (__reify_IIOwp ((fun () -> pprog1 AllActions ctx))) [] in
 // reveal_opaque (`%beh) beh;
 // assert (beh ws == bh); 
  match tr1, tr2 with
  | Finite_trace t1 r1, Finite_trace t2 r2 -> begin
    assert (Finite_trace t1 r1 `member_of` bh ==> r1 == 7) by (
      norm [delta_only [`%beh;`%member_of;`%beh_giio];iota];
      //norm [delta_only [`%link1;`%pprog1];iota];
     dump "H");
    admit ();
    assert (r2 == 7);
    assert (r1 == r2)
  end
  | _, _ -> assume (False)
