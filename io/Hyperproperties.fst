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

(* h is non-interfering for flag polymorphic simplified ctx
  -- should be true since this ctx cannot do any actions **)
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

open Compiler.Languages
open FStar.List.Tot

val leak_the_same : trace -> trace -> pi:monitorable_prop -> rc:('a -> trace -> 'b -> trace -> bool) -> Type0
let leak_the_same h1 h2 pi rc =
  // if there is a valid local trace for h1 that leaks information
  // then there is a valid local trace for h2 that leaks the same information
  (forall lt1. enforced_locally pi h1 lt1 ==> 
    (exists lt2. enforced_locally pi h2 lt2 /\
      (forall cmd arg. pi cmd arg (rev lt1 @ h1) == pi cmd arg (rev lt2 @ h2)) /\
      (forall x y. rc x h1 y lt1 == rc x h2 y lt2)))

val gni : 
  pi : monitorable_prop ->
  rc : ('a -> trace -> 'b -> trace -> bool) ->
  ctx: (fl:erased tflag -> pi:erased monitorable_prop -> unit -> IIO int fl (fun _ -> True) (fun _ _ _ -> True)) ->
  Lemma (
    let bh = beh_ctx #(fun _ -> True) (ctx AllActions pi) in
    forall h1 lt1 r1 h2 lt2 r2. 
      (h1, Finite_trace lt1 r1) `pt_mem` bh /\ 
      (h2, Finite_trace lt2 r2) `pt_mem` bh /\
      leak_the_same h1 h2 pi rc
    ==> (exists h3 lt3 r3. (h3, Finite_trace lt3 r3) `pt_mem` bh /\ 
                      h1 == h3 /\ lt2 == lt3 /\ r2  == r3))

(* h is non-interfering for flag polymorphic ctx
  -- should be true since a flag polymorphic ctx can not do any actions 
  
  the type of ctx is simplified here:
    * unit, int should be arbitrary types
    * it can be HO
    * ctx should also take instrumented actions
    * ctx should also take the contracts *)
val gni_v1 : 
  #pre:_ ->
  ctx:(fl:erased tflag -> unit -> IIO int fl pre (fun _ _ _ -> True)) ->
  #a:Type ->
  secrets:(h:_{pre h} -> a) ->
  Lemma (
    let bh = beh_ctx #pre (ctx AllActions) in
    forall t1 t2. t1 `pt_mem` bh /\ t2 `pt_mem` bh ==>
      (exists t3. t3 `pt_mem` bh /\ secrets (fst t1) == secrets (fst t3) /\ snd t2 == snd t3))

let gni_v1 #pre ctx #a secrets = 
  let bh = beh_ctx #pre (ctx AllActions) in
  let reified_ctx : dm_giio int AllActions (to_hist pre (fun _ _ _ -> True)) = __reify_IIOwp (ctx AllActions) in
  introduce forall (t1 t2:prefixed_trace pre).
  t1 `pt_mem` bh /\ t2 `pt_mem` bh 
  ==> (exists (t3:prefixed_trace pre). t3 `pt_mem` bh /\ secrets (fst t1) == secrets (fst t3) /\ snd t2 == snd t3) 
  with begin
    introduce t1 `pt_mem` bh /\ t2 `pt_mem` bh
    ==> (exists (t3:prefixed_trace pre). t3 `pt_mem` bh /\ secrets (fst t1) == secrets (fst t3) /\ snd t2 == snd t3)
    with _. begin
      let newH = (fst t1) in
      let t3 : prefixed_trace pre = (newH, snd t2) in 
      assert (t2 `pt_mem` bh); (** unfolds to: **)
      assert ((snd t2) `member_of` beh_giio reified_ctx (fst t2)); 
      assume ((snd t2) `member_of` beh_giio reified_ctx newH); (** folds into: **)
      assert (t3 `pt_mem` bh);
      assert (secrets (fst t1) == secrets (fst t3));
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
