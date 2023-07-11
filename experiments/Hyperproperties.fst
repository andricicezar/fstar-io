module Hyperproperties

open FStar.Tactics
open ExtraTactics
open FStar.Ghost
open FStar.String


open FStar.Tactics
open FStar.List.Tot

open MIO
open MIO.Behavior
open BeyondCriteria
open Compiler.Model

(** this is a second definition of reify that is in the Tot effect **)
assume val _tot_reify_MIOwp (#a:Type) (#wp:Hist.hist a) (#fl:erased tflag) ($f:unit -> MIOwp a fl wp) : Tot (dm_gmio a fl wp)

(** ** Non-interference theorems for ctx **)
(* Termination-insensitive noninterference (TINI) definition took from Beyond Full Abstraction
    TINI = {b | ∀t1 t2∈b. (t1 terminating ∧ t2 terminating
                          ∧ pub-inputs(t1)=pub-inputs(t2))
                          ⇒ pub-events(t1)=pub-events(t2)} 
                          
   A trace in our case has 2 components, the history and the local trace * result.
   The ctx is called on an existing history and it produces its own local trace and result.

   The public inputs come from two dirrection:
   1) there are the public inputs the pi and the contracts leak about the history
   2) there are public inputs from the environment. each time the context does an IO action,
      it gets a result from the environment.

   The public events are all the events produced by the context (local trace) and its result.
   So, if the public inputs are the same, then the local trace and the result should be equal.

Example:
let ctx = match Openfile "asd.tx" with
          | Inl fd -> write fd "text"; 7
          | Inr _ -> 42

pi = max 2 openfiles
h1 = [EOpenfile]            lt1 = [EOpenfile;EWrite] r1 = 7
h2 = [EOpenfile;Eopenfile]  lt2 = []                 r2 = 42
*)

let make_rc_tree (#a:Type) (#b:Type) (rc:rc_typ a b) : tree pck_rc =
  Node (| a, b, rc |) Leaf Leaf

type event_dtuple = (bool & cmd:io_cmds & (arg:io_sig.args cmd) & io_sig.res cmd arg)
val (!) : event -> event_dtuple
let (!) = destruct_event

(** the context can learn more things after it does IO actions **)
let hist_public_inputs (#pi:policy_spec) (phi:policy pi) (rc:rc_typ 'a 'b) (h1 h2 ctx_lt:trace) : Type0 =
  (* TODO: there is no need to write forall cmds. one can restrict it for the heads of the two traces *)
  (forall cmd arg. phi (rev ctx_lt @ h1) cmd arg == phi (rev ctx_lt @ h2) cmd arg) /\
  (** the runtime checks can be partially applied, so we have to
      take in consideration when were they first partially applied
      and when were they completely applied. The ctx has access to 
      effectful runtime checks of type: eff_rc_typ = 'a -> 'b -> MIO bool **)
  (forall (i:nat) x y. i < length ctx_lt ==> (
    let call1, call2 = splitAt i ctx_lt in
    rc x (rev call1 @ h1) y call2 == rc x (rev call1 @ h2) y call2))

(** the call of an IO action is an output 
    from the context to the environment **)
let ctx_output (e:event_dtuple) : cmd:io_cmds & io_sig.args cmd =
  let (| _, cmd, arg, _ |) = e in
  (| cmd, arg |)

(** the result of an IO action is an input
    from the environment to the context **)
let env_input (e:event_dtuple) : io_sig.res (Mkdtuple4?._2 e) (Mkdtuple4?._3 e) =
  let (| _, cmd, arg, res |) = e in
  res

let rec ni_traces (pi:policy_spec) (phi:policy pi) (rc:rc_typ 'a 'b) (r1 r2:int) (h1 h2 acc_lt lt1 lt2:trace) : 
  GTot Type0 (decreases lt1) =
  hist_public_inputs phi rc h1 h2 acc_lt ==> (
    match lt1, lt2 with
    | [], [] -> r1 == r2
    | hd1::t1, hd2::t2 -> begin
        (ctx_output !hd1 == ctx_output !hd2 /\
        (** determinacy **)
        (env_input !hd1 == env_input !hd2 ==> ni_traces pi phi rc r1 r2 h1 h2 (acc_lt@[hd1]) t1 t2))
    end
    | _, _ -> False)


(* 
TODO:
- [ ] is it the theorem we want?
- [ ] can we write it in a more simple way to be easier to prove in F*?
- [ ] prove 
*)
val ni : 
  pi : policy_spec ->
  phi : policy pi ->
  (** for any runtime check **)
  rc : (rc_typ 'a 'b) ->
  (** the ctx is in a first-order setting. I don't think it matters **)
  ctx: (fl:erased tflag -> pi:erased policy_spec -> acts fl pi false -> typ_eff_rcs fl (make_rc_tree rc) -> unit -> MIO int fl (fun _ -> True) (fun _ _ _ -> True)) ->
  Lemma (
                                  (** one has to instantiate the ctx to be able to call beh **)
    let bh = beh_ctx #(fun _ -> True) (ctx AllActions pi (inst_io_cmds phi) (make_rcs_eff (make_rc_tree rc))) in
    forall h1 lt1 r1 h2 lt2 r2. 
      (h1, Finite_trace lt1 r1) `pt_mem` bh /\ 
      (h2, Finite_trace lt2 r2) `pt_mem` bh ==> 
      ni_traces pi phi rc r1 r2 h1 h2 [] lt1 lt2)

// parametricity ==>
//   ctx == Return r
//   ctx == dm_gmio_bind (inst_io_cmds pi cmd arg) cont
//   ctx == dm_gmio_bind (eff_rc x) (fun eff_rc' -> dm_gmio_bind cont1 (fun y -> dm_gmio_bind (eff_rc' y) cont2)
// with that, one can do induction on the ctx to prove the non-interference
// there is no axiom/law for erased
// pi is Tot, it does not matter that it is erased
//

(**** Types using the gmio directly **)

type gmio_acts (fl:erased tflag) (pi:policy_spec) (caller:bool) =
  (cmd : io_cmds) ->
  (arg : io_sig.args cmd) ->
  dm_gmio (io_resm cmd arg) fl
    (to_hist (fun _ -> True)
      (fun h r lt ->
        enforced_locally pi h lt /\
        (match r with
        | Inr Contract_failure -> lt == []
        | r' -> lt == [convert_call_to_event caller cmd arg r'])))

val gmio_inst_cmds : #pi:policy_spec -> phi:policy pi -> Tot (gmio_acts AllActions pi false)
let gmio_inst_cmds phi cmd arg =
  _tot_reify_MIOwp (fun () -> inst_io_cmds phi cmd arg)

// Binary parametricity for contexts, picking the trivial relation for erased.
// It says that all contexts are parametric.

let gmio_eff_rc_typ_cont_wp (fl:erased tflag) (#t1:Type u#a) (#t2:Type u#b) (rc:rc_typ t1 t2) (x:t1) (y:t2) (initial_h:erased trace) =
  to_hist
    (fun h -> initial_h `suffix_of` h)
    (eff_rc_typ_cont_post rc initial_h x y)

type gmio_eff_rc_typ_cont (fl:erased tflag) (t1:Type u#a) (t2:Type u#b) (rc:rc_typ t1 t2) (x:t1) (initial_h:erased trace) =
  y:t2 -> (dm_gmio bool fl (gmio_eff_rc_typ_cont_wp fl rc x y initial_h))
  
type gmio_eff_rc_typ (fl:erased tflag) (#t1 #t2:Type) (rc:rc_typ t1 t2) =
  x:t1 -> (dm_gmio (initial_h:(erased trace) & gmio_eff_rc_typ_cont fl t1 t2 rc x initial_h) fl (to_hist (fun _ -> True) (fun h (| initial_h, _ |) lt -> h == reveal initial_h /\ lt == [])))

#set-options "--print_effect_args"

val reify_eff_rc_cont : #fl:erased tflag -> #t1:Type -> #t2:Type -> #rc:rc_typ t1 t2 -> x:t1 -> initial_h:erased trace -> eff_rc_typ_cont fl t1 t2 rc x initial_h -> gmio_eff_rc_typ_cont fl t1 t2 rc x initial_h
let reify_eff_rc_cont #fl #t1 #t2 #rc x initial_h cont (y:t2) =
  _tot_reify_MIOwp (fun () -> cont y)

val reify_eff_rc : #fl:erased tflag -> #t1:Type -> #t2:Type -> #rc:rc_typ t1 t2 -> eff_rc_typ fl rc -> gmio_eff_rc_typ fl rc
let reify_eff_rc #fl #t1 #t2 #rc eff_rc x =
  admit ();
  dm_gmio_bind
    (initial_h:(erased trace) & eff_rc_typ_cont fl t1 t2 rc x initial_h)
    (initial_h:(erased trace) & gmio_eff_rc_typ_cont fl t1 t2 rc x initial_h)
    fl NoActions
    (to_hist (fun _ -> True) (fun h (| initial_h, _ |) lt -> h == reveal initial_h /\ lt == []))
    (fun (| h, cont |) -> hist_return (| h, reify_eff_rc_cont x h cont |))
    (_tot_reify_MIOwp (fun () -> eff_rc x))
    (fun (| h, cont |) -> dm_gmio_return _ (| h, reify_eff_rc_cont x h cont |))

type gmio_pck_eff_rc (fl:erased tflag) = pck:pck_rc & gmio_eff_rc_typ fl (Mkdtuple3?._3 pck)

type gmio_typ_eff_rcs (fl:erased tflag) (rcs:tree pck_rc) = 
  eff_rcs:(tree (gmio_pck_eff_rc fl)){
    equal_trees rcs (map_tree eff_rcs dfst)}

type gmio_ctx (rc:rc_typ unit int) =
  fl:erased tflag -> pi:erased policy_spec -> gmio_acts fl pi -> gmio_typ_eff_rcs fl (make_rc_tree rc) -> unit -> dm_gmio int fl (to_hist (fun _ -> True) (fun _ _ _ -> True))

val bind1  : 
  #a: Type ->
  #b: Type ->
  v: dm_gmio a AllActions trivial_hist ->
  f: (x: a -> dm_gmio b AllActions trivial_hist) ->
  Tot (dm_gmio b AllActions trivial_hist)
let bind1 #a #b = dm_gmio_bind a b AllActions AllActions trivial_hist (fun _ -> trivial_hist)

let third
  (eff_rc:gmio_eff_rc_typ AllActions #'a #'b 'rc)
  (cont1:dm_gmio 'b AllActions trivial_hist)
  (cont2: _ -> dm_gmio 'c AllActions trivial_hist) 
  x :
  dm_gmio 'c AllActions trivial_hist =
  admit ();
  dm_gmio_subcomp 'c AllActions AllActions _ trivial_hist (
    dm_gmio_bind 
      (initial_h:(erased trace) & gmio_eff_rc_typ_cont AllActions 'a 'b 'rc x initial_h)
      'c
      AllActions
      AllActions
      trivial_hist
      (fun (| initial_h, _ |) -> hist_bind trivial_hist (fun y -> hist_bind (gmio_eff_rc_typ_cont_wp AllActions 'rc x y initial_h) (fun _ -> trivial_hist)))
      (eff_rc x) 
      (fun (| initial_h, eff_rc' |) -> 
        dm_gmio_bind _ _ _ _ trivial_hist (fun y -> hist_bind (gmio_eff_rc_typ_cont_wp AllActions 'rc x y initial_h) (fun _ -> trivial_hist))
          cont1 
	  (fun y -> 
	    dm_gmio_bind _ _ _ _ (gmio_eff_rc_typ_cont_wp AllActions 'rc x y initial_h) (fun _ -> trivial_hist)
	      (eff_rc' y) 
	      cont2)))

let rec only_pi_and_rc
  (pi:policy_spec)
  (gmio_cmds:gmio_acts AllActions pi)
  (eff_rc:gmio_eff_rc_typ AllActions #'a #'b 'rc)
  (m:dm_gmio 'c AllActions trivial_hist) :
  GTot Type0 (decreases m) =
  (exists r. m == Return r) 
  \/
  (exists cmd arg (cont:io_resm cmd arg -> dm_gmio 'c AllActions trivial_hist).
    (forall r.  (cont r) << m /\ only_pi_and_rc pi gmio_cmds eff_rc (cont r)) ==>
    (m == (bind1 (gmio_cmds cmd arg) cont)))
  \/
  (exists x (cont1:dm_gmio 'b AllActions trivial_hist) (cont2: _ -> dm_gmio 'c AllActions trivial_hist). 
    ((cont1 << m /\ only_pi_and_rc pi gmio_cmds eff_rc cont1) /\
    (forall r. (cont2 r) << m /\ only_pi_and_rc pi gmio_cmds eff_rc (cont2 r))) ==> 
    m == third eff_rc cont1 cont2 x)

(** *** Effect polymorphism *)
noeq type monad = {
  m    : Type u#(max 1 a) -> Type u#(max 1 a);
  ret  : #a:Type -> a -> m a;
  (* TODO: bind should be polymorphic in two universes *)
  bind : #a:Type -> #b:Type -> m a -> (a -> m b) -> m b;
  (* We don't want acts to be part of this monad because we want to provide different versions *)
}

let dm_gmio' (fl:erased tflag) (pi:policy_spec) (a:Type) = dm_gmio a fl (pi_as_hist pi)

let as_gmio_dm (w:dm_gmio' 'f 'p 'a) : dm_gmio 'a 'f (pi_as_hist 'p) = 
  let tree : mio 'a = w in
  assert (pi_as_hist 'p `Hist.hist_ord` MIO.dm_gmio_theta tree);
  tree

let as_gmio_dm' (w:dm_gmio 'a 'f (pi_as_hist 'p)) : dm_gmio' 'f 'p 'a = w

let lemma_bind_pi_implies_pi (#a #b:Type) (pi:policy_spec) : 
  Lemma (pi_as_hist #b pi `hist_ord` (hist_bind (pi_as_hist #a pi) (fun (_:a) -> pi_as_hist pi))) = admit ()

let dm_gmio_return' (a:Type) (fl:erased tflag) (x:a) : dm_gmio a fl (hist_return x) by (compute ()) =
  dm_mio_return a x

let dm_mon (fl:erased tflag) (pi:policy_spec) : monad = {
  m = dm_gmio' fl pi;
  ret = (fun (x:'a) -> dm_gmio_return' 'a fl x);
  bind = (fun (m:dm_gmio' fl pi 'a) (k:'a -> dm_gmio' fl pi 'b) -> 
    let wp : Hist.hist 'b = Hist.hist_bind (pi_as_hist #'a pi) (fun _ -> pi_as_hist pi) in 
    let tr : dm_gmio 'b fl wp = dm_gmio_bind _ _ _ _ _ _ (as_gmio_dm m) (fun x -> as_gmio_dm (k x)) in
    lemma_bind_pi_implies_pi #'a #'b pi;
    let w = dm_gmio_subcomp 'b _ _ wp (pi_as_hist pi) tr in
    as_gmio_dm' w)
}

type effpoly_rc (mon:monad) = (unit -> mon.m (int -> mon.m (Universe.raise_t (bool <: Type))))
  
type effpoly_ctx =
  (mon:monad) -> io_act:(cmd:io_cmds -> arg:io_sig.args cmd -> mon.m (Universe.raise_t (io_sig.res cmd arg))) -> unit -> mon.m (Universe.raise_t (int <: Type))

#set-options "--print_universes"

(**
val law : rc:rc_typ unit int -> effpoly_ctx -> gmio_ctx rc
let law rc effctx fl pi io_acts effrc =
  effctx (dm_mon fl pi) io_acts
**)

(** *** Parametricity **)
// Type of contexts
let ctx_type rc =
  fl:erased tflag -> pi:erased policy_spec -> typ_io_cmds fl pi -> typ_eff_rcs fl (make_rc_tree rc) -> unit -> dm_gmio int fl (to_hist (fun _ -> True) (fun _ _ _ -> True))

assume val typ_io_cmds_r :
  fl0: erased tflag -> fl1: erased tflag -> // erased_r is trivial
  pi0: erased policy_spec -> pi1: erased policy_spec ->
  io0: typ_io_cmds fl0 pi0 -> io1: typ_io_cmds fl1 pi1 ->
  Type0
// let typ_io_cmds_r fl0 fl1 pi0 pi1 io0 io1 = io0 == io1
// We probably need something recursive that inspects io0 and io1
// The situation is actually worse since these are also effectful things

assume val typ_eff_rcs_r :
  rt: _ ->
  fl0: erased tflag -> fl1: erased tflag -> // erased_r is trivial
  t0: typ_eff_rcs fl0 rt ->
  t1: typ_eff_rcs fl1 rt ->
  Type0
// Similar to the above

// Relation of contexts (it cannot type check because of the effect, but would the monad be enough?)
let ctx_type_r rc (ctx0 ctx1 : ctx_type rc) =
  fl0: erased tflag -> fl1: erased tflag -> // erased_r is trivial
  pi0: erased policy_spec -> pi1: erased policy_spec ->
  io0: typ_io_cmds fl0 pi0 -> io1: typ_io_cmds fl1 pi1 ->
  ior: typ_io_cmds_r fl0 fl1 pi0 pi1 io0 io1 ->
  t0: typ_eff_rcs fl0 (make_rc_tree rc) ->
  t1: typ_eff_rcs fl1 (make_rc_tree rc) ->
  tr: typ_eff_rcs_r _ fl0 fl1 t0 t1 ->
  // ignoring unit
  // Assuming the relation on dm_gmio is equality
  Lemma (ctx0 fl0 pi0 io0 t0 () == ctx1 fl1 pi1 io1 t1 ())

// typ_io_cmds NoAction = Inr Contract_failure
// typ_io_cmds AllActions = let h = get_Trace () in if pi h cmd arg then io_cmds cmd arg else Inr Contract_failure

assume val ctx_param :
  rc: rc_typ 'a 'b ->
  ctx0: ctx_type rc -> ctx1: ctx_type rc ->
  ctx_type_r rc ctx0 ctx1

(*

val bind1  : 
  #a: Type ->
  #b: Type ->
  v: dm_gmio a AllActions trivial_hist ->
  f: (x: a -> dm_gmio b AllActions trivial_hist) ->
  Tot (dm_gmio b AllActions trivial_hist)
let bind1 #a #b = dm_gmio_bind a b AllActions AllActions trivial_hist (fun _ -> trivial_hist)

let rec only_pi_and_rc (pi:policy_spec) (eff_rc:eff_rc_typ AllActions #'a #'b 'rc) (m:dm_gmio 'c AllActions trivial_hist) : GTot Type0 (decreases m) =
  
  (exists r. m == Return r) 
  \/
  (exists cmd arg (cont:io_resm cmd arg -> dm_gmio 'c AllActions trivial_hist).
    (forall r.  (cont r) << m /\ only_pi_and_rc pi eff_rc (cont r)) ==>
    (m == (bind1 (__reify_MIOwp (fun () -> inst_io_cmds pi cmd arg <: MIOwp (io_resm cmd arg) AllActions trivial_hist)) cont)))
  \/
  (exists x (cont1:dm_gmio 'b AllActions trivial_hist) (cont2: _ -> dm_gmio 'c AllActions trivial_hist). 
    ((cont1 << m /\ only_pi_and_rc pi eff_rc cont1) /\
    (forall r. (cont2 r) << m /\ only_pi_and_rc pi eff_rc (cont2 r))) ==> 
    m == dm_gmio_bind _ _ AllActions AllActions _ _ (__reify_MIOwp (fun () -> eff_rc x)) (fun (| _, eff_rc' |) -> 
               bind1 cont1 (fun y -> 
                 bind1 (__reify_MIOwp (fun () -> eff_rc' y)) cont2)))
*)  

let ni pi rc ctx = admit ()














(*** Old **)

(** There are many difficulties on trying to state Hyperproperties
about whole/partial source programs. **)

(** Whole programs **)

let read_content (fnm:string) : MIO (r:(resexn string){~(r == Inr Contract_failure)}) IOActions
  (requires (fun _ -> True))
  (ensures (fun _ r lt -> 
    (Inr? r /\ lt == [EOpenfile fnm (Inr (Inr?.v r))]) \/
    (exists fd. lt == [EOpenfile fnm (Inl fd);ERead fd r])
    )) =
  match static_cmd Openfile fnm with
  | Inl fd -> static_cmd Read fd
  | Inr err -> Inr err

let rec get_fd_content (fd:file_descr) (t:MIO.Sig.trace) : option string =
  match t with
  | [] -> None
  | (ERead fd' (Inl msg')) :: tl -> if fd = fd' then (Some msg') else (get_fd_content fd tl)
  | (ERead fd' (Inr msg')) :: tl -> if fd = fd' then None else (get_fd_content fd tl)
  | _ :: tl -> get_fd_content fd tl
  
let rec get_content (fnm:string) (t:MIO.Sig.trace) : option string =
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

let whole1 () : MIO int AllActions 
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
val leak_the_same : trace -> trace -> pi:policy_spec -> rc:('a -> trace -> 'b -> trace -> bool) -> Type0
let leak_the_same h1 h2 pi rc =
  // for each valid local trace of h1,
  // there exists a valid local trace for h2
  // both leaking the same information through pi and rc
  (forall lt1. enforced_locally pi h1 lt1 ==> 
    (exists lt2. enforced_locally pi h2 lt2 /\
      (forall cmd arg. pi cmd arg (rev lt1 @ h1) == pi cmd arg (rev lt2 @ h2)) /\
      (* not strong enough *)
      (forall arg res. rc arg h1 res lt1 == rc arg h2 res lt2)))

val tini : 
  pi : policy_spec ->
  (** for any runtime check **)
  rc : ('a -> trace -> 'b -> trace -> bool) ->
  (** the ctx is in a first-order setting. I don't think it matters **)
  ctx: (fl:erased tflag -> pi:erased policy_spec -> typ_io_cmds fl pi -> typ_eff_rcs fl (make_rc_tree rc) -> unit -> MIO int fl (fun _ -> True) (fun _ _ _ -> True)) ->
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
  pi : policy_spec ->
  (** for any runtime check **)
  rc : ('a -> trace -> 'b -> trace -> bool) ->
  (** the ctx is in a first-order setting. I don't think it matters **)
  ctx: (fl:erased tflag -> pi:erased policy_spec -> typ_io_cmds fl pi -> typ_eff_rcs fl (make_rc_tree rc) -> unit -> MIO int fl (fun _ -> True) (fun _ _ _ -> True)) ->
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
  ctx:(fl:erased tflag -> unit -> MIO int fl (fun _ -> True) (fun _ _ _ -> True)) ->
  Lemma (
    let bh = beh_ctx #(fun _ -> True) (ctx AllActions) in
    forall t1 t2. t1 `pt_mem` bh /\ t2 `pt_mem` bh ==>
      (exists t3. t3 `pt_mem` bh /\ 
             fst t1 == fst t3 /\ // histories are equal
             snd t2 == snd t3   // local traces are equal
             ))
             
let gni_v0 ctx =
  let bh = beh_ctx #(fun _ -> True) (ctx AllActions) in
  let reified_ctx : dm_gmio int AllActions (to_hist (fun _ -> True) (fun _ _ _ -> True)) = __reify_MIOwp (ctx AllActions) in
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
      //assert ((snd t2) `member_of #event` beh_gmio reified_ctx (fst t2)); (* not sure why it does not work *)
      assume ((snd t2) `member_of` beh_gmio reified_ctx newH); (** folds into: **)
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
  ctx:(unit -> MIO int fl (fun _ -> True) (fun _ _ _ -> True)) ->
  MIO int (fl + IOActions) (fun _ -> True) (fun _ _ _ -> True) 
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
  let bh = beh_gmio (__reify_MIOwp ((fun () -> pprog1 AllActions ctx))) [] in
 // reveal_opaque (`%beh) beh;
 // assert (beh ws == bh); 
  match tr1, tr2 with
  | Finite_trace t1 r1, Finite_trace t2 r2 -> begin
    assert (Finite_trace t1 r1 `member_of` bh ==> r1 == 7) by (
      norm [delta_only [`%beh;`%member_of;`%beh_gmio];iota];
      //norm [delta_only [`%link1;`%pprog1];iota];
     dump "H");
    admit ();
    assert (r2 == 7);
    assert (r1 == r2)
  end
  | _, _ -> assume (False)
