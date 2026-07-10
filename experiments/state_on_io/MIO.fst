module MIO

open FStar.Tactics
open FStar.Ghost

include MIO.Sig
open DMFree
open GuardedDMFree

(** * The MIO effect indexed by a flag, in the style of sciostar/MIO.fst.

    The underlying representation of `mio_dm` is the free monad over
    `cmd_sum guard_cmd (mio_cmds mst)` on the first channel (the second
    channel is instantiated with the empty signature): guard commands
    (GCmd) play the role that `PartialCall` plays in the sciostar
    representation. Therefore the flag predicate `satisfies` is defined on
    this guarded carrier and always allows guard commands, no matter the
    flag. **)

(** The carrier of mio_dm: mio extended with guard commands. **)
type gmio (mst:mstate) (a:Type) = free (cmd_sum guard_cmd (mio_cmds mst)) (empty_cmds u#0 u#0) a

(** **** Flag **)
noeq
type tflag = | NoOps | GetMStateOps | IOOps | AllOps

(** Which commands does a flag allow? Guards (CmdL) are always allowed,
    no matter the flag: they play the role of PartialCall in sciostar.
    (Note: destructing the command inside a `Call` pattern of `satisfies`
    trips universe inference, so the dispatch lives in this helper where
    `r` is a regular binder.) **)
let allows #mst (flag:tflag) (#r:Type0) (op:cmd_sum guard_cmd (mio_cmds mst) r) : Type0 =
  match op with
  | CmdL _        -> True
  | CmdR (CmdL _) -> (match flag with | AllOps | IOOps -> True | _ -> False)
  | CmdR (CmdR _) -> (match flag with | AllOps | GetMStateOps -> True | _ -> False)

let rec satisfies #mst #a (m:gmio mst a) (flag:tflag) : Tot Type0 (decreases m) =
  match flag, m with
  | AllOps, _      -> True
  | _, Return _    -> True
  | _, Call1 _ op k -> allows flag op /\ (forall r. satisfies (k r) flag)
  (* the second channel carries the empty signature: no Call2 node exists *)
  | _, Call2 _ op k -> True

let (⊕) (flag1:tflag) (flag2:tflag) : tflag =
  match flag1, flag2 with
  | NoOps, NoOps -> NoOps
  | NoOps, fl -> fl
  | fl, NoOps -> fl
  | GetMStateOps, GetMStateOps -> GetMStateOps
  | IOOps, IOOps -> IOOps
  | _, _ -> AllOps

let (≼) (flag1:tflag) (flag2:tflag) : Type0 =
  match flag1, flag2 with
  | NoOps, _ -> True
  | GetMStateOps, NoOps -> False
  | GetMStateOps, IOOps -> False
  | GetMStateOps, _ -> True
  | IOOps, NoOps -> False
  | IOOps, GetMStateOps -> False
  | IOOps, _ -> True
  | AllOps, AllOps -> True
  | AllOps, _ -> False

let plus_compat_le (f1 f2 : tflag) : Lemma (f1 ≼ (f1⊕f2)) = ()
let plus_comm      (f1 f2 : tflag) : Lemma (f1⊕f2 == f2⊕f1) = ()

let allows_le #mst (f1:tflag) (f2:tflag{f1 ≼ f2}) (#r:Type0) (op:cmd_sum guard_cmd (mio_cmds mst) r) :
  Lemma (allows f1 op ==> allows f2 op) = ()

let rec sat_le #mst (f1:tflag) (f2:tflag{f1 ≼ f2}) (m : gmio mst 'a) :
  Lemma (ensures satisfies m f1 ==> satisfies m f2) (decreases m) =
  match m with
  | Return _ -> ()
  | Call1 _ op k ->
    allows_le f1 f2 op;
    Classical.forall_intro
     ((fun r -> sat_le f1 f2 (k r)) <: r:_ -> Lemma (satisfies (k r) f1 ==> satisfies (k r) f2))
  | Call2 _ op k -> ()

let rec sat_bind #mst (fl:tflag) (v : gmio mst 'a) (f : 'a -> gmio mst 'b)
  : Lemma (ensures v `satisfies` fl /\ (forall x. f x `satisfies` fl) ==> free_bind v f `satisfies` fl)
          (decreases v)
  =
  match v with
  | Return _ -> ()
  | Call1 _ op k ->
    Classical.forall_intro
     ((fun r -> sat_bind fl (k r) f) <: r:_ -> Lemma ((k r) `satisfies` fl /\ (forall x. f x `satisfies` fl) ==> free_bind (k r) f `satisfies` fl))
  | Call2 _ op k -> ()

let sat_bind_add #mst (fl_v fl_f:tflag) (v : gmio mst 'a) (f : 'a -> gmio mst 'b)
  : Lemma (v `satisfies` fl_v /\ (forall x. f x `satisfies` fl_f) ==> free_bind v f `satisfies` (fl_v ⊕ fl_f))
  =
  sat_le fl_v (fl_v ⊕ fl_f) v;
  let aux x : Lemma (f x `satisfies` fl_f ==> f x `satisfies` (fl_v ⊕ fl_f)) =
    sat_le fl_f (fl_v ⊕ fl_f) (f x)
  in
  Classical.forall_intro aux;
  sat_bind (fl_v ⊕ fl_f) v f

let mio_dm_bind_is_free_bind (mst:mstate) #a #b
  (wp_v : hist #io_event a)
  (wp_f : a -> hist #io_event b)
  (v : mio_dm mst a wp_v)
  (f : (x:a -> mio_dm mst b (wp_f x)))
: Lemma (mio_dm_bind mst wp_v wp_f v f == free_bind v f)
=
  let r = mio_dm_bind mst wp_v wp_f v f in
  assert (r == free_bind v f)

(** ** Defining F* Effect **)

type dm_gmio (a:Type) (mst:mstate) (flag:erased tflag) (wp:hist #io_event a) =
  t:(mio_dm mst a wp){t `satisfies` flag}

let dm_gmio_theta #mst #a (m:gmio mst a) : hist #io_event a =
  theta (cmd_wp_sum guard_cmd_wp mio_cwp) empty_cmd_wp m

let dm_gmio_return (a:Type) (x:a) (mst:mstate) : dm_gmio a mst NoOps (hist_return x) by (compute ()) =
  mio_dm_return mst x

val dm_gmio_bind  :
  a: Type ->
  b: Type ->
  mst: mstate ->
  flag_v : erased tflag ->
  wp_v: hist #io_event a ->
  flag_f : erased tflag ->
  wp_f: (a -> hist #io_event b) ->
  v: dm_gmio a mst flag_v wp_v ->
  f: (x: a -> dm_gmio b mst flag_f (wp_f x)) ->
  Tot (dm_gmio b mst (flag_v ⊕ flag_f) (hist_bind wp_v wp_f))

let dm_gmio_bind a b mst flag_v wp_v flag_f wp_f v f : (dm_gmio b mst (flag_v ⊕ flag_f) (hist_bind wp_v wp_f)) =
  let r = mio_dm_bind mst wp_v wp_f v f in
  sat_bind_add flag_v flag_f v f;
  mio_dm_bind_is_free_bind mst wp_v wp_f v f;
  assert (free_bind v f `satisfies` (flag_v ⊕ flag_f));
  r

val dm_gmio_subcomp :
  a: Type ->
  mst:mstate ->
  flag1 : erased tflag ->
  wp1: hist #io_event a ->
  flag2 : erased tflag ->
  wp2: hist #io_event a ->
  f: dm_gmio a mst flag1 wp1 ->
  Pure (dm_gmio a mst flag2 wp2) ((flag1 ≼ flag2) /\ wp1 ⊑ wp2) (fun _ -> True)
let dm_gmio_subcomp a mst flag1 wp1 flag2 wp2 f =
  sat_le flag1 flag2 f;
  mio_dm_subcomp mst wp1 wp2 f

let dm_gmio_if_then_else (a : Type u#a) (mst:mstate)
  (fl1 : erased tflag) (wp1 : hist #io_event a)
  (fl2 : erased tflag) (wp2 : hist #io_event a)
  (f : dm_gmio a mst fl1 wp1) (g : dm_gmio a mst fl2 wp2) (b : bool) : Type =
  dm_gmio a mst (fl1 ⊕ fl2) (hist_if_then_else wp1 wp2 b)

total
reifiable
reflectable
effect {
  MIOwp (a:Type) ([@@@effect_param] mst:mstate) (flag:erased tflag) (wp : hist #io_event a)
  with {
       repr       = dm_gmio
     ; return     = dm_gmio_return
     ; bind       = dm_gmio_bind
     ; subcomp    = dm_gmio_subcomp
     ; if_then_else = dm_gmio_if_then_else
     }
}

(** Guards (the analogue of sciostar's PartialCall) satisfy any flag,
    in particular NoOps. **)
let dm_gmio_guard_return
  (mst:mstate) (pre:pure_pre) : dm_gmio (squash pre) mst NoOps (guard_wp pre) by (compute ()) =
  mio_dm_guard_return mst pre

(** Note: like in GuardedDMFree.lift_pure_gdm, the subcomp query here is
    sensitive to quantifier instantiation; it only goes through when split
    off from the rest of the VC, with ifuel 2 and the WP inclusion asserted
    explicitly. **)
#push-options "--z3rlimit 40 --ifuel 2 --split_queries always"
val lift_pure_dm_gmio :
  a: Type u#a ->
  [@@@effect_param] mst: mstate ->
  w: pure_wp a ->
  f: (eqtype_as_type unit -> PURE a w) ->
  Tot (dm_gmio a mst NoOps (wp_lift_pure_hist w))
let lift_pure_dm_gmio a mst w f =
  lemma_wp_lift_pure_hist_implies_as_requires #a #io_event w;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall u#a ();
  let lhs : dm_gmio _ mst NoOps (guard_wp #io_event (as_requires w)) =
    dm_gmio_guard_return mst (as_requires w) in
  let rhs (_:squash (as_requires w)) : dm_gmio a mst NoOps (wp_lift_pure_hist w) =
    let r = f () in
    dm_gmio_return a r mst in
  let m = dm_gmio_bind _ a mst NoOps (guard_wp #io_event (as_requires w)) NoOps (fun _ -> wp_lift_pure_hist w) lhs rhs in
  assert (hist_bind (guard_wp #io_event (as_requires w)) (fun _ -> wp_lift_pure_hist w) ⊑ wp_lift_pure_hist #a #io_event w);
  dm_gmio_subcomp a mst NoOps _ NoOps _ m
#pop-options

sub_effect PURE ~> MIOwp = lift_pure_dm_gmio

effect MIO
  (a:Type)
  (fl:erased tflag)
  (mst:mstate)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  MIOwp a mst fl (to_hist pre post)

(** ** Actions **)

#push-options "--z3rlimit 20"
let static_op
  (#mst:mstate)
  (c:caller)
  (#r:Type0)
  (op : io_cmds r) :
  MIO r IOOps mst
    (requires (fun h -> io_pre op h))
    (ensures (fun h (res:r) lt ->
        io_post op res /\
        lt == [convert_call_to_event c op res])) =
  MIOwp?.reflect (gdm_cmd1 mio_cwp empty_cmd_wp c (CmdL op) <: dm_gmio r mst IOOps (to_hist
    (fun h -> io_pre op h)
    (fun h (res:r) lt -> io_post op res /\ lt == [convert_call_to_event c op res])))
#pop-options

let get_trace #mst () : MIOwp (Ghost.erased trace) mst GetMStateOps
  (fun p h -> p [] (Ghost.hide h)) =
  MIOwp?.reflect (gdm_cmd1 mio_cwp empty_cmd_wp Prog (CmdR GetTrace) <: dm_gmio (Ghost.erased trace) mst GetMStateOps (fun p h -> p [] (Ghost.hide h)))

let get_state #mst () : MIOwp mst.typ mst GetMStateOps
  (fun p h -> forall s. s `mst.abstracts` h ==> p [] s) =
  MIOwp?.reflect (gdm_cmd1 mio_cwp empty_cmd_wp Prog (CmdR GetST) <: dm_gmio mst.typ mst GetMStateOps (fun p h -> forall s. s `mst.abstracts` h ==> p [] s))

(** Sanity check: flags compose through the effect (IOOps ⊕ GetMStateOps = AllOps). **)
private
let _test_flag_composition (#mst:mstate) () :
  MIO unit AllOps mst (fun _ -> True) (fun _ _ _ -> True) =
  let fd = static_op Prog (Openfile "test.txt") in
  let _ = get_state () in
  ()
