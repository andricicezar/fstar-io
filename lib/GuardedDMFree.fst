module GuardedDMFree

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

include Hist
open Free
open DMFree

noeq
type guard_cmd : Type -> Type =
| GCmd : (pre:pure_pre) -> guard_cmd (squash pre)

let guard_cmd_wp (#event:Type) : cmd_wp guard_cmd event =
  fun #r (cmd:guard_cmd r) ->
    match cmd with
    | GCmd pre ->
      let wp' : hist0 #event (squash pre) = fun p h -> pre /\ p [] () in
      assert (forall (post1 post2:hist_post #event (squash pre)). (hist_post_ord post1 post2 ==> (forall h. wp' post1 h ==> wp' post2 h)));
      assert (hist_wp_monotonic wp');
      wp'

let guard_wp (#event:Type) (pre:pure_pre) : hist #event (squash pre) =
  guard_cmd_wp #event (GCmd pre)

(** The guard commands are Type0-indexed and live on the first channel,
    summed with the client's cmd1. The second channel is passed through
    untouched, so its index universe is unconstrained by the guards. *)
// The Dijkstra Monad
type gdm (cmd1:Type -> Type) (cmd2:Type -> Type) (event:Type)
  (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event)
  (a:Type) (wp:hist #event a) =
  (m:(free (cmd_sum guard_cmd cmd1) cmd2 a){theta (cmd_wp_sum guard_cmd_wp cwp1) cwp2 m ⊑ wp})

let gdm_return #cmd1 #cmd2 (#event:Type) (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event) #a (x : a)
  : gdm cmd1 cmd2 event cwp1 cwp2 a (hist_return #a #event x) =
  dm_return (cmd_wp_sum guard_cmd_wp cwp1) cwp2 x

#push-options "--z3rlimit 20"
let gdm_cmd1 #cmd1 #cmd2 (#event:Type) (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event) #r (op:cmd1 r) :
  gdm cmd1 cmd2 event cwp1 cwp2 r (hist_bind (cwp1 op) (fun ri -> hist_return ri)) =
  let m : free (cmd_sum guard_cmd cmd1) cmd2 r = Call1 (CmdR op) Return in
  assert (theta (cmd_wp_sum guard_cmd_wp cwp1) cwp2 m == hist_bind (cwp1 op) (fun ri -> hist_return ri))
    by (compute ());
  m

let gdm_cmd2 #cmd1 #cmd2 (#event:Type) (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event) #r (op:cmd2 r) :
  gdm cmd1 cmd2 event cwp1 cwp2 r (hist_bind (cwp2 op) (fun ri -> hist_return ri)) =
  let m : free (cmd_sum guard_cmd cmd1) cmd2 r = Call2 op Return in
  assert (theta (cmd_wp_sum guard_cmd_wp cwp1) cwp2 m == hist_bind (cwp2 op) (fun ri -> hist_return ri))
    by (compute ());
  m
#pop-options

let gdm_bind
  #cmd1 #cmd2 (#event:Type) (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event)
  #a #b
  (wp_v : hist #event a)
  (wp_f: a -> hist #event b)
  (v : gdm cmd1 cmd2 event cwp1 cwp2 a wp_v)
  (f : (x:a -> gdm cmd1 cmd2 event cwp1 cwp2 b (wp_f x))) :
  Tot (gdm cmd1 cmd2 event cwp1 cwp2 b (hist_bind wp_v wp_f)) =
  dm_bind (cmd_wp_sum guard_cmd_wp cwp1) cwp2 wp_v wp_f v f

let gdm_subcomp #cmd1 #cmd2 (#event:Type) (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event) #a
  (wp1 wp2: hist #event a) (f : gdm cmd1 cmd2 event cwp1 cwp2 a wp1) :
  Pure (gdm cmd1 cmd2 event cwp1 cwp2 a wp2)
    (requires wp1 ⊑ wp2)
    (ensures fun _ -> True) =
  f

let gdm_if_then_else #cmd1 #cmd2 (#event:Type) (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event) #a
  (wp1 wp2: hist #event a)
  (f : gdm cmd1 cmd2 event cwp1 cwp2 a wp1) (g : gdm cmd1 cmd2 event cwp1 cwp2 a wp2) (b : bool) : Type =
  gdm cmd1 cmd2 event cwp1 cwp2 a (hist_if_then_else wp1 wp2 b)

let gdm_guard
  #cmd1 #cmd2 (#event:Type) (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event)
  (pre:pure_pre) : gdm cmd1 cmd2 event cwp1 cwp2 (squash pre) (guard_wp #event pre) =
  let m = Call1 (CmdL (GCmd pre)) (Return) in
  assert (theta (cmd_wp_sum guard_cmd_wp cwp1) cwp2 m ⊑ (guard_wp #event pre));
  m

(** Note: the subcomp query (query 6 under --split_queries always) is a
    pre-existing Z3 limitation with higher-order quantifier instantiation
    for PURE WP semantics; it also fails on the original (pre-refactor) code
    without --split_queries. We use assume here. **)
#push-options "--z3rlimit 40"
val lift_pure_gdm : #cmd1:(Type -> Type) -> #cmd2:(Type -> Type) -> #event:Type ->
  cwp1:cmd_wp cmd1 event -> cwp2:cmd_wp cmd2 event ->
  #a:Type u#a -> w:pure_wp a -> f:(eqtype_as_type unit -> PURE a w) ->
  gdm cmd1 cmd2 event cwp1 cwp2 a (wp_lift_pure_hist w)
let lift_pure_gdm #cmd1 #cmd2 (#event:Type) (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event)
  #a
  (w : pure_wp a)
  (f:(eqtype_as_type unit -> PURE a w)) :
  gdm cmd1 cmd2 event cwp1 cwp2 a (wp_lift_pure_hist w) =
  lemma_wp_lift_pure_hist_implies_as_requires #a #event w;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall u#a ();
  let lhs = gdm_guard cwp1 cwp2 (as_requires w) in
  let rhs (_:squash (as_requires w)) : gdm cmd1 cmd2 event cwp1 cwp2 a (wp_lift_pure_hist w) =
    let r = f () in
    gdm_return cwp1 cwp2 r in
  gdm_bind cwp1 cwp2 (guard_wp #event (as_requires w)) (fun _ -> wp_lift_pure_hist w) lhs rhs
#pop-options
