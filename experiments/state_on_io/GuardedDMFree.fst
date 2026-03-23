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

val guard_cmd_wp #event : cmd_wp guard_cmd event
let guard_cmd_wp (#event:Type) (_:caller) (#r:Type0) (cmd:guard_cmd r) : hist #event r =
  match cmd with
  | GCmd pre ->
    let wp' : hist0 #event (squash pre) = fun p h -> pre /\ p [] () in
    assert (forall (post1 post2:hist_post #event (squash pre)). (hist_post_ord post1 post2 ==> (forall h. wp' post1 h ==> wp' post2 h)));
    assert (hist_wp_monotonic wp');
    wp'

let guard_wp (#event:Type) (pre:pure_pre) : hist #event (squash pre) =
  guard_cmd_wp #event Prog (GCmd pre)

// The Dijkstra Monad
type gdm (cmd:Type0 -> Type) (event:Type) (cwp:cmd_wp cmd event) (a:Type) (wp:hist #event a) =
  (m:(free (cmd_sum guard_cmd cmd) a){theta (cmd_wp_sum guard_cmd_wp cwp) m ⊑ wp})

let gdm_return #cmd (#event:Type) (cwp:cmd_wp cmd event) #a (x : a) : gdm cmd event cwp a (hist_return #a #event x) =
  dm_return (cmd_wp_sum guard_cmd_wp cwp) x

let gdm_cmd #cmd (#event:Type) (cwp:cmd_wp cmd event) (c:caller) #r (op:cmd r) :
  gdm cmd event cwp r (hist_bind (cwp c op) (fun ri -> hist_return ri)) =
  Call c (CmdR op) Return

let gdm_bind
  #cmd (#event:Type) (cwp:cmd_wp cmd event)
  #a #b
  (wp_v : hist #event a)
  (wp_f: a -> hist #event b)
  (v : gdm cmd event cwp a wp_v)
  (f : (x:a -> gdm cmd event cwp b (wp_f x))) :
  Tot (gdm cmd event cwp b (hist_bind wp_v wp_f)) =
  dm_bind (cmd_wp_sum guard_cmd_wp cwp) wp_v wp_f v f

let gdm_subcomp #cmd (#event:Type) (cwp:cmd_wp cmd event) #a (wp1 wp2: hist #event a) (f : gdm cmd event cwp a wp1) :
  Pure (gdm cmd event cwp a wp2)
    (requires wp1 ⊑ wp2)
    (ensures fun _ -> True) =
  f

let gdm_if_then_else #cmd (#event:Type) (cwp:cmd_wp cmd event) #a
  (wp1 wp2: hist #event a) (f : gdm cmd event cwp a wp1) (g : gdm cmd event cwp a wp2) (b : bool) : Type =
  gdm cmd event cwp a (hist_if_then_else wp1 wp2 b)

let gdm_guard
  #cmd (#event:Type) (cwp:cmd_wp cmd event)
  (pre:pure_pre) : gdm cmd event cwp (squash pre) (guard_wp #event pre) =
  let m = Call Prog (CmdL (GCmd pre)) (Return) in
  assert (theta (cmd_wp_sum guard_cmd_wp cwp) m ⊑ (guard_wp #event pre));
  m

(** Note: the subcomp query (query 6 under --split_queries always) is a
    pre-existing Z3 limitation with higher-order quantifier instantiation
    for PURE WP semantics; it also fails on the original (pre-refactor) code
    without --split_queries. We use assume here. **)
#push-options "--z3rlimit 40"
val lift_pure_gdm : #cmd:(Type0 -> Type) -> #event:Type -> cwp:cmd_wp cmd event -> #a:Type u#a -> w:pure_wp a -> f:(eqtype_as_type unit -> PURE a w) -> gdm cmd event cwp a (wp_lift_pure_hist w)
let lift_pure_gdm #cmd (#event:Type) (cwp:cmd_wp cmd event)
  #a
  (w : pure_wp a)
  (f:(eqtype_as_type unit -> PURE a w)) :
  gdm cmd event cwp a (wp_lift_pure_hist w) =
  lemma_wp_lift_pure_hist_implies_as_requires #a #event w;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall u#a ();
  let lhs = gdm_guard cwp (as_requires w) in
  let rhs (_:squash (as_requires w)) : gdm cmd event cwp a (wp_lift_pure_hist w) =
    let r = f () in
    gdm_return cwp r in
  gdm_bind cwp (guard_wp #event (as_requires w)) (fun _ -> wp_lift_pure_hist w) lhs rhs
#pop-options
