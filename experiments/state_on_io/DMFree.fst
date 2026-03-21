module DMFree

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Hist

(** cmd_wp maps each command to a hist-based WP over events.
    - cmd: command type (parameterizes the free monad)
    - event: event type (parameterizes the hist monad) *)
let cmd_wp (cmd:Type0 -> Type) (event:Type) = caller -> #r:Type0 -> cmd r -> hist #event r

let guard_wp (#event:Type) (pre:pure_pre) : hist #event (squash pre) =
  let wp' : hist0 #event (squash pre) = fun p h -> pre /\ p [] () in
  assert (forall (post1 post2:hist_post #event (squash pre)). (hist_post_ord post1 post2 ==> (forall h. wp' post1 h ==> wp' post2 h)));
  assert (hist_wp_monotonic wp');
  wp'

(** Inspired from Kenji Maillard's thesis (2.4.5) **)
let rec theta #a #cmd (#event:Type) (cwp:cmd_wp cmd event) (m:free cmd a) : Tot (hist #event a) (decreases m) =
  match m with
  | Return x -> hist_return x
  | Guard pre k ->
      hist_bind (guard_wp #event pre) (fun r -> theta cwp (k r))
  | Call c op k ->
      hist_bind (cwp c op) (fun ri -> theta cwp (k ri))

let lemma_theta_is_monad_morphism_ret #cmd (#event:Type) (cwp:cmd_wp cmd event) (v:'a) :
  Lemma (theta cwp (free_return #cmd v) == hist_return v) by (compute ()) = ()

let another_lemma (wp1:hist 'a) (wp2:'a -> hist 'b) (wp3:'a -> hist 'b) p h :
  Lemma
    (requires ((forall x. (wp3 x) ⊑ (wp2 x)) /\ hist_bind wp1 wp2 p h))
    (ensures (hist_bind wp1 wp3 p h)) = ()

let another_lemma' (wp1:hist 'a) (wp2:'a -> hist 'b) (wp3:'a -> hist 'b) :
  Lemma
    (requires ((forall x. (wp3 x) ⊑ (wp2 x))))
    (ensures (hist_bind wp1 wp3 ⊑ hist_bind wp1 wp2)) = ()

private let hist_ord wp1 wp2 = wp2 ⊑ wp1

let rec lemma_theta_is_lax_morphism_bind #a #b #cmd (#event:Type) (cwp:cmd_wp cmd event) (m:free cmd a) (f:a -> free cmd b) :
  Lemma
    (theta cwp (free_bind m f) ⊑ hist_bind (theta cwp m) (fun x -> theta cwp (f x))) =
  match m with
  | Return x ->
    calc (hist_ord) {
      hist_bind (theta cwp m) (fun x -> theta cwp (f x));
      == {
        assert (hist_bind (theta cwp (Return x)) (fun x -> theta cwp (f x))
          == hist_bind (theta cwp m) (fun x -> theta cwp (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta cwp (Return x)) (fun x -> theta cwp (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_return x) (fun x -> theta cwp (f x));
      `hist_ord` {} (** here there is an eta that forces us to use `hist_ord` **)
      theta cwp (f x);
      == {} // unfold free_bind
      theta cwp (free_bind (Return x) f);
      == {}
      theta cwp (free_bind m f);
    }
  | Call c op k ->
    calc (hist_ord) {
      hist_bind (theta cwp m) (fun x -> theta cwp (f x));
      == {
        assert (hist_bind (theta cwp (Call c op k)) (fun x -> theta cwp (f x))
           == hist_bind (theta cwp m) (fun x -> theta cwp (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta cwp (Call c op k)) (fun x -> theta cwp (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_bind (cwp c op) (fun ri -> theta cwp (k ri))) (fun x -> theta cwp (f x));
      `hist_equiv` { lemma_hist_bind_associativity (cwp c op) (fun ri -> theta cwp (k ri)) (fun x -> theta cwp (f x)) }
      hist_bind (cwp c op) (fun ri -> hist_bind (theta cwp (k ri)) (fun x -> theta cwp (f x)));
      `hist_ord` {
        let rhs1 = fun ri -> hist_bind (theta cwp (k ri)) (fun x -> theta cwp (f x)) in
        let rhs2 = fun ri -> theta cwp (free_bind (k ri) f) in
        introduce forall ri. (rhs1 ri) `hist_ord` (rhs2 ri) with begin
          lemma_theta_is_lax_morphism_bind cwp (k ri) f
        end;
        another_lemma' (cwp c op) rhs1 rhs2;
        assert (hist_bind (cwp c op) rhs1 `hist_ord` hist_bind (cwp c op) rhs2) by (assumption ())
      }
      hist_bind (cwp c op) (fun ri -> theta cwp (free_bind (k ri) f));
      == { _ by (compute ()) } // unfold theta
      theta cwp (Call c op (fun ri -> free_bind (k ri) f));
      `hist_ord` { _ by (compute ()) } // unfold free_bind
      theta cwp (free_bind (Call c op k) f);
      == {}
      theta cwp (free_bind m f);
    }
  | Guard pre k ->
    calc (hist_ord) {
      hist_bind (theta cwp m) (fun x -> theta cwp (f x));
      == {
        assert (hist_bind (theta cwp (Guard pre k)) (fun x -> theta cwp (f x))
           == hist_bind (theta cwp m) (fun x -> theta cwp (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta cwp (Guard pre k)) (fun x -> theta cwp (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_bind (guard_wp #event pre) (fun r -> theta cwp (k r))) (fun x -> theta cwp (f x));
      `hist_equiv` { lemma_hist_bind_associativity (guard_wp #event pre) (fun r -> theta cwp (k r)) (fun x -> theta cwp (f x)) }
      hist_bind (guard_wp #event pre) (fun r -> hist_bind (theta cwp (k r)) (fun x -> theta cwp (f x)));
      `hist_ord` {
        let rhs1 = fun r -> hist_bind (theta cwp (k r)) (fun x -> theta cwp (f x)) in
        let rhs2 = fun r -> theta cwp (free_bind (k r) f) in
        introduce forall (r:squash pre). (rhs1 r) `hist_ord` (rhs2 r) with begin
          lemma_theta_is_lax_morphism_bind cwp (k r) f
        end;
        another_lemma' (guard_wp #event pre) rhs1 rhs2;
        assert (hist_bind (guard_wp #event pre) rhs1 `hist_ord` hist_bind (guard_wp #event pre) rhs2) by (assumption ())
      }
      hist_bind (guard_wp #event pre) (fun r -> theta cwp (free_bind (k r) f));
      == { _ by (compute ()) } // unfold theta
      theta cwp (Guard pre (fun r -> free_bind (k r) f));
      `hist_ord` { _ by (compute ()) } // unfold free_bind
      theta cwp (free_bind (Guard pre k) f);
      == {}
      theta cwp (free_bind m f);
    }

// The Dijkstra Monad
type dm (cmd:Type0 -> Type) (event:Type) (cwp:cmd_wp cmd event) (a:Type) (wp:hist #event a) =
  (m:(free cmd a){theta cwp m ⊑ wp})

let dm_return #cmd (#event:Type) (cwp:cmd_wp cmd event) #a (x : a) : dm cmd event cwp a (hist_return #a #event x) =
  free_return x

#push-options "--z3rlimit 40"
let dm_bind
  #cmd (#event:Type) (cwp:cmd_wp cmd event)
  #a #b
  (wp_v : hist #event a)
  (wp_f: a -> hist #event b)
  (v : dm cmd event cwp a wp_v)
  (f : (x:a -> dm cmd event cwp b (wp_f x))) :
  Tot (dm cmd event cwp b (hist_bind wp_v wp_f)) =
  lemma_theta_is_lax_morphism_bind cwp v f;
  free_bind v f
#pop-options

let dm_subcomp #cmd (#event:Type) (cwp:cmd_wp cmd event) #a (wp1 wp2: hist #event a) (f : dm cmd event cwp a wp1) :
  Pure (dm cmd event cwp a wp2)
    (requires wp1 ⊑ wp2)
    (ensures fun _ -> True) =
  f

let dm_if_then_else #cmd (#event:Type) (cwp:cmd_wp cmd event) #a
  (wp1 wp2: hist #event a) (f : dm cmd event cwp a wp1) (g : dm cmd event cwp a wp2) (b : bool) : Type =
  dm cmd event cwp a (hist_if_then_else wp1 wp2 b)

let dm_guard_return
  #cmd (#event:Type) (cwp:cmd_wp cmd event)
  (pre:pure_pre) : dm cmd event cwp (squash pre) (guard_wp #event pre) =
  let m = Guard pre (Return) in
  assert ((guard_wp #event pre) `hist_ord` theta cwp m);
  m

(** Note: the subcomp query (query 6 under --split_queries always) is a
    pre-existing Z3 limitation with higher-order quantifier instantiation
    for PURE WP semantics; it also fails on the original (pre-refactor) code
    without --split_queries. We use assume here. **)
#push-options "--z3rlimit 40"
let lift_pure_dm #cmd (#event:Type) (cwp:cmd_wp cmd event)
  #a
  (w : pure_wp a)
  (f:(eqtype_as_type unit -> PURE a w)) :
  dm cmd event cwp a (wp_lift_pure_hist w) =
  lemma_wp_lift_pure_hist_implies_as_requires #a #event w;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs = dm_guard_return cwp (as_requires w) in
  let rhs = (fun (pre:(squash (as_requires w))) -> dm_return cwp (f pre)) in
  let m = dm_bind cwp _ _ lhs rhs in
  assume (theta cwp m ⊑ wp_lift_pure_hist w);
  m
#pop-options
