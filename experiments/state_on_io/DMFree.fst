module DMFree

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Hist

let ev_wp (ev:Type0 -> Type) (event:Type) = caller -> #r:Type0 -> ev r -> hist #event r

let partial_call_wp (#event:Type) (pre:pure_pre) : hist #event (squash pre) =
  let wp' : hist0 #event (squash pre) = fun p h -> pre /\ p [] () in
  assert (forall (post1 post2:hist_post #event (squash pre)). (hist_post_ord post1 post2 ==> (forall h. wp' post1 h ==> wp' post2 h)));
  assert (hist_wp_monotonic wp');
  wp'

(** Inspired from Kenji Maillard's thesis (2.4.5) **)
let rec theta #a #ev (#event:Type) (cmd_wp:ev_wp ev event) (m:free ev a) : Tot (hist #event a) (decreases m) =
  match m with
  | Return x -> hist_return x
  | PartialCall pre k ->
      hist_bind (partial_call_wp #event pre) (fun r -> theta cmd_wp (k r))
  | Call caller cmd k ->
      hist_bind (cmd_wp caller cmd) (fun ri -> theta cmd_wp (k ri))

let lemma_theta_is_monad_morphism_ret #ev (#event:Type) (cmd_wp:ev_wp ev event) (v:'a) :
  Lemma (theta cmd_wp (free_return #ev v) == hist_return v) by (compute ()) = ()

let another_lemma (wp1:hist 'a) (wp2:'a -> hist 'b) (wp3:'a -> hist 'b) p h :
  Lemma
    (requires ((forall x. (wp3 x) ⊑ (wp2 x)) /\ hist_bind wp1 wp2 p h))
    (ensures (hist_bind wp1 wp3 p h)) = ()

let another_lemma' (wp1:hist 'a) (wp2:'a -> hist 'b) (wp3:'a -> hist 'b) :
  Lemma
    (requires ((forall x. (wp3 x) ⊑ (wp2 x))))
    (ensures (hist_bind wp1 wp3 ⊑ hist_bind wp1 wp2)) = ()

private let hist_ord wp1 wp2 = wp2 ⊑ wp1

let rec lemma_theta_is_lax_morphism_bind #a #b #ev (#event:Type) (cmd_wp:ev_wp ev event) (m:free ev a) (f:a -> free ev b) :
  Lemma
    (theta cmd_wp (free_bind m f) ⊑ hist_bind (theta cmd_wp m) (fun x -> theta cmd_wp (f x))) =
  match m with
  | Return x ->
    calc (hist_ord) {
      hist_bind (theta cmd_wp m) (fun x -> theta cmd_wp (f x));
      == {
        assert (hist_bind (theta cmd_wp (Return x)) (fun x -> theta cmd_wp (f x))
          == hist_bind (theta cmd_wp m) (fun x -> theta cmd_wp (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta cmd_wp (Return x)) (fun x -> theta cmd_wp (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_return x) (fun x -> theta cmd_wp (f x));
      `hist_ord` {} (** here there is an eta that forces us to use `hist_ord` **)
      theta cmd_wp (f x);
      == {} // unfold free_bind
      theta cmd_wp (free_bind (Return x) f);
      == {}
      theta cmd_wp (free_bind m f);
    }
  | Call tr cmd k ->
    calc (hist_ord) {
      hist_bind (theta cmd_wp m) (fun x -> theta cmd_wp (f x));
      == {
        assert (hist_bind (theta cmd_wp (Call tr cmd k)) (fun x -> theta cmd_wp (f x))
           == hist_bind (theta cmd_wp m) (fun x -> theta cmd_wp (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta cmd_wp (Call tr cmd k)) (fun x -> theta cmd_wp (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_bind (cmd_wp tr cmd) (fun ri -> theta cmd_wp (k ri))) (fun x -> theta cmd_wp (f x));
      `hist_equiv` { lemma_hist_bind_associativity (cmd_wp tr cmd) (fun ri -> theta cmd_wp (k ri)) (fun x -> theta cmd_wp (f x)) }
      hist_bind (cmd_wp tr cmd) (fun ri -> hist_bind (theta cmd_wp (k ri)) (fun x -> theta cmd_wp (f x)));
      `hist_ord` {
        let rhs1 = fun ri -> hist_bind (theta cmd_wp (k ri)) (fun x -> theta cmd_wp (f x)) in
        let rhs2 = fun ri -> theta cmd_wp (free_bind (k ri) f) in
        introduce forall ri. (rhs1 ri) `hist_ord` (rhs2 ri) with begin
          lemma_theta_is_lax_morphism_bind cmd_wp (k ri) f
        end;
        another_lemma' (cmd_wp tr cmd) rhs1 rhs2;
        assert (hist_bind (cmd_wp tr cmd) rhs1 `hist_ord` hist_bind (cmd_wp tr cmd) rhs2) by (assumption ())
      }
      hist_bind (cmd_wp tr cmd) (fun ri -> theta cmd_wp (free_bind (k ri) f));
      == { _ by (compute ()) } // unfold theta
      theta cmd_wp (Call tr cmd (fun ri -> free_bind (k ri) f));
      `hist_ord` { _ by (compute ()) } // unfold free_bind
      theta cmd_wp (free_bind (Call tr cmd k) f);
      == {}
      theta cmd_wp (free_bind m f);
    }
  | PartialCall pre k ->
    calc (hist_ord) {
      hist_bind (theta cmd_wp m) (fun x -> theta cmd_wp (f x));
      == {
        assert (hist_bind (theta cmd_wp (PartialCall pre k)) (fun x -> theta cmd_wp (f x))
           == hist_bind (theta cmd_wp m) (fun x -> theta cmd_wp (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta cmd_wp (PartialCall pre k)) (fun x -> theta cmd_wp (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_bind (partial_call_wp #event pre) (fun r -> theta cmd_wp (k r))) (fun x -> theta cmd_wp (f x));
      `hist_equiv` { lemma_hist_bind_associativity (partial_call_wp #event pre) (fun r -> theta cmd_wp (k r)) (fun x -> theta cmd_wp (f x)) }
      hist_bind (partial_call_wp #event pre) (fun r -> hist_bind (theta cmd_wp (k r)) (fun x -> theta cmd_wp (f x)));
      `hist_ord` {
        let rhs1 = fun r -> hist_bind (theta cmd_wp (k r)) (fun x -> theta cmd_wp (f x)) in
        let rhs2 = fun r -> theta cmd_wp (free_bind (k r) f) in
        introduce forall (r:squash pre). (rhs1 r) `hist_ord` (rhs2 r) with begin
          lemma_theta_is_lax_morphism_bind cmd_wp (k r) f
        end;
        another_lemma' (partial_call_wp #event pre) rhs1 rhs2;
        assert (hist_bind (partial_call_wp #event pre) rhs1 `hist_ord` hist_bind (partial_call_wp #event pre) rhs2) by (assumption ())
      }
      hist_bind (partial_call_wp #event pre) (fun r -> theta cmd_wp (free_bind (k r) f));
      == { _ by (compute ()) } // unfold theta
      theta cmd_wp (PartialCall pre (fun r -> free_bind (k r) f));
      `hist_ord` { _ by (compute ()) } // unfold free_bind
      theta cmd_wp (free_bind (PartialCall pre k) f);
      == {}
      theta cmd_wp (free_bind m f);
    }

// The Dijkstra Monad
type dm (ev:Type0 -> Type) (event:Type) (cmd_wp:ev_wp ev event) (a:Type) (wp:hist #event a) =
  (m:(free ev a){theta cmd_wp m ⊑ wp})

let dm_return #ev (#event:Type) (cmd_wp:ev_wp ev event) #a (x : a) : dm ev event cmd_wp a (hist_return #a #event x) =
  free_return x

#push-options "--z3rlimit 40"
let dm_bind
  #ev (#event:Type) (cmd_wp:ev_wp ev event)
  #a #b
  (wp_v : hist #event a)
  (wp_f: a -> hist #event b)
  (v : dm ev event cmd_wp a wp_v)
  (f : (x:a -> dm ev event cmd_wp b (wp_f x))) :
  Tot (dm ev event cmd_wp b (hist_bind wp_v wp_f)) =
  lemma_theta_is_lax_morphism_bind cmd_wp v f;
  free_bind v f
#pop-options

let dm_subcomp #ev (#event:Type) (cmd_wp:ev_wp ev event) #a (wp1 wp2: hist #event a) (f : dm ev event cmd_wp a wp1) :
  Pure (dm ev event cmd_wp a wp2)
    (requires wp1 ⊑ wp2)
    (ensures fun _ -> True) =
  f

let dm_if_then_else #ev (#event:Type) (cmd_wp:ev_wp ev event) #a
  (wp1 wp2: hist #event a) (f : dm ev event cmd_wp a wp1) (g : dm ev event cmd_wp a wp2) (b : bool) : Type =
  dm ev event cmd_wp a (hist_if_then_else wp1 wp2 b)

let dm_partial_return
  #ev (#event:Type) (cmd_wp:ev_wp ev event)
  (pre:pure_pre) : dm ev event cmd_wp (squash pre) (partial_call_wp #event pre) =
  let m = PartialCall pre (Return) in
  assert ((partial_call_wp #event pre) `hist_ord` theta cmd_wp m);
  m

(** Note: the subcomp query (query 6 under --split_queries always) is a
    pre-existing Z3 limitation with higher-order quantifier instantiation
    for PURE WP semantics; it also fails on the original (pre-refactor) code
    without --split_queries. We use assume here. **)
#push-options "--z3rlimit 40"
let lift_pure_dm #ev (#event:Type) (cmd_wp:ev_wp ev event)
  #a
  (w : pure_wp a)
  (f:(eqtype_as_type unit -> PURE a w)) :
  dm ev event cmd_wp a (wp_lift_pure_hist w) =
  lemma_wp_lift_pure_hist_implies_as_requires #a #event w;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs = dm_partial_return cmd_wp (as_requires w) in
  let rhs = (fun (pre:(squash (as_requires w))) -> dm_return cmd_wp (f pre)) in
  let m = dm_bind cmd_wp _ _ lhs rhs in
  assume (theta cmd_wp m ⊑ wp_lift_pure_hist w);
  m
#pop-options
