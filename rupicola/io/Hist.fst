module Hist

open FStar.Tactics
open FStar.List.Tot.Base
open Trace
(** The postcondition for an io computation is defined over the
result (type: a) and local trace (type: list event).
The local trace represents the events that happend during the
computation. Local trace is in chronological order.

We also have the history (type: list event) that represents the
events that happend until the beginning of the io computation.
The history is in reverse chronological order.

At the end of an io computation, the local trace is
reversed and appended to the history. **)

type hist_post (h:history) a = lt:local_trace h -> r:a -> Type0
type hist_pre = h:history -> Type0

type hist0 a =
  h:history -> hist_post h a -> Type0

unfold
let hist_post_ord (#h:history) (p1 p2:hist_post h 'a) = forall lt r. p1 lt r ==> p2 lt r

unfold
let hist_post_equiv (#h:history) (p1 p2:hist_post h 'a) =
  hist_post_ord p1 p2 /\ hist_post_ord p2 p1

unfold
let hist_wp_monotonic (wp:hist0 'a) =
  forall h (p1 p2:hist_post h 'a). (p1 `hist_post_ord` p2) ==>  (wp h p1 ==> wp h p2)

type hist a = wp:(hist0 a){hist_wp_monotonic wp}

let wp2p (wp:hist 'a) (h:history) : hist_post h 'a =
  fun lt res -> forall p. wp h p ==> p lt res

val hist_subcomp0 : #a:Type -> #p1:(a -> Type0) -> #p2:(a -> Type0) -> #_:unit{forall x. p1 x ==> p2 x} -> wp:hist (x:a{p1 x}) ->
  (hist (x:a{p2 x}))
let hist_subcomp0 #a #p1 #p2 #_ wp : (hist (x:a{p2 x})) =
  let wp' : hist0 (x:a{p2 x}) = wp in
  assert (forall h (post1:hist_post h (x:a{p2 x})) (post2:hist_post h (x:a{p2 x})). (hist_post_ord post1 post2 ==>  wp' h post1 ==> wp' h post2));
  assert (hist_wp_monotonic #(x:a{p2 x}) wp');
  wp'

val hist_subcomp : #a:Type -> #p1:(a -> Type0) -> #p2:(a -> Type0) -> wp:hist (x:a{p1 x}) ->
  Pure (hist (x:a{p2 x})) (requires (forall x. p1 x ==> p2 x)) (ensures (fun _ -> True))
let hist_subcomp #a #p1 #p2 wp = hist_subcomp0 #a #p1 #p2 #() wp


unfold
let hist_return (x:'a) : hist 'a =
  admit ();
  fun _ p -> p [] x

unfold
let hist_post_shift (h:history) (p:hist_post h 'a) (lt:local_trace h) : hist_post (h++lt) 'a =
  fun lt' r -> p (lt @ lt') r

unfold
let hist_post_bind
  (#a #b:Type)
  (h:history)
  (kw : a -> hist b)
  (p:hist_post h b) :
  Tot (hist_post h a) =
  fun lt r ->
    kw r (h ++ lt) (hist_post_shift h p lt)

unfold
let hist_bind (#a #b:Type) (w : hist a) (kw : a -> hist b) : hist b =
  fun h p -> w h (hist_post_bind #a #b h kw p)

unfold
let wp_lift_pure_hist (w : pure_wp 'a) : hist 'a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  admit ();
  fun _ p -> w (p [])

let lemma_wp_lift_pure_hist_implies_as_requires #a w :
  Lemma (forall h (p:hist_post h a). wp_lift_pure_hist w h p ==> as_requires w) =
    assert (forall h (p:hist_post h a) x. p [] x ==> True) ;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity w ;
    assert (forall h (p:hist_post h a). w (fun x -> p [] x) ==> w (fun _ -> True))

unfold
val (⊑) (#a : Type) : hist a -> hist a -> Type0
let (⊑) wp1 wp2 = forall h p. wp2 h p ==> wp1 h p

unfold
val hist_equiv (#a : Type) : hist a -> hist a -> Type0
let hist_equiv wp1 wp2 = forall h p. wp1 h p <==> wp2 h p

unfold
let hist_if_then_else (wp1 wp2:hist 'a) (b:bool) : hist 'a =
  fun h p -> (b ==> wp1 h p) /\ ((~b) ==> wp2 h p)

let __list_assoc_l #a (l1 l2 l3 : list a) : Lemma (l1 @ (l2 @ l3) == (l1 @ l2) @ l3) = List.Tot.Properties.append_assoc l1 l2 l3
let __helper #a (lt lt' : list a) : Lemma (rev_acc lt [] @ rev_acc lt' [] == rev_acc (lt'@lt) []) = List.Tot.Properties.rev_append lt' lt
let __iff_refl a : Lemma (a <==> a) = ()

let lemma_hist_bind_associativity #a #b #c (w1:hist a) (w2:a -> hist b) (w3: b -> hist c) :
  Lemma (hist_bind w1 (fun r1 -> hist_bind (w2 r1) w3) `hist_equiv` hist_bind (hist_bind w1 w2) w3)
  =
  let lhs = hist_bind w1 (fun r1 -> hist_bind (w2 r1) w3) in
  let rhs = hist_bind (hist_bind w1 w2) w3 in
  let pw (h : history) (p : hist_post h c) : Lemma (lhs h p <==> rhs h p) =
    assert (lhs h p <==> rhs h p) by begin
      unfold_def (`hist_bind);
      norm [];
      l_to_r [`__list_assoc_l];
      l_to_r [`__helper];
      mapply (`__iff_refl)
    end
  in
  Classical.forall_intro_2 pw

unfold
let to_hist #a (pre:hist_pre) (post:(h:history -> a -> local_trace h -> Type0)) : hist a =
  fun h p -> pre h /\ (forall lt r. post h r lt ==> p lt r)

let post_as_hist = to_hist (fun _ -> True)

let trivial_hist #a : hist a =
  to_hist (fun _ -> True) (fun _ _ _ -> True)
