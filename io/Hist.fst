module Hist

open FStar.Tactics
open FStar.List.Tot.Base

(** The postcondition for an io computation is defined over the
result (type: a) and local trace (type: list event).
The local trace represents the events that happend during the
computation. Local trace is in chronological order.

We also have the history (type: list event) that represents the
events that happend until the beginning of the io computation.
The history is in reverse chronological order.

At the end of an io computation, the local trace is
reversed and appended to the history. **)

let hist_post (#event_type:Type) a = lt:list event_type -> r:a -> Type0
let hist_pre (#event_type:Type) = h:list event_type -> Type0

type hist0 (#event_type:Type) a = hist_post #event_type a -> hist_pre #event_type

unfold
let hist_post_ord (#event_type:Type) (p1 p2:hist_post #event_type 'a) = forall lt r. p1 lt r ==> p2 lt r

unfold
let hist_wp_monotonic (#event_type:Type) (wp:hist0 #event_type 'a) =
  forall p1 p2. (p1 `hist_post_ord` p2) ==> (forall h. wp p1 h ==> wp p2 h)

type hist #event_type a = wp:(hist0 #event_type a){hist_wp_monotonic wp}

val hist_subcomp0 : #event_type:Type -> #a:Type -> #p1:(a -> Type0) -> #p2:(a -> Type0) -> #_:unit{forall x. p1 x ==> p2 x} -> wp:hist #event_type (x:a{p1 x}) -> 
  (hist #event_type (x:a{p2 x}))
let hist_subcomp0 #_ #a #p1 #p2 #_ wp : (hist (x:a{p2 x})) =
  let wp' : hist0 (x:a{p2 x}) = wp in
  assert (forall (post1:hist_post (x:a{p2 x})) (post2:hist_post (x:a{p2 x})). (hist_post_ord post1 post2 ==> (forall h. wp' post1 h ==> wp' post2 h)));
  assert (hist_wp_monotonic #(x:a{p2 x}) wp');
  wp'

val hist_subcomp : #event_type:Type -> #a:Type -> #p1:(a -> Type0) -> #p2:(a -> Type0) -> wp:hist #event_type (x:a{p1 x}) -> 
  Pure (hist #event_type (x:a{p2 x})) (requires (forall x. p1 x ==> p2 x)) (ensures (fun _ -> True))
let hist_subcomp #event_type #a #p1 #p2 wp = hist_subcomp0 #event_type #a #p1 #p2 #() wp


unfold
let hist_return (#event_type:Type) (x:'a) : hist #event_type 'a =
  fun p _ -> p [] x

unfold
let hist_post_shift (#event_type:Type) (p:hist_post #event_type 'a) (lt:list event_type) : hist_post #event_type 'a =
  fun lt' r -> p (lt @ lt') r

unfold
let hist_post_bind
  (#a #b:Type)
  (#event_type:Type)
  (h:list event_type)
  (kw : a -> hist #event_type b)
  (p:hist_post #event_type b) :
  Tot (hist_post #event_type a) =
  fun lt r ->
    kw r (hist_post_shift p lt) (List.rev lt @ h)

unfold
let hist_bind (#event_type:Type) (#a #b:Type) (w : hist #event_type a) (kw : a -> hist #event_type b) : hist #event_type b =
  fun p h -> w (hist_post_bind #a #b #event_type h kw p) h

unfold
let wp_lift_pure_hist (#event_type:Type) (w : pure_wp 'a) : hist #event_type 'a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fun p _ -> w (p [])

let lemma_wp_lift_pure_hist_implies_as_requires #a #event_type w :
  Lemma (forall (p:hist_post #event_type a) h. wp_lift_pure_hist w p h ==> as_requires w) =
    assert (forall (p:hist_post #event_type a) x. p [] x ==> True) ;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity w ;
    assert (forall (p:hist_post #event_type a). w (fun x -> p [] x) ==> w (fun _ -> True))

unfold
val (⊑) (#event_type:Type) (#a : Type) : hist #event_type a -> hist #event_type a -> Type0
let (⊑) wp1 wp2 = forall h p. wp2 p h ==> wp1 p h

unfold
val hist_equiv (#event_type:Type) (#a : Type) : hist #event_type a -> hist #event_type a -> Type0
let hist_equiv wp1 wp2 = forall h p. wp1 p h <==> wp2 p h

unfold
let hist_if_then_else (wp1 wp2:hist #'event 'a) (b:bool) : hist #'event 'a =
  fun p h -> (b ==> wp1 p h) /\ ((~b) ==> wp2 p h)

let __list_assoc_l #a (l1 l2 l3 : list a) : Lemma (l1 @ (l2 @ l3) == (l1 @ l2) @ l3) = List.Tot.Properties.append_assoc l1 l2 l3
let __helper #a (lt lt' : list a) : Lemma (rev_acc lt [] @ rev_acc lt' [] == rev_acc (lt'@lt) []) = List.Tot.Properties.rev_append lt' lt
let __iff_refl a : Lemma (a <==> a) = ()

let lemma_hist_bind_associativity #a #b #c #ev (w1:hist #ev a) (w2:a -> hist #ev b) (w3: b -> hist #ev c) :
  Lemma (hist_bind w1 (fun r1 -> hist_bind (w2 r1) w3) `hist_equiv` hist_bind (hist_bind w1 w2) w3)
  =
  let lhs = hist_bind w1 (fun r1 -> hist_bind (w2 r1) w3) in
  let rhs = hist_bind (hist_bind w1 w2) w3 in
  let pw (p : hist_post c) (h : list ev) : Lemma (lhs p h <==> rhs p h) =
    assert (lhs p h <==> rhs p h) by begin
      unfold_def (`hist_bind);
      norm [];
      l_to_r [`__list_assoc_l];
      l_to_r [`__helper];
      mapply (`__iff_refl)
    end
  in
  Classical.forall_intro_2 pw
  

unfold
let to_hist #a #event pre post : hist #event a =
  fun p h -> pre h /\ (forall lt r. post h r lt ==> p lt r)

let post_as_hist = to_hist (fun _ -> True)

(** TODO: is this the trivial wp? **)
let trivial_hist #a #event : hist #event a =
  to_hist (fun _ -> True) (fun _ _ _ -> True)


type dec_post #event = list event -> list event -> Type0
