module FancyTraces2

open FStar.List.Tot

val promise (e:Type u#a) (a:Type u#b) : Type u#(max a b)

noeq
type event (e: Type0) : Type u#1 =
| Ev : e -> event e
| EAsync : #b:Type0 -> pr:promise e b -> lt:atrace e -> event e
| EAwait : #b:Type0 -> pr:promise e b -> event e
and atrace e : Type u#1 = list (event e)

type trace e = list e

val suffix_of : atrace 'e -> atrace 'e -> Type0
val lemma_suffix_of_reflexive : l:atrace 'e -> Lemma (suffix_of l l)

val parallel_traces (e:Type0) : Type u#1 (* promise_id -> atrace *)

val mem (pr:promise 'e 'a) (pts:parallel_traces 'e) : Type0
val sel (pr:promise 'e 'a) (pts:(parallel_traces 'e){pr `mem` pts}) : atrace 'e

val insert (pr:promise 'e 'a) (lt:atrace 'e) (pts:parallel_traces 'e) : parallel_traces 'e

let ord #e (pts pts':parallel_traces e) =
  (forall a (x:promise e a). x `mem` pts ==> x `mem` pts') /\
  (forall a (x:promise e a). x `mem` pts ==> (sel x pts' `suffix_of` sel x pts))

val size : atrace 'e -> nat

let rec closed_atrace (m:parallel_traces 'e) (tr:atrace 'e) : GTot Type0 (decreases (size tr)) =
  match tr with
  | [] -> True
  | Ev _ :: tl ->
    assume (size tl < size tr);
    closed_atrace m tl
  | EAwait #_ #b pr :: tl ->
    assume (size tl < size tr);
    pr `mem` m /\ closed_atrace m tl
  | EAsync pr lt :: tl ->
    assume (size lt < size tr);
    assume (size (lt@tl) < size tr);
    closed_atrace m lt /\
    closed_atrace (insert pr lt m) (lt@tl)
    (** this is a bit awkard because it exposes the promise to the asynchronus computation **)
    (** this variant does not consider HO promises:
        closed_atrace m lt /\ closed_atrace (map_insert pr m lt) tl **)

val interleave_map
  (pts: parallel_traces 'e)
  (#_: squash (forall a (pr:promise 'e a). pr `mem` pts ==> closed_atrace pts (sel pr pts)))
  : list (trace 'e)

let w_pre e = h:atrace e -> pts:parallel_traces e{
  closed_atrace pts h
  // /\ (forall pr. pr `mem` pts ==> (sel pr pts) `suffix_of` pr.lt)
  // we cannot have this refinement since we don't store the trace on the promise anymore
} -> Type0

let w_post e a h pts =
  a -> lt:atrace e -> pts':parallel_traces e{
      pts `ord` pts' /\
      closed_atrace pts' (h @ lt)
  } -> Type0

let w e a = h:atrace e -> pts:parallel_traces e{closed_atrace pts h} -> w_post e a h pts -> Type0

let encode_pre_post_in_w #e #a
  (pre:w_pre e)
  (post:(h:atrace e -> pts:parallel_traces e -> w_post e a h pts))
  : w e a
  = (fun h pts p -> pre h pts /\ (forall r' lt' pts'. post h pts r' lt' pts' ==> p r' lt' pts'))