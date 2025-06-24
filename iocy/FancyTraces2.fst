module FancyTraces2

open FStar.List.Tot
open FStar.Ghost

module M = FStar.FiniteMap.Base

type promise_id = erased nat

noeq
type promise (e:Type u#a) (a:Type u#b) : Type u#(max a b) =
| Promise : id:promise_id -> r:erased a -> promise e a
(** CA: having the local trace on the promise, pushes the promise type to universe 1, preventing HO promises **)

noeq
type event (e: Type0) : Type u#1 =
| Ev : e -> event e
| EAsync : #b:Type0 -> pr:promise e b -> lt:atrace e -> event e
| EAwait : #b:Type0 -> pr:promise e b -> event e
and atrace e : Type u#1 = list (event e)

type trace e = list e

assume val suffix_of : atrace 'e -> atrace 'e -> Type0
assume val lemma_suffix_of_reflexive : l:atrace 'e -> Lemma (suffix_of l l)

type parallel_traces e = (* promise_id -> atrace *)
  M.map nat (atrace e)
  (* CA: this nat should be promise_id, but is not an eqtype? *)
  // M.map int (a:Type0 & pr:promise e a & tr:atrace e)
  (* CA: why do I have the promise here? *)

let mem_id (id:promise_id) (pts:parallel_traces 'e) = reveal id `M.mem` pts
let sel_id (id:promise_id) (pts:(parallel_traces 'e){id `mem_id` pts}) : GTot (atrace 'e) =
  M.lookup (reveal id) pts
  // Mkdtuple3?._3 (M.lookup id pts)

let mem (pr:promise 'e 'a) (pts:parallel_traces 'e) = pr.id `mem_id` pts
let sel (pr:promise 'e 'a) (pts:(parallel_traces 'e){pr `mem` pts}) : GTot (atrace 'e) =
  sel_id pr.id pts

let insert (pr:promise 'e 'a) (lt:atrace 'e) (pts:parallel_traces 'e) : GTot (parallel_traces 'e) =
  M.insert (reveal pr.id) lt pts

let ord #e (pts pts':parallel_traces e) =
  (forall x. x `mem_id` pts ==> x `mem_id` pts') /\
  (forall x. x `mem_id` pts ==> (sel_id x pts' `suffix_of` sel_id x pts))

assume val size : atrace 'e -> nat

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
  (#_: squash (forall id. id `mem_id` pts ==> closed_atrace pts (sel_id id pts)))
  : list (trace 'e)

let w_pre e = h:atrace e -> map:parallel_traces e{
  closed_atrace map h
  // /\ (forall pr. pr `map_mem` map ==> (map_sel pr map) `suffix_of` pr.lt)
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