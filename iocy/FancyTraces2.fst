module FancyTraces2

open FStar.List.Tot
open FStar.Ghost

module M = FStar.FiniteMap.Base

noeq
type promise (e:Type0) (a:Type0) : Type u#0 =
| Promise : id:erased nat -> r:erased a -> promise e a (** CA: having the local trace on the promise, pushes the promise type to universe 1, preventing HO promises **)

noeq
type event (e: Type0) : Type u#1 =
| Ev : e -> event e
| EAsync : #b:Type0 -> pr:promise e b -> lt:atrace e -> event e
| EAwait : #b:Type0 -> pr:promise e b -> event e
and atrace e : Type u#1 = list (event e)

type trace e = list e

assume val suffix_of : atrace 'e -> atrace 'e -> Type0
assume val lemma_suffix_of_reflexive : l:atrace 'e -> Lemma (suffix_of l l)

type map_t e =
  M.map int (a:Type0 & pr:promise e a & tr:atrace e)

let map_mem (pr:promise 'e 'a) (m:map_t 'e) = reveal pr.id `M.mem` m
let map_sel (pr:promise 'e 'a) (m:(map_t 'e){pr `map_mem` m}) : GTot (atrace 'e) =
  Mkdtuple3?._3 (M.lookup (reveal pr.id) m)
let map_sel_id (id:nat) (m:(map_t 'e){id `M.mem` m}) : GTot (atrace 'e) =
  Mkdtuple3?._3 (M.lookup id m)
let map_insert (pr:promise 'e 'a) (lt:atrace 'e) (m:map_t 'e) : GTot (map_t 'e) =
  M.insert (reveal pr.id) (| 'a, pr, lt |) m

assume val size : atrace 'e -> nat

let rec closed_atrace (m:map_t 'e) (tr:atrace 'e) : GTot Type0 (decreases (size tr)) =
  match tr with
  | [] -> True
  | Ev _ :: tl ->
    assume (size tl < size tr);
    closed_atrace m tl
  | EAwait #_ #b pr :: tl ->
    assume (size tl < size tr);
    pr `map_mem` m /\ closed_atrace m tl
  | EAsync pr lt :: tl ->
    assume (size lt < size tr);
    assume (size (lt@tl) < size tr);
    closed_atrace m lt /\
    closed_atrace (map_insert pr lt m) (lt@tl) (** this is a bit awkard because it exposes the promise to the asynchronus computation **)
    (** this variant does not consider HO promises:
        closed_atrace m lt /\ closed_atrace (map_insert pr m lt) tl **)

val interleave_map
  (m: map_t 'e)
  (#_: squash (forall id. id `M.mem` m ==> closed_atrace m (map_sel_id id m)))
  : list (trace 'e)
