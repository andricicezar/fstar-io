module FancyTraces2

open FStar.List.Tot
open FStar.Ghost

module M = FStar.FiniteMap.Base

type promise_id = nat

noeq
type promise (e:Type u#a) (a:Type u#b) : Type u#(max a b) =
| Promise : id:promise_id -> r:erased a -> promise e a
(** CA: having the local trace on the promise, pushes the promise type to universe 1, preventing HO promises **)

let suffix_of l h = admit ()
let lemma_suffix_of_reflexive l = admit ()

type parallel_traces e : Type u#1 = (* promise_id -> atrace *)
  M.map promise_id (atrace e)
  (* CA: this nat should be promise_id, but is not an eqtype? *)
  // M.map int (a:Type0 & pr:promise e a & tr:atrace e)
  (* CA: why do I have the promise here? *)

let mem_id (id:promise_id) (pts:parallel_traces 'e) = reveal id `M.mem` pts
let sel_id (id:promise_id) (pts:(parallel_traces 'e){id `mem_id` pts}) : (atrace 'e) =
  M.lookup id pts
  // Mkdtuple3?._3 (M.lookup id pts)

let mem (pr:promise 'e 'a) (pts:parallel_traces 'e) = pr.id `mem_id` pts
let sel (pr:promise 'e 'a) (pts:(parallel_traces 'e){pr `mem` pts}) :  atrace 'e =
  sel_id pr.id pts
let insert (pr:promise 'e 'a) (lt:atrace 'e) (pts:parallel_traces 'e) : parallel_traces 'e =
  M.insert pr.id lt pts
