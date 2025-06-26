module FancyTraces2

open FStar.List.Tot
open FStar.Ghost

module FSet = FStar.FiniteSet.Base
module M = FStar.FiniteMap.Base

type promise_id = nat

noeq
type promise (e:Type u#0) (a:Type u#0) : Type u#0 =
| Promise : id:promise_id -> promise e a
(** CA: having the local trace on the promise, pushes the promise type to universe 1, preventing HO promises **)

type parallel_traces (e:Type0) : Type u#1 = (* promise_id -> atrace *)
  n:nat & m:(M.map promise_id (a:Type0 & a & atrace e)){
    forall id. id `FSet.mem` (M.domain m) <==> id < n
  }
  // M.map int (a:Type0 & pr:promise e a & tr:atrace e)
  (* CA: why do I have the promise here? *)

let mem_id (id:promise_id) (pts:parallel_traces 'e) = id `M.mem` (dsnd pts)
let sel_id (id:promise_id) (pts:(parallel_traces 'e){id `mem_id` pts}) : a:Type0 & a & atrace 'e =
  M.lookup id (dsnd pts)
  // Mkdtuple3?._3 (M.lookup id pts)

let mem (pr:promise 'e 'a) (pts:parallel_traces 'e) = pr.id `mem_id` pts /\ 'a == (sel_id pr.id pts)._1

let sel_lt pr pts = (sel_id pr.id pts)._3
let sel_r pr pts = (sel_id pr.id pts)._2
let sel_a pr pts = (sel_id pr.id pts)._1

let async r lt pts =
  let (| n, m |) = pts in
  let m' = M.insert (n+1) (| _, r, lt |) m in
  admit ();
  let pts' : parallel_traces _ = (| n + 1, m' |) in
  (Promise (n+1), pts')

let await pr pts =
  let (| n, m |) = pts in
  let m' = M.insert pr.id (| _, sel_r pr pts, [] |) m in
  admit ();
  (| n, m' |)

let closed_atrace pts tr = admit ()
let closed_atrace_async h pts r lt = admit ()
let closed_atrace_await_pr pr h pt = admit ()
let closed_atrace_produce ev h pts = admit ()

let size_pts pr = admit ()

let fulfilled pr pts : bool =
  match sel_lt pr pts with
  | [] -> true
  | _ -> false

let waiting pr pts : bool =
  match sel_lt pr pts with
  | EAwait _::_ -> true
  | _ -> false

let can_progress pr pts =
  not (fulfilled pr pts) && not (waiting pr pts)

let generate_all_promises #e pts : list (a:Type0 & pr:promise e a{pr `mem` pts}) =
  let (| n, m |) = pts in
  let rec aux (i:nat{i < n}) : list (a:Type0 & pr:promise e a{pr `mem` pts}) = begin
    let pr : promise e (sel_id i pts)._1 = Promise i in
    if i = 0 then [(| _, pr |)]
    else ([(| _, pr |)] @ aux (i-1))
  end in
  if 0 < n then aux (n-1)
  else []


let get_next #e pts =
  let l = filter (fun (apr:(a:Type0 & pr:promise e a{pr `mem` pts})) -> can_progress (dsnd apr) pts) (generate_all_promises pts) in
  admit ();
  l

let simple_progress (pr:promise 'e 'a) (pts:(parallel_traces 'e){pr `mem` pts /\ can_progress pr pts})
  : 'e * pts':parallel_traces 'e{size_pts pts' < size_pts pts} =
  let (| n, m |) = pts in
  match sel_lt pr pts with
  | ev :: tl -> begin
    let m' = M.insert pr.id (| _, sel_r pr pts, tl |) m in
    admit ();
    (ev, (| n, m' |))
  end

(**
let normalize (pts:parallel_traces 'e) : parallel_traces 'e =
  let l = filter (fun (apr:(a:Type0 & pr:promise e a{pr `mem` pts})) -> can_progress (dsnd apr) pts) (generate_all_promises pts) in **)

let progress pr pts = admit ()
