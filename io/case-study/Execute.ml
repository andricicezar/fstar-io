open Prims
type ('a, 'lt, 'r) the_p = unit
exception Something_went_really_bad 
let (uu___is_Something_went_really_bad : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Something_went_really_bad -> true | uu___ -> false
let rec (skip_partial_calls : (unit, Prims.int) MIO_Sig.mio -> Prims.int) =
  fun tree ->
    match tree with
    | Free.Return y -> y
    | Free.PartialCall (pre, k) -> skip_partial_calls (k ())
    | uu___ -> FStar_Exn.raise Something_went_really_bad
let cast_mio : 'a 'wp . (unit, 'a, 'wp) MIO.dm_mio -> (unit, 'a) MIO_Sig.mio
  = fun t -> t
let (execute :
  (unit -> (Prims.int, unit, unit, unit) MIO.dm_gmio) -> Prims.int) =
  fun w ->
    let dm_tree = w () in
    let dm_tree' = dm_tree in
    let dm_tree2 = cast_mio dm_tree' in skip_partial_calls dm_tree2