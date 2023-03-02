open Prims
type ('a, 'lt, 'r) the_p = unit
exception Something_went_really_bad 
let (uu___is_Something_went_really_bad : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Something_went_really_bad -> true | uu___ -> false
let rec (skip_partial_calls : Prims.int MIO_Sig.mio -> unit -> Prims.int) =
  fun tree ->
    fun uu___ ->
      match tree with
      | Free.Return y -> y
      | Free.PartialCall (pre, k) -> skip_partial_calls (k ()) ()
      | uu___1 -> FStar_Exn.raise Something_went_really_bad
let (execute : (unit -> (Prims.int, unit, unit) MIO.dm_gmio) -> Prims.int) =
  fun w ->
    let dm_tree = Obj.magic (w ()) in
    let dm_tree' = dm_tree in skip_partial_calls dm_tree' ()
