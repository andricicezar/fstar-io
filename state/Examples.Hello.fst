module Examples.Hello

open FStar.FiniteSet.Base
open FStar.Ghost
open FStar.Monotonic.Heap
open FStar.Preorder
open FStar.Tactics.Typeclasses
open LabeledRefs
open Witnessable

let hello0 ()
  : SST (ref int)
    (requires (fun h0 -> True))
    (ensures (fun h0 _ h1 -> True)) =
    sst_alloc_shareable #SNat 1

let hello ()
  : SST unit
    (requires (fun h0 -> True))
    (ensures (fun h0 () h1 -> True)) =
    let ref_ll = sst_alloc_shareable #SNat 1 in 
    ()

let hello_read_write ()
  : SST unit
    (requires (fun h0 -> False))
    (ensures (fun h0 () h1 -> True)) =
    let ref = sst_alloc_shareable #SNat 1 in 
    let v = !ref in
    ref := v + 1;
    ()
