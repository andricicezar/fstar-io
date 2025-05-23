module Examples.Hello

open FStar.FiniteSet.Base
open FStar.Ghost
open FStar.Monotonic.Heap
open FStar.Preorder
open FStar.Tactics.Typeclasses
open LabeledRefs
open Witnessable

let hello0 ()
  : LR (ref int)
    (requires (fun h0 -> True))
    (ensures (fun h0 _ h1 -> True)) =
    lr_alloc_shareable #SNat 1

let hello ()
  : LR unit
    (requires (fun h0 -> True))
    (ensures (fun h0 () h1 -> True)) =
    let ref_ll = lr_alloc_shareable #SNat 1 in 
    ()

let hello_read_write ()
  : LR unit
    (requires (fun h0 -> False))
    (ensures (fun h0 () h1 -> True)) =
    let ref = lr_alloc_shareable #SNat 1 in 
    let v = !ref in
    ref := v + 1;
    ()
