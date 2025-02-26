module Examples.Intro

open FStar.FiniteSet.Base
open FStar.Ghost
open FStar.Monotonic.Heap
open FStar.Preorder
open FStar.Tactics
open FStar.Tactics.Typeclasses
open SharedRefs
open Witnessable

type callback =
  unit -> SST unit (fun _ -> True) (fun h0 _ h1 -> modifies_only_shared_and_encapsulated h0 h1 /\ gets_shared Set.empty h0 h1)

type lib_type =
  r:ref (ref int) -> SST callback (fun _ -> witnessed (contains_pred r) /\ witnessed (is_shared r)) (fun h0 _ h1 -> modifies_only_shared_and_encapsulated h0 h1 /\ gets_shared Set.empty h0 h1)

let prog (lib : lib_type) : SST unit (requires fun h0 -> True) (ensures fun h0 _ h1 -> True) =
  let secret : ref int = sst_alloc 42 in
  // let h = get_heap () in
  // assert (is_private secret h);
  let r : ref (ref int) = sst_alloc_shared #(SRef SNat) (sst_alloc_shared #(SNat) 0) in
  // assert (!secret == 42);
  // assert (is_private secret h);
  // let h0 = get_heap () in
  assume (witnessed (contains_pred r) /\ witnessed (is_shared r)) ;
  let cb = lib r in
  // let h1 = get_heap () in
  // assume (modifies_only_shared h0 h1);
  // assert (is_private secret h);
  // assert (~ (is_shared secret h));
  // assert (!secret == 42);
  let v : ref int = sst_alloc_shared #(SNat) 1 in
  // let h = get_heap () in
  sst_write_shareable #(SRef SNat) r v;
  assume (!secret == 42);
  cb ();
  assume (!secret == 42)
