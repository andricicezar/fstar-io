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
  unit -> SST unit (fun _ -> True) (fun _ _ _ -> True)

type lib_type =
  ref (ref int) -> SST callback (fun _ -> True) (fun _ _ _ -> True)

let prog (lib : lib_type) : SST unit (requires fun h0 -> True) (ensures fun h0 _ h1 -> True) =
  let secret : ref int = sst_alloc 42 in
  let r : ref (ref int) = sst_alloc_shared #(SRef SNat) (sst_alloc_shared #(SNat) 0) in
  assert (!secret == 42);
  let cb = lib r in
  assume (!secret == 42);
  // r := sst_alloc_shared #(SNat) 1;
  let v : ref int = sst_alloc_shared #(SNat) 1 in
  let h = get_heap () in
  sst_write_shareable #(SRef SNat) r v;
  assert (!secret == 42);
  cb ();
  assume (!secret == 42)
