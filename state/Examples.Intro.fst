module Examples.Intro

open FStar.FiniteSet.Base
open FStar.Ghost
open FStar.Monotonic.Heap
open FStar.Preorder
open FStar.Tactics
open FStar.Tactics.Typeclasses
open SharedRefs
open Witnessable

// TODO: Make lib effectful
let prog (lib : (ref (ref int) -> cb:(unit -> unit))) : SST unit (requires fun h0 -> True) (ensures fun h0 _ h1 -> True) =
  let secret : ref int = sst_alloc 42 in
  let r : ref (ref int) = sst_alloc_shared #(SRef SNat) (sst_alloc_shared #(SNat) 0) in
  let cb = lib r in
  // r := sst_alloc_shared #(SNat) 1;
  let v : ref int = sst_alloc_shared #(SNat) 1 in
  assume (forall h0. (forall (t: shareable_typ).
              to_Type t == ref int ==>
              forall_refs_heap contains_pred h0 #t v /\
              (is_shared r h0 ==> forall_refs_heap is_shared h0 #t v))) ;
  sst_write_ref r v;
  cb ();
  assert (!secret == 42)
