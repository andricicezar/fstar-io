module Examples.Intro

open FStar.FiniteSet.Base
open FStar.Ghost
open FStar.Monotonic.Heap
open FStar.Preorder
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Universe
open STLC
open Backtranslation.STLCToTargetLang
open SharedRefs
open Witnessable

let lemma_modifies_only_shared_and_encapsulated h0 h1 #a #rel (r : mref a rel) :
  Lemma
    (requires modifies_only_shared_and_encapsulated h0 h1 /\ h0 `contains` r /\ ~(compare_addrs r map_shared) /\ ~(is_shared r h0 \/ is_encapsulated r h0))
    (ensures sel h0 r == sel h1 r)
= ()

type callback =
  unit -> SST unit (fun _ -> True) (fun h0 _ h1 -> modifies_only_shared_and_encapsulated h0 h1 /\ gets_shared Set.empty h0 h1)

type lib_type =
  r:ref (ref int) -> SST callback (fun _ -> witnessed (contains_pred r) /\ witnessed (is_shared r)) (fun h0 _ h1 -> modifies_only_shared_and_encapsulated h0 h1 /\ gets_shared Set.empty h0 h1)

#push-options "--z3rlimit 10000"
let prog (lib : lib_type) : SST unit (requires fun h0 -> True) (ensures fun h0 _ h1 -> True) =
  let secret : ref int = sst_alloc 42 in
  let r : ref (ref int) = sst_alloc_shared #(SRef SNat) (sst_alloc_shared #(SNat) 0) in
  witness (contains_pred r) ;
  witness (is_shared r) ;
  let cb = lib r in
  let v : ref int = sst_alloc_shared #(SNat) 1 in
  sst_write_shareable #(SRef SNat) r v;
  cb ();
  assert (!secret == 42)
#pop-options

(* Unverified libraries *)

let ucb_ty = TArr TUnit TUnit
let ulib_ty = TArr (TRef TNat) ucb_ty

(* Trivial library *)

val triv_cb : elab_poly_typ ucb_ty
let triv_cb _ _ _ _ =
  raise_val ()

val triv_lib : elab_poly_typ ulib_ty
let triv_lib read write alloc r =
  triv_cb read write alloc

(* Adversarial library *)

#push-options "--z3rlimit 10000"
val adv_cb : ref (ref int) -> ref (linkedList (ref int)) -> elab_poly_typ ucb_ty
let adv_cb r g #inv #prref #hrel bt_read bt_write bt_alloc _ =
  assume (forall h0. inv h0 /\ prref r) ; // Why??
  let v = bt_read #(TRef TNat) r in
  // bt_write #(TLList (TRef TNat)) g (LLCons v g); // This fails too, not great for unverified code
  raise_val ()

(* iter on linked lists *)
let rec ll_iter #a (f : a -> SST unit (fun _ -> True) (fun _ _ _ -> True)) (l: linkedList a) :
  SST unit (fun _ -> True) (fun _ _ _ -> True)
= match l with
  | LLNil -> ()
  | _ -> ()

(* WRONG approach below *)
#push-options "--z3rlimit 10000"
val adv_lib : lib_type
let adv_lib r =
  let g : ref (linkedList (ref int)) = sst_alloc_shared #(SLList (SRef SNat)) LLNil in
  (fun () ->
    recall (contains_pred r) ;
    let v = sst_read #(SRef SNat) r in
    // sst_write_shareable #(SLList (SRef SNat)) g (LLCons v g) ;
    // ll_iter (fun r' -> sst_write_shareable #SNat r' 0) !g;
    // sst_write_shareable #SNat r (sst_alloc_shared #SNat 0)
    ()
  )
