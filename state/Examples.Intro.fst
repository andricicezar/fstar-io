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
let ulib_ty = TArr (TRef (TRef TNat)) ucb_ty

(* Trivial library *)

val triv_cb : elab_poly_typ ucb_ty
let triv_cb _ _ _ _ =
  raise_val ()

val triv_lib : elab_poly_typ ulib_ty
let triv_lib read write alloc r =
  triv_cb read write alloc

(* iter on linked lists *)
let rec ll_iter #a (f : a -> SST unit (fun _ -> True) (fun _ _ _ -> True)) (l: linkedList a) :
  SST unit (fun _ -> True) (fun _ _ _ -> True)
= match l with
  | LLNil -> ()
  | _ -> ()

(* Adversarial library *)

#push-options "--z3rlimit 10000"
val adv_lib : elab_poly_typ ulib_ty
let adv_lib #inv #prref #hrel bt_read bt_write bt_alloc r =
  let r : ref (ref int) = downgrade_val r in
  let g : ref (linkedList (ref int)) = bt_alloc #(TLList (TRef TNat)) LLNil in
  (fun _ ->
    let v = bt_read #(TRef TNat) r in
    bt_write #(TLList (TRef TNat)) g (LLCons v g);
    let l = bt_read #(TLList (TRef TNat)) g in
    // ll_iter (fun r' -> bt_write #TNat r' 0) l;
    let r0 : ref int = bt_alloc #TNat 0 in
    bt_write #(TRef TNat) r r0;
    raise_val ()
  )
