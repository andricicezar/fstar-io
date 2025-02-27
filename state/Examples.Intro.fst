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
open Compiler

type callback =
  unit -> SST unit (fun _ -> True) (fun h0 _ h1 -> modifies_only_shared_and_encapsulated h0 h1 /\ gets_shared Set.empty h0 h1)

type lib_type =
  r:ref (ref int) -> SST callback (fun _ -> witnessed (contains_pred r) /\ witnessed (is_shared r)) (fun h0 _ h1 -> modifies_only_shared_and_encapsulated h0 h1 /\ gets_shared Set.empty h0 h1)

#push-options "--z3rlimit 10000"
let prog (lib : lib_type) : SST int (requires fun h0 -> True) (ensures fun h0 _ h1 -> True) =
  let secret : ref int = sst_alloc 42 in
  let r : ref (ref int) = sst_alloc_shared #(SRef SNat) (sst_alloc_shared 0) in
  witness (contains_pred r) ;
  witness (is_shared r) ;
  let cb = lib r in
  let v : ref int = sst_alloc_shared 1 in
  sst_write r v;
  cb ();
  assert (!secret == 42);
  0
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

(* Adversarial library *)

val adv_lib : elab_poly_typ ulib_ty
let adv_lib #inv #prref #hrel bt_read bt_write bt_alloc r =
  let r : ref (ref int) = downgrade_val r in
  let g : ref (linkedList (ref int)) = bt_alloc #(TLList (TRef TNat)) LLNil in
  (* iteration on linked list, using fuel to ensure termination *)
  let pspec = mk_targetlang_pspec inv prref hrel in
  let rec ll_iter (n:nat) (l : linkedList (ref int)) : ST unit (TargetLang.pre_targetlang_arrow pspec l) (TargetLang.post_targetlang_arrow pspec) =
    if n = 0 then () else
    match l with
    | LLNil -> ()
    | LLCons r' r ->
      bt_write #TNat r' 0 ;
      let l' = bt_read #(TLList (TRef TNat)) r in
      ll_iter (n-1) l'
  in
  (fun _ ->
    let v = bt_read #(TRef TNat) r in
    bt_write #(TLList (TRef TNat)) g (LLCons v g);
    let l = bt_read #(TLList (TRef TNat)) g in
    ll_iter 1000 l;
    let r0 : ref int = bt_alloc #TNat 0 in
    bt_write #(TRef TNat) r r0;
    raise_val ()
  )

(* Calling SecRef* on it *)

let sit : src_interface1 = {
  ct = lib_type ;
  c_ct = admit () ;
  psi = fun _ _ _ -> True
}

let compiled_prog =
  compile_pprog1 #sit prog
