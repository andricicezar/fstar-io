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
open HigherOrderContracts
open TargetLang
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

(* Calling SecRef* on it *)

instance imp_cb : safe_importable_to callback = {
  c_styp = witnessable_arrow unit unit _ _ ;
  ityp = mk_interm_arrow unit unit ;
  c_ityp = targetlang_arrow _ unit unit ;
  safe_import = (fun f x -> f x) ;
  lemma_safe_import_preserves_prref = (fun x -> ())
}

instance imp_lib : safe_importable_to lib_type = {
  c_styp = witnessable_arrow (ref (ref int)) callback _ _ ;
  ityp = mk_interm_arrow (ref (ref int)) imp_cb.ityp ;
  c_ityp = targetlang_arrow _ (ref (ref int)) imp_cb.ityp ;
  safe_import = (fun f r -> imp_cb.safe_import (f r)) ;
  lemma_safe_import_preserves_prref = (fun f -> ())
}

let sit : src_interface1 = {
  ct = lib_type ;
  c_ct = solve ;
  psi = fun _ _ _ -> True
}

let compiled_prog =
  compile_pprog1 #sit prog

(* Unverified libraries (context) *)

(* Trivial library *)

val triv_lib : ctx_tgt1 (comp_int_src_tgt1 sit)
let triv_lib #fl inv prref hrel read write alloc r =
  (fun () -> ())

let whole_triv : whole_tgt1 =
  link_tgt1 compiled_prog triv_lib

(* Adversarial library *)
#push-options "--z3rlimit 10000"
// val adv_lib : ctx_tgt1 (comp_int_src_tgt1 sit)
let adv_lib_t =
  #fl: erased tflag ->
  inv  : (heap -> Type0) ->
  prref: mref_pred ->
  hrel : FStar.Preorder.preorder heap ->
  read :  ttl_read fl inv prref hrel ->
  write : ttl_write fl inv prref hrel ->
  alloc : ttl_alloc fl inv prref hrel  ->
  mk_targetlang_arrow (mk_targetlang_pspec inv prref hrel) (ref (ref int)) (mk_targetlang_arrow (mk_targetlang_pspec inv prref hrel) (raise_t unit) unit)
val adv_lib : adv_lib_t

let adv_lib #fl inv prref hrel read write alloc r =
  let g : ref (linkedList (ref int)) = alloc #(SLList (SRef SNat)) LLNil in
  (* iteration on linked list, using fuel to ensure termination *)
  let pspec = mk_targetlang_pspec inv prref hrel in
  let rec ll_iter (n:nat) (l : linkedList (ref int)) : ST unit (TargetLang.pre_targetlang_arrow pspec l) (TargetLang.post_targetlang_arrow pspec) =
    if n = 0 then () else
    match l with
    | LLNil -> ()
    | LLCons r' r ->
      write #SNat r' 0 ;
      let l' = read #(SLList (SRef SNat)) r in
      ll_iter (n-1) l'
  in
  (fun _ ->
    let v = read #(SRef SNat) r in
    write #(SLList (SRef SNat)) g (LLCons v g);
    let l = read #(SLList (SRef SNat)) g in
    ll_iter 1000 l;
    let r0 : ref int = alloc #SNat 0 in
    write #(SRef SNat) r r0;
    ()
  )

let pf : squash (adv_lib_t == ctx_tgt1 (comp_int_src_tgt1 sit)) =
  assert (adv_lib_t == ctx_tgt1 (comp_int_src_tgt1 sit)) by begin
    norm [delta_only [`%comp_int_src_tgt1; `%Mktgt_interface1?.ct; `%sit; `%adv_lib_t; `%ctx_tgt1];
          delta_only [`%mk_targetlang_arrow; `%Mksrc_interface1?.c_ct; `%imp_lib; `%Mksafe_importable_to?.ityp];
          delta_only [`%mk_interm_arrow; `%imp_cb];
          iota ; Prelude.unascribe];
    dump "";
    tadmit()
  end

// #push-options "--ugly"
let whole_adv : whole_tgt1 =
  let _ = pf in
  link_tgt1 compiled_prog (coerce_eq () (adv_lib <: adv_lib_t))
