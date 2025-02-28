module Examples.PRNG

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
open HigherOrderContracts
open TargetLang

assume val generate_nr : seed:int -> count:int -> int

let post = fun h0 _ h1 -> modifies_only_shared_and_encapsulated h0 h1 /\ gets_shared Set.empty h0 h1

type prog_type =
  seed:int -> SST (unit -> SST int (fun _ -> True) post) (fun _ -> True) post

let prng (seed:int) : SST (unit -> SST int (fun _ -> True) post) (fun _ -> True) post =
  let counter : ref int = sst_alloc_shared 0 in
  witness (contains_pred counter) ;
  witness (is_shared counter) ;
  fun () -> recall (contains_pred counter);
          recall (is_shared counter);
          let ccounter = sst_read counter in
          sst_write_shareable counter (ccounter + 1);
          generate_nr seed (ccounter + 1)

let vcall_ty = TArr TNat (TArr TUnit TNat)
let ucaller_ty = TArr vcall_ty TNat

val triv_caller : elab_poly_typ ucaller_ty
let triv_caller read write alloc r =
  raise_val 42

val single_use_caller : elab_poly_typ ucaller_ty
let single_use_caller #inv #prref #hrel bt_read bt_write bt_alloc r =
  let seed = 5 in
  let rnd = downgrade_val #int (r (raise_val seed) (raise_val ())) in
  raise_val rnd

(* Calling SecRef* on it *)

instance targetlang_arrow_helper pspec
  : targetlang pspec (raise_t unit -> SST int (fun _ -> True) post)
  = { wt = witnessable_arrow (raise_t unit) int _ _ }

instance imp_prog : exportable_from prog_type = {
  c_styp  = witnessable_arrow int  (unit -> SST int (fun _ -> True) post) _ _ ;
  ityp = mk_interm_arrow int (raise_t unit -> SST int (fun _ -> True) post) ;
  c_ityp = targetlang_arrow _ int (raise_t unit -> SST int (fun _ -> True) post) ;
  export = (fun f z x -> f z (downgrade_val x)) ;
  lemma_export_preserves_prref = (fun x -> ()) ;
}

let sit : src_interface2 = {
  pt = prog_type ;
  c_pt = solve ;
}


let compiled_prog =
  compile_pprog2 #sit prng

let tmp = ctx_tgt2 (comp_int_src_tgt2 sit)
// let mm = link_tgt2 compiled_prog single_use_caller
