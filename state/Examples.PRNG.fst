module Examples.PRNG

open FStar.FiniteSet.Base
open FStar.Ghost
open FStar.Monotonic.Heap
open FStar.Preorder
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Universe
open STLC
open Backtranslation.STLCToPolyIface
open SharedRefs
open Witnessable
open Compiler
open HigherOrderContracts
open PolyIface
open SpecTree

val generate_nr : seed:int -> count:int -> int
let generate_nr seed count = seed+count

let post = fun h0 _ h1 -> modifies_only_shared_and_encapsulated h0 h1 /\ gets_shared Set.empty h0 h1

type prog_type =
  seed:int -> SST (raise_t unit -> SST int (fun _ -> True) post) (fun _ -> True) post

val prng : prog_type
let prng (seed:int) =
  let counter : ref int = sst_alloc_shared 0 in
  witness (contains_pred counter) ;
  witness (is_shared counter) ;
  fun _ -> recall (contains_pred counter);
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

instance exportable_prog pspec : exportable_from pspec (mk_targetlang_arrow pspec int (mk_targetlang_arrow pspec (raise_t unit) int)) Leaf =
  targetlang_is_exportable _ pspec #(targetlang_arrow pspec int (mk_targetlang_arrow pspec (raise_t unit) int) #_ #(targetlang_arrow pspec (raise_t unit) int))

let sit : src_interface2 = {
  specs = (fun _ -> Leaf);
  hocs = Leaf;
  pt = (fun pspec -> mk_targetlang_arrow pspec int (mk_targetlang_arrow pspec (raise_t unit) int));
  c_pt = (fun pspec -> exportable_prog pspec);
}

val prng' : prog_src2 sit
let prng' seed =
  let cb = prng seed in
  (fun _ -> cb (raise_val ()))

let compiled_prog =
  compile_pprog2 #sit prng'

val some_ctx : ctx_tgt2 (comp_int_src_tgt2 sit)
let some_ctx inv prref hrel read write alloc prng =
  let cb = prng 5 in
  let _ = cb (raise_val ()) in
  let _ = cb (raise_val ()) in
  cb (raise_val ())

let whole : whole_tgt2 =
  link_tgt2 compiled_prog some_ctx

let r = whole ()
let _ =
  match r with
  | 8 -> FStar.IO.print_string "Success"
  | _ -> FStar.IO.print_string "Something went wrong!"
