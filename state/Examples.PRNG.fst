module Examples.PRNG

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
  seed:int -> SST (unit -> SST int (fun _ -> True) post) (fun _ -> True) post

(* Calling SecRef* on it *)

instance exportable_prog a3p : exportable_from a3p (mk_poly_arrow a3p int (mk_poly_arrow a3p unit int) #(witnessable_arrow u#0 u#_ _ _ _ _)) Leaf =
  poly_iface_is_exportable _ a3p #(poly_iface_arrow a3p int (mk_poly_arrow a3p unit int) #_ #(poly_iface_arrow a3p unit int))

let sit : src_interface2 = {
  specs = (fun _ -> Leaf);
  hocs = Leaf;
  pt = (fun a3p -> mk_poly_arrow a3p int (mk_poly_arrow a3p unit int));
  c_pt = (fun a3p -> exportable_prog a3p);
}

val prng : prog_src2 sit
let prng (seed:int) =
  let counter : mref int (fun v v' -> b2t(v <= v')) = sst_alloc 0 in
  encapsulate counter;
  witness (contains_pred counter) ;
  witness (is_encapsulated counter) ;
  fun _ -> 
    recall (contains_pred counter);
    recall (is_encapsulated counter);
    let ccounter = sst_read counter in
    sst_write counter (ccounter + 1);
    generate_nr seed (ccounter + 1)

let compiled_prog =
  compile_pprog2 #sit prng

val some_ctx : ctx_tgt2 (comp_int_src_tgt2 sit)
let some_ctx _ _ _ prng =
  let cb = prng 5 in
  let _ = cb () in
  let _ = cb () in
  cb ()

let whole : whole_tgt2 =
  link_tgt2 compiled_prog some_ctx

let r = whole ()
let _ =
  match r with
  | 8 -> FStar.IO.print_string "Success!\n"
  | _ -> FStar.IO.print_string "Something went wrong!\n"
