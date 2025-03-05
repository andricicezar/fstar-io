module Examples.Intro

open FStar.Tactics
open FStar.Tactics.Typeclasses
open SharedRefs
open HigherOrderContracts
open PolyIface
open Compiler
open Witnessable
open SpecTree

#set-options "--print_universes"

type callback a3p =
  mk_poly_arrow a3p unit unit

type lib_type a3p =
  mk_poly_arrow
    a3p
    (ref (ref int))
    (callback a3p) #(witnessable_arrow u#0 u#_ _ _ _ _)
                      (* ^ F* wrongly infers that first universe as 1 instead
                         of zero, which is wrong. Work around it. *)

instance safe_importable_lib_type a3p : safe_importable_to a3p (lib_type a3p) Leaf =
  poly_iface_is_safely_importable a3p (lib_type a3p)
    #(poly_iface_arrow a3p (ref (ref int)) (callback a3p) #solve #(poly_iface_arrow a3p unit unit))

(* Calling SecRef* on it *)

let sit : src_interface1 = {
  specs = (fun a3p -> Leaf);
  hocs = Leaf;
  ct = lib_type;
  c_ct = safe_importable_lib_type;
  psi = fun _ _ _ -> True
}

#push-options "--z3rlimit 10000" (* very flaky for some reason. *)
#restart-solver
let prog (lib : lib_type c3p) : SST int (requires fun h0 -> True) (ensures fun h0 _ h1 -> True) =
  let secret : ref int = sst_alloc 42 in
  let r : ref (ref int) = sst_alloc_shared #(SRef SNat) (sst_alloc_shared 0) in
  witness (contains_pred r);
  witness (is_shared r);
  let cb = lib r in
  let v : ref int = sst_alloc_shared 1 in
  let h = get_heap () in
  (* Sad, but these asserts seem to help. They are really just the precondition
  of sst_write. *)
  assert (h `contains` r);
  assert (~(compare_addrs r map_shared));
  assert (
    (forall t. to_Type t == int ==>
      forall_refs_heap contains_pred h #t 1 /\
      (is_shared r h ==> forall_refs_heap is_shared h #t 1)));
  sst_write r v;
  cb ();
  let v = !secret in
  assert (v == 42); (* we know statically that the secret has not changed. *)
  v (* return it, the ocaml code prints it out *)
#pop-options

let compiled_prog =
  compile_pprog1 #sit prog

(* Unverified libraries (context) *)

(* Trivial library *)

val triv_lib : ctx_tgt1 (comp_int_src_tgt1 sit)
let triv_lib read write alloc r =
  (fun _ -> ())

let whole_triv : whole_tgt1 =
  link_tgt1 compiled_prog triv_lib

(* Adversarial library *)
#push-options "--z3rlimit 10000"
val adv_lib : ctx_tgt1 (comp_int_src_tgt1 sit)
let adv_lib #a3p read write alloc r =
  let g : ref (linkedList (ref int)) = alloc #(SLList (SRef SNat)) LLNil in
  (* iteration on linked list, using fuel to ensure termination *)
  let rec ll_iter (n:nat) (l : linkedList (ref int)) : ST unit (pre_poly_arrow a3p l) (post_poly_arrow a3p) =
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

let whole_adv : whole_tgt1 =
  link_tgt1 compiled_prog adv_lib

let secret_is = whole_adv ()
let _ =
  match secret_is with
  | 42 -> FStar.IO.print_string "Secret is 42! Correct!\n"
  | _ -> FStar.IO.print_string "Impossible! Secret is NOT 42! Something went wrong!\n"