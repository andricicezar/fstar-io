module Examples.Intro

open FStar.Ghost
open FStar.Monotonic.Heap
open FStar.Preorder
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Universe
open SharedRefs
open HigherOrderContracts
open TargetLang
open Compiler
open Witnessable
open SpecTree

#set-options "--print_universes"

type callback pspec =
  mk_targetlang_arrow pspec unit unit

type lib_type pspec =
  mk_targetlang_arrow
    pspec
    (ref (ref int))
    (callback pspec) #(witnessable_arrow u#0 u#_ _ _ _ _)
                      (* ^ F* wrongly infers that first universe as 1 instead
                         of zero, which is wrong. Work around it. *)

instance safe_importable_lib_type pspec : safe_importable_to pspec (lib_type pspec) Leaf =
  targetlang_is_safely_importable pspec (lib_type pspec)
    #(targetlang_arrow pspec (ref (ref int)) (callback pspec) #solve #(targetlang_arrow pspec unit unit))

(* Calling SecRef* on it *)

let sit : src_interface1 = {
  specs = (fun pspec -> Leaf);
  hocs = Leaf;
  ct = lib_type;
  c_ct = safe_importable_lib_type;
  psi = fun _ _ _ -> True
}

#push-options "--z3rlimit 10000" (* very flaky for some reason. *)
#restart-solver
let prog (lib : lib_type concrete_spec) : SST int (requires fun h0 -> True) (ensures fun h0 _ h1 -> True) =
  let secret : ref int = sst_alloc 42 in
  let r : ref (ref int) = sst_alloc_shared #(SRef SNat) (sst_alloc_shared 0) in
  witness (contains_pred r) ;
  witness (is_shared r) ;
  let cb = lib r in
  let v : ref int = sst_alloc_shared 1 in
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
let triv_lib inv prref hrel read write alloc r =
  (fun _ -> ())

let whole_triv : whole_tgt1 =
  link_tgt1 compiled_prog triv_lib

(* Adversarial library *)
#push-options "--z3rlimit 10000"
val adv_lib : ctx_tgt1 (comp_int_src_tgt1 sit)
let adv_lib inv prref hrel read write alloc r =
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

let whole_adv : whole_tgt1 =
  link_tgt1 compiled_prog adv_lib
