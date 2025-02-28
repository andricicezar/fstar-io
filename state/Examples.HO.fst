module Examples.HO

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

type f_eqx (pspec:targetlang_pspec) = x:ref int -> ST (resexn unit) (requires (fun h0 -> (Mktuple3?._1 pspec) h0 /\ satisfy x (prref_c))) (ensures (fun h0 r h1 -> (Mktuple3?._1 pspec) h1 /\ (Mktuple3?._3 pspec) h0 h1 /\ (Inr? r \/ sel h0 x == sel h1 x)))

let f_pspec pspec : pck_spec pspec =
 (SpecErr false (ref int) (exportable_refinement pspec
                  (ref int)
                  Leaf
                  (fun _ -> l_True))
                .c_styp
              (fun x h0 -> (Mktuple3?._1 pspec) h0 /\ satisfy x (prref_c))
              unit
              (safe_importable_is_importable pspec unit Leaf).c_styp
              (fun x h0 r h1 -> (Mktuple3?._1 pspec) h1 /\ (Mktuple3?._3 pspec) h0 h1 /\ (Inr? r \/ sel h0 x == sel h1 x)))

let f_spec : pck_spec concrete_spec = f_pspec concrete_spec

let f_eqx_is_safe_importable pspec : safe_importable_to pspec (f_eqx pspec) (Node (f_pspec pspec) Leaf Leaf) =
  solve
(**
  safe_importable_arrow pspec
    (ref int) unit
    Leaf Leaf
    (fun x h0 -> (Mktuple3?._1 pspec) h0 /\ satisfy x (prref_c))
    (fun x h0 r h1 -> (Mktuple3?._1 pspec) h1 /\ (Mktuple3?._3 pspec) h0 h1 /\ (Inr? r \/ sel h0 x == sel h1 x))**)

let f_hoc : hoc concrete_spec f_spec =
EnforcePost
    (fun _ -> ())
    (fun _ _ -> ())
    (fun rx ->
      let rx :ref int = rx in
      recall (contains_pred rx);
      let x = sst_read rx in
      let eh0 = get_heap () in
      let check : cb_check concrete_spec (ref int) (resexn unit) (fun x -> sst_pre (fun h0 -> satisfy x (prref_c))) (fun x -> sst_post _ _ (fun h0 r h1 -> Inr? r \/ sel h0 x == sel h1 x)) rx eh0 =
        (fun kres -> if x = sst_read rx then Inl () else Inr (Contract_failure "x has changed")) in
      (| eh0, check |))

let f_pkhoc : pck_hoc concrete_spec =
  (| f_spec, f_hoc |)

let f_tree : hoc_tree (Node f_spec Leaf Leaf) =
  Node f_pkhoc Leaf Leaf

let sit : src_interface1 = {
  specs = (fun preds -> Node (f_pspec preds) Leaf Leaf);
  hocs = f_tree;
  ct = f_eqx;
  c_ct = f_eqx_is_safe_importable;
  psi = fun _ _ _ -> True
}

(**
val unsafe_f : mk_interm_arrow (ref int) (resexn unit)
let unsafe_f x =
  recall (contains_pred x);
  recall (is_shared x);
  sst_write x 0;
  Inl ()**)

val tgt_f : ctx_tgt1 (comp_int_src_tgt1 sit)
let tgt_f inv prref hrel read write alloc x =
  write x 0;
  Inl ()

val prog : prog_src1 sit
let prog f =
  let r = sst_alloc_shared #SNat 5 in
  witness (contains_pred r);
  witness (is_shared r);
  match f r with
  | Inl () -> 0
  | Inr _ -> -1

(* Calling SecRef* on it *)

let compiled_prog =
  compile_pprog1 #sit prog

let whole_prog : whole_tgt1 =
  link_tgt1 compiled_prog tgt_f

let r = whole_prog ()
let _ =
  match r with
  | 0 -> FStar.IO.print_string "Contract failed\n"
  | -1 -> FStar.IO.print_string "Contract succedded\n"
  | _ -> FStar.IO.print_string "Impossible\n"
