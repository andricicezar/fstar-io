module Examples.HO

open FStar.Ghost
open FStar.Monotonic.Heap
open FStar.Preorder
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Universe
open SharedRefs
open HigherOrderContracts
open PolyIface
open Compiler
open Witnessable
open SpecTree

#set-options "--print_universes"

type f_eqx (a3p:threep) = x:ref int -> ST (resexn unit) (requires (fun h0 -> inv a3p h0 /\ satisfy x (prref a3p))) (ensures (fun h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1 /\ (Inr? r \/ sel h0 x == sel h1 x)))

let f_a3p (a3p:threep) : pck_spec =
 (SpecErr00 false (ref int) (witnessable_ref int)
    (fun x h0 -> inv a3p h0 /\ satisfy x (prref a3p))
    unit
    witnessable_unit
    (fun x h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1 /\ (Inr? r \/ sel h0 x == sel h1 x)))

let f_spec : pck_spec = f_a3p c3p

let f_eqx_is_safe_importable a3p : safe_importable_to a3p (f_eqx a3p) (Node (f_a3p a3p) Leaf Leaf) =
  safe_importable_arrow a3p
    (ref int) unit
    Leaf Leaf
    #(exportable_ref a3p int)
    #(safe_importable_is_importable a3p unit Leaf #(safe_importable_unit a3p))
    (fun x h0 -> inv a3p h0 /\ satisfy x (prref a3p))
    (fun x h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1 /\ (Inr? r \/ sel h0 x == sel h1 x))

let f_hoc : hoc c3p f_spec =
  EnforcePost
    (fun _ -> ())
    (fun _ _ -> ())
    (fun rx ->
      let rx :ref int = rx in
      recall (contains_pred rx);
      let x = sst_read rx in
      let eh0 = get_heap () in
      let check : cb_check c3p (ref int) (resexn unit) (fun x -> sst_pre (fun h0 -> satisfy x (prref_c))) (fun x -> sst_post _ _ (fun h0 r h1 -> Inr? r \/ sel h0 x == sel h1 x)) rx eh0 =
        (fun kres -> if x = sst_read rx then Inl () else Inr (Contract_failure "x has changed")) in
      (| eh0, check |))

let f_pkhoc : pck_hoc c3p =
  (| f_spec, f_hoc |)

let f_tree : hoc_tree c3p (Node f_spec Leaf Leaf) =
  Node f_pkhoc Leaf Leaf

let sit : src_interface1 = {
  specs = (fun preds -> Node (f_a3p preds) Leaf Leaf);
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
let tgt_f read write alloc x =
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










type f_xeq5 = x:ref int -> SST (resexn int)
  (requires (fun h0 -> sel h0 x == 5 /\ satisfy x (prref_c)))
  (ensures (fun h0 r h1 -> (Inr? r \/ (Inl? r /\ Inl?.v r == 2)) /\ ((hrel_c) h0 h1)))

let f_xeq5_is_exportable : exportable_from c3p f_xeq5 _ =
  exportable_arrow c3p
    (ref int) int
    Leaf Leaf
    (fun x -> sst_pre (fun h0 -> sel h0 x == 5 /\ satisfy x (prref_c)))
    (fun x -> sst_post (resexn int) _ (fun h0 r h1 -> (Inr? r \/ (Inl? r /\ Inl?.v r == 2)) /\ ((hrel_c) h0 h1)))

let f_xeq5_spec : pck_spec =
  SpecErr00 true (ref ℤ) (safe_importable_is_importable c3p (ref ℤ) Leaf).c_styp (λ x → sst_pre (λ h0 → sel h0 x == 5 ∧ satisfy x prref_c)) ℤ
(exportable_refinement c3p ℤ Leaf (λ _ → l_True)).c_styp (λ x → sst_post (resexn ℤ) (λ h0 → sel h0 x == 5 ∧ satisfy x prref_c) (λ h0 r h1 → (Inr? r ∨ (Inl? r ∧ Inl?.v r == 2)) ∧ hrel_c h0 h1))

let f_xeq5_hoc : hoc c3p f_xeq5_spec =
  EnforcePre
    (fun rx ->
      let rx :ref int = rx in
      let eh0 = get_heap () in
      let check : cb_check c3p (ref int) _ (pre_poly_arrow c3p #(argt0 f_xeq5_spec) #(wt_argt0 f_xeq5_spec)) (fun x _ _ h1 -> (pre0 f_xeq5_spec) x h1) rx eh0 =
        (fun _ ->
          recall (contains_pred rx);
          if 5 = sst_read rx then Inl () else Inr (Contract_failure "x has changed")) in
      (| eh0, check |))
    (fun x r -> admit ())

let f_xeq5_pkhoc : pck_hoc c3p =
  (| f_xeq5_spec, f_xeq5_hoc |)

let f_xeq5_tree : hoc_tree c3p (Node f_xeq5_spec Leaf Leaf) =
  Node f_xeq5_pkhoc Leaf Leaf

val f_with_pre : f_xeq5
let f_with_pre x =
  recall (contains_pred x);
  let v = sst_read x in
  assert (v == 5);
  Inl (10 / v)

let f_with_dc = f_xeq5_is_exportable.export f_xeq5_tree f_with_pre

