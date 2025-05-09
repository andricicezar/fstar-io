module Examples.HOC

open FStar.Ghost
open FStar.Monotonic.Heap
open FStar.Preorder
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Universe
open LabeledRefs
open HigherOrderContracts
open PolyIface
open Compiler
open Witnessable
open SpecTree

(** This files contains two examples **)

type f_eqx (a3p:threep) = x:ref int -> ST (resexn unit) (requires (fun h0 -> inv a3p h0 /\ satisfy x (prref a3p))) (ensures (fun h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1 /\ (Inr? r \/ sel h0 x == sel h1 x)))

let f_a3p (a3p:threep) : spec =
 (Spec false true (ref int) (witnessable_ref int)
    (fun x h0 -> inv a3p h0 /\ satisfy x (prref a3p))
    unit
    witnessable_unit
    (fun x h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1 /\ (Inr? r \/ sel h0 x == sel h1 x)))

let f_spec : spec = f_a3p c3p

let f_eqx_is_safe_importable a3p : safe_importable_to a3p (f_eqx a3p) (Node (U00 (f_a3p a3p)) Leaf Leaf) =
  safe_importable_arrow_err00 a3p
    (ref int) Leaf #(exportable_ref a3p int)
    unit Leaf #(safe_importable_is_importable a3p unit Leaf #(safe_importable_unit a3p))
    (fun x h0 -> inv a3p h0 /\ satisfy x (prref a3p))
    (fun x h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1 /\ (Inr? r \/ sel h0 x == sel h1 x))

let f_hoc : hoc c3p f_spec =
  EnforcePost
    (fun _ -> ())
    (fun _ _ -> ())
    (fun rx ->
      let rx :ref int = rx in
      recall (contains_pred rx);
      let x = lr_read rx in
      let eh0 = get_heap () in
      let check : cb_check c3p (ref int) (resexn unit) (fun x -> lr_pre (fun h0 -> satisfy x (prref_c))) (fun x -> lr_post _ _ (fun h0 r h1 -> Inr? r \/ sel h0 x == sel h1 x)) rx eh0 =
        (fun kres -> if x = lr_read rx then Inl () else Inr (Contract_failure "x has changed")) in
      (| eh0, check |))

let f_pkhoc : pck_uhoc c3p =
  (| U00 f_spec, U00hoc f_hoc |)

let f_tree : hoc_tree c3p (Node (U00 f_spec) Leaf Leaf) =
  Node f_pkhoc Leaf Leaf

let sit : src_interface1 = {
  specs = (fun a3p -> Node (U00 (f_a3p a3p)) Leaf Leaf);
  hocs = f_tree;
  ct = f_eqx;
  c_ct = f_eqx_is_safe_importable;
  psi = fun _ _ _ -> True
}

(**
val unsafe_f : mk_interm_arrow (ref int) (resexn unit)
let unsafe_f x =
  recall (contains_pred x);
  recall (is_shareable x);
  lr_write x 0;
  Inl ()**)

val some_ctx : ctx_tgt1 (comp_int_src_tgt1 sit)
let some_ctx read write alloc x =
  write x 0;
  Inl ()

val prog : prog_src1 sit
let prog f =
  let r = lr_alloc_shared #SNat 5 in
  witness (contains_pred r);
  witness (is_shareable r);
  match f r with
  | Inl () -> 0
  | Inr _ -> -1

(* Calling SecRef* on it *)

let compiled_prog =
  compile_pprog1 #sit prog

let whole_prog : whole_tgt1 =
  link_tgt1 compiled_prog some_ctx

let r = whole_prog ()
let _ =
  match r with
  | 0 -> FStar.IO.print_string "Success!\n"
  | -1 -> FStar.IO.print_string "Error!\n"
  | _ -> FStar.IO.print_string "Impossible\n"









type f_xeq5 (a3p:threep) =
  x:ref int -> ST (resexn int) 
    (requires (fun h0 -> sel h0 x == 5 /\ inv a3p h0 /\ satisfy x (prref a3p))) 
    (ensures (fun h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1 /\ (Inr? r \/ (Inl? r /\ Inl?.v r == 2))))

let f_xeq5_spec (a3p:threep) : spec =
  Spec true true
    (ref ℤ) (witnessable_ref int)
    (fun x h0 -> sel h0 x == 5 /\ inv a3p h0 /\ satisfy x (prref a3p))
    ℤ witnessable_int
    (fun x h0 r h1 -> inv a3p h1 /\ h0 `hrel a3p` h1 /\ (Inr? r \/ (Inl? r /\ Inl?.v r == 2)))

let f_xeq5_is_exportable a3p : exportable_from a3p (f_xeq5 a3p) (Node (U00 (f_xeq5_spec a3p)) Leaf Leaf) =
  exportable_arrow_err00 a3p
    (ref int) Leaf #(safe_importable_is_importable a3p _ Leaf #(safe_importable_ref a3p int))
    int Leaf #(exportable_int a3p)
    _ _

let f_xeq5_hoc : hoc c3p (f_xeq5_spec c3p) =
  EnforcePre
    (fun rx ->
      let rx :ref int = rx in
      let eh0 = get_heap () in
      let check : cb_check c3p (ref int) _ (pre_poly_arrow c3p #(f_xeq5_spec c3p).argt #(f_xeq5_spec c3p).wt_argt) (fun x _ _ h1 -> (f_xeq5_spec c3p).pre x h1) rx eh0 =
        (fun _ ->
          recall (contains_pred rx);
          if 5 = lr_read rx then Inl () else Inr (Contract_failure "x has changed")) in
      (| eh0, check |))
    (fun x r -> ())

let f_xeq5_pkhoc : pck_uhoc c3p =
  (| U00 (f_xeq5_spec c3p), U00hoc f_xeq5_hoc |)

let f_xeq5_tree : hoc_tree c3p (Node (U00 (f_xeq5_spec c3p)) Leaf Leaf) =
  Node f_xeq5_pkhoc Leaf Leaf

let sit2 : src_interface2 = {
  specs = (fun a3p -> Node (U00 (f_xeq5_spec a3p)) Leaf Leaf);
  hocs = f_xeq5_tree;
  pt = f_xeq5;
  c_pt = f_xeq5_is_exportable;
}

val prog2 : prog_src2 sit2
let prog2 x =
  recall (contains_pred x);
  let v = lr_read x in
  assert (v == 5);
  Inl (10 / v)

let compiled_prog2 =
  compile_pprog2 #sit2 prog2

val some_ctx2 : ctx_tgt2 (comp_int_src_tgt2 sit2)
let some_ctx2 _ _ alloc prog =
  let x : ref int = alloc 0 in
  match prog x with
  | Inr _ -> 0
  | Inl _ -> -1

let whole_prog2 : whole_tgt2 =
  link_tgt2 compiled_prog2 some_ctx2

let r2 = whole_prog2 ()
let _ =
  match r2 with
  | 0 -> FStar.IO.print_string "Success 2!\n"
  | -1 -> FStar.IO.print_string "Error 2!\n"
  | _ -> FStar.IO.print_string "Impossible 2!\n"

