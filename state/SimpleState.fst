module SimpleState

open FStar.Ref

assume val trp : Type // Type of the reference of the program (not shared)
assume val trs : Type // Type of the reference *shared* between program and context
                      // <- for now let's assume this is not refined
assume val t1 : Type  // Type not allowed to contain references,
                      // since otherwise the program can share `rp` to the context.
assume val t2 : Type

// Simple target types

// Target type of whole program
let t_tw : Type = ref trp -> ref trs -> St int

// Target type of context
let t_tc : Type = ref trs -> t1 -> St t2

// Target type of program -- has initial control, calls context
let t_tp : Type = ref trp -> ref trs -> (t1 -> St t2) -> St int

let t_link (t_p:t_tp) (t_c:t_tc) : t_tw =
  fun (rp:ref trp) (rs:ref trs) ->
    t_p rp rs (t_c rs)

// Refined source types

// This separation invariant used for both program and context
let sep (rp:ref trp) (rs:ref trs) (h0:heap) : Type0 =
  (* initial references are not aliasing: (what hyper-heap regions could give us?) *)
  addr_of rp <> addr_of rs /\
  (* initial references are allocated: *)
  h0 `contains` rp /\ h0 `contains` rs
  (* + TODO (hard in general!?): rp is not reachable from rs *)

assume val post_prog : ref trp -> ref trs -> heap -> int -> heap -> Type0
// <- user defined and proved statically about the partial program

let s_tw : Type = rp:ref trp -> rs:ref trs ->
  ST int (requires (fun h0 -> sep rp rs h0))
         (ensures (fun h0 res h1 -> post_prog rp rs h0 res h1))

assume val pre_ctx : ref trs -> t1 -> heap -> Type0
// <- user defined and proved statically about the partial program (who calls context)

assume val post_ctx : ref trs -> t1 -> heap -> t2 -> heap -> bool
// dynamically enforced when the context returns control back to the program
// (so for now going directly to bool)

let s_tc (rp:ref trp) : Type = rs:ref trs -> arg:t1 ->
  ST t2 (requires (fun h0 -> sep rp rs h0 /\ pre_ctx rs arg h0))
        (ensures (fun h0 res h1 -> sep rp rs h1 // <- necessarily preserved by context
          /\ post_ctx rs arg h0 res h1 // <- dynamically enforced
          /\ sel h0 rp == sel h1 rp)) // <- enforced by state separation

// putting together the types + specs above
let s_tp : Type = rp:ref trp -> rs:ref trs ->
  (arg:t1 -> ST t2 (requires (fun h0 -> sep rp rs h0 /\ pre_ctx rs arg h0))
                   (ensures (fun h0 res h1 -> sep rp rs h1
                     /\ post_ctx rs arg h0 res h1
                     /\ sel h0 rp == sel h1 rp))) ->
  ST int (requires (fun h0 -> sep rp rs h0))
         (ensures (fun h0 res h1 -> post_prog rp rs h0 res h1))

// Problem: had to change order of arguments to use rp in context type
//          (so this doesn't return a s_tw)
let s_link (s_p:s_tp) (rp:ref trp) (s_c:s_tc rp) (rs:ref trs) :
  ST int (requires (fun h0 -> sep rp rs h0))
         (ensures (fun h0 res h1 -> post_prog rp rs h0 res h1)) =
  s_p rp rs (s_c rs)

// Solution using erased references

open FStar.Ghost

let se_tc : Type = erp:erased (ref trp) -> rs:ref trs -> arg:t1 ->
  ST t2 (requires (fun h0 -> sep erp rs h0 /\ pre_ctx rs arg h0))
        (ensures (fun h0 res h1 -> sep erp rs h1 // <- necessarily preserved by context
          /\ post_ctx rs arg h0 res h1 // <- dynamically enforced
          /\ sel h0 erp == sel h1 erp)) // <- enforced by state separation

let se_link (s_p:s_tp) (s_c:se_tc) : s_tw =
  fun (rp:ref trp) (rs:ref trs) ->
    s_p rp rs (s_c rp rs)
