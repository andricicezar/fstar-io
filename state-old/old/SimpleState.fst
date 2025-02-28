module SimpleState

open FStar.Ref

assume val trp : Type0  // Type of the reference of the program (not shared)
assume val init_rp : trp
assume val trs : Type0  // Type of the reference *shared* between program and context
                        // <- for now let's assume this is not refined
                        // (assumed for all the types here, since they are used in target)
assume val init_rs : trs
assume val targ : Type0 // Type not allowed to contain references,
                        // since otherwise the program can share `rp` to the context.
assume val tres : Type0

// Simple target types

// Target type of whole program
let t_tw : Type = ref trp -> ref trs -> St int

// Target type of context
let t_tc : Type = ref trs -> targ -> St tres

// Target type of program -- has initial control, calls context
let t_tp : Type = ref trp -> ref trs -> (targ -> St tres) -> St int

let t_link (t_p:t_tp) (t_c:t_tc) : t_tw =
  fun (rp:ref trp) (rs:ref trs) ->
    t_p rp rs (t_c rs) (* <-- rp is not passed to the context *)

// Refined source types (pre- and post-conditions on stateful functions)

// This separation invariant used for both program and context
let sep (rp:ref trp) (rs:ref trs) (h:heap) : Type0 =
  (* initial references are not aliasing: (what hyper-heap regions could give us?) *)
  addr_of rp <> addr_of rs /\
  (* initial references are allocated: *)
  h `contains` rp /\ h `contains` rs
  (* + TODO (hard in general!?): rp is not reachable from rs *)
  (* Does this kind of (un)reachability (deep/transitive) already lead us to
     separation logic, or is there anything we can do in a simpler setting. *)
  (* Otherwise can define unreachability predicate for specific types like
     linked lists *)

assume val post_prog : ref trp -> ref trs -> heap -> int -> heap -> Type0
// <- user defined and proved statically about the partial program

let s_tw : Type = rp:ref trp -> rs:ref trs ->
  ST int (requires (fun h0 -> sep rp rs h0))
         (ensures (fun h0 res h1 -> post_prog rp rs h0 res h1))

assume val pre_ctx : ref trs -> targ -> heap -> Type0
// <- user defined and proved statically about the partial program (who calls context)

assume val post_ctx : ref trs -> targ -> heap -> tres -> heap -> bool
// dynamically enforced when the context returns control back to the program
// (so for now going directly to bool)
// - The use of gst_get in a non-ghost context will cause extraction problems later
// - Saner longer term alternative :
//   look only at value of rs in initial and final heap?
open FStar.Ghost
(** Cezar: This is similar to what we have in POPL'24 as contracts (section 4.3) **)
assume val ck_post_ctx : rs:ref trs -> arg:targ -> ST 
  (h0:(erased heap) & (res:tres -> ST bool (requires (fun _ -> True)) (ensures (fun h0' b h1 -> h0' == h1 /\ (b <==> post_ctx rs arg h0 res h1)))))
  (requires (fun _ -> True)) (requires (fun h0 (| h0', _ |) h1 -> h0 == h1 /\ h0 == reveal h0'))
(** Cezar: the current spec says that the contract does not modify the heap (in other words, it only reads from the heap) .
           Is this spec strong enough? Are there cases where we would like a weaker spec?
    Here is an example on how to check if rs is unchanged: 
      fun rs arg -> 
        let saved_rs = !rs in
        let h0 = hide (gst_get ()) in
        (| h0, (fun res -> saved_rs = !rs) |)
**)

let s_tc (rp:ref trp) : Type = rs:ref trs -> arg:targ ->
  ST tres (requires (fun h0 -> sep rp rs h0 /\ pre_ctx rs arg h0))
          (ensures (fun h0 res h1 -> sep rp rs h1 // <- necessarily preserved by context
            /\ post_ctx rs arg h0 res h1 // <- dynamically enforced
            /\ sel h0 rp == sel h1 rp)) // <- enforced by state separation

// putting together the types + specs above
let s_tp : Type = rp:ref trp -> rs:ref trs ->
  (arg:targ -> ST tres (requires (fun h0 -> sep rp rs h0 /\ pre_ctx rs arg h0))
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

let se_tc : Type = erp:erased (ref trp) -> rs:ref trs -> arg:targ ->
  ST tres (requires (fun h0 -> sep erp rs h0 /\ pre_ctx rs arg h0))
          (ensures (fun h0 res h1 -> sep erp rs h1 // <- necessarily preserved by context
            /\ post_ctx rs arg h0 res h1 // <- dynamically enforced
            /\ sel h0 erp == sel h1 erp)) // <- enforced by state separation
                                          // TODO: very specific, e.g. for ref int

let se_link (s_p:s_tp) (s_c:se_tc) : s_tw =
  fun (rp:ref trp) (rs:ref trs) ->
    s_p rp rs (s_c rp rs) (* rp passed to the context, but only as `erased` argument *)

val gst_get' : unit    -> GST (erased heap) (fun p h0 -> p h0 (reveal h0))
let gst_get' () = let h = gst_get () in hide h

let compile (s_p:s_tp) : t_tp =
  fun rp rs t_c -> 
    let s_c arg : ST tres (requires (fun h0 -> sep rp rs h0 /\ pre_ctx rs arg h0))
                          (ensures (fun h0 res h1 -> sep rp rs h1
                          /\ post_ctx rs arg h0 res h1
                          /\ sel h0 rp == sel h1 rp)) =
      let h0 = gst_get' () in
      assert (h0 `contains` rp /\ h0 `contains` rs);
      let (| _, ck |) = ck_post_ctx rs arg in
      let res = t_c arg in
      let h1 = gst_get' () in 
      recall rp; // monotonicity of the heap
      recall rs; // monotonicity of the heap
      assert (sep rp rs h1);
      assume (sel h0 rp == sel h1 rp); // TODO: seems hard
      if ck res
      then res
      else admit() // TODO: signal error :)
    in
    let h0 = gst_get' () in
    assume (sep rp rs h0); // TODO: where would one get initial separation from?
    s_p rp rs s_c

// Cezar: I suppose the initial separation will come from linking, where one
// allocates the two references. However, this involves adding a pre-condition to t_tp.

// refined t_tp
let t_rtp : Type = rp:ref trp -> rs:ref trs -> (targ -> St tres) ->
  ST int (requires (fun h0 -> sep rp rs h0))
         (ensures (fun _ _ _ -> True))

let t_alloc_and_link (t_p:t_rtp) (t_c:t_tc) : unit -> St int =
  fun () ->
    let rp : ref trp = alloc init_rp in
    let rs : ref trs = alloc init_rs in
      t_p rp rs (t_c rs) (* <-- rp is not passed to the context *)
