module DisjointState

open FStar.Ref
open FStar.Ghost

assume val trp : Type0  // Type of the reference of the program (not shared)
assume val init_rp : trp

val targ : Type0  // Type not allowed to contain references, 
                  // since otherwise the program can share `rp` to the context.
let targ = unit   // Instantiated to unit to be able to use that it does not contain references
assume val tres : Type0

// Simple target types

// Target type of whole program
let t_tw : Type = ref trp -> St int

// Target type of context
let t_tc : Type = targ -> St tres

// Target type of program -- has initial control, calls context
let t_tp : Type = ref trp -> t_tc -> St int

let t_link (t_p:t_tp) (t_c:t_tc) : t_tw =
  fun (rp:ref trp) ->
    t_p rp (t_c) (* <-- rp is not passed to the context *)

// Refined source types (pre- and post-conditions on stateful functions)

assume val post_prog : ref trp -> heap -> int -> heap -> Type0
// <- user defined and proved statically about the partial program

let s_tw : Type = rp:ref trp ->
  ST int (requires (fun h0 -> True))
         (ensures (fun h0 res h1 -> post_prog rp h0 res h1))

assume val pre_ctx : targ -> heap -> Type0
// <- user defined and proved statically about the partial program (who calls context)

assume val post_ctx : targ -> heap -> tres -> heap -> Type0
// dynamically enforced when the context returns control back to the program

(** Cezar: This is similar to what we have in POPL'24 as contracts (section 4.3) **)
assume val ck_post_ctx : arg:targ -> ST 
  (h0:(erased heap) & (res:tres -> ST bool (requires (fun _ -> True)) (ensures (fun h0' b h1 -> h0' == h1 /\ (b <==> post_ctx arg h0 res h1)))))
  (requires (fun _ -> True)) (requires (fun h0 (| h0', _ |) h1 -> h0 == h1 /\ h0 == reveal h0'))
(** Cezar: the current spec says that the contract does not modify the heap (in other words, it only reads from the heap) .
           Is this spec strong enough? Are there cases where we would like a weaker spec?
    Here is an example on how to check if rs is unchanged: 
      fun rs arg -> 
        let saved_rs = !rs in
        let h0 = hide (gst_get ()) in
        (| h0, (fun res -> saved_rs = !rs) |)
**)

let s_tc (rp:ref trp) : Type = arg:targ ->
  ST tres (requires (fun h0 -> h0 `contains` rp /\ pre_ctx arg h0))
          (ensures (fun h0 res h1 -> 
            post_ctx arg h0 res h1 // <- dynamically enforced
            /\ sel h0 rp == sel h1 rp)) // <- enforced by state separation

// putting together the types + specs above
let s_tp : Type = rp:ref trp ->
  s_tc rp ->
  ST int (requires (fun h0 -> True))
         (ensures (fun h0 res h1 -> post_prog rp h0 res h1))

// Problem: had to change order of arguments to use rp in context type
//          (so this doesn't return a s_tw)
let s_link (s_p:s_tp) (rp:ref trp) (s_c:s_tc rp) :
  ST int (requires (fun h0 -> True))
         (ensures (fun h0 res h1 -> post_prog rp h0 res h1)) =
  s_p rp s_c

// Solution using erased references
let se_tc : Type = erp:erased (ref trp) -> s_tc erp

let se_link (s_p:s_tp) (s_c:se_tc) : s_tw =
  fun (rp:ref trp) ->
    s_p rp (s_c rp) (* rp passed to the context, but only as `erased` argument *)

val gst_get' : unit    -> GST (erased heap) (fun p h0 -> p h0 (reveal h0))
let gst_get' () = let h = gst_get () in hide h

val strengthen : rp:ref trp -> (targ -> St tres) -> s_tc rp
let strengthen rp (t_c:targ -> St tres) arg =
  let h0 = gst_get' () in
  let (| _, ck |) = ck_post_ctx arg in
  let res = t_c arg in
  let h1 = gst_get' () in 
  recall rp; // monotonicity of the heap
  assume (sel h0 rp == sel h1 rp); // TODO: seems hard
  if ck res
  then res
  else admit() // TODO: signal error :) 

let compile (s_p:s_tp) : t_tp =
  fun rp t_c -> 
    let s_c = strengthen rp t_c in
    let h0 = gst_get' () in
    s_p rp s_c

// Cezar: I suppose the initial separation will come from linking, where one
// allocates the two references. However, this involves adding a pre-condition to t_tp.

// refined t_tp
let t_rtp : Type = rp:ref trp -> (targ -> St tres) ->
  ST int (requires (fun h0 -> True))
         (ensures (fun _ _ _ -> True))

let t_alloc_and_link (t_p:t_rtp) (t_c:t_tc) : unit -> St int =
  fun () ->
    let rp : ref trp = alloc init_rp in
    t_link t_p t_c rp
