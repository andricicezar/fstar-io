module DisjointStateSL

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

assume val trp : Type0  // Type of the reference of the program (not shared)
assume val init_rp : trp

assume val targ : Type0  // Type not allowed to contain references, 
                         // since otherwise the program can share `rp` to the context.
assume val tres : Type0

// Simple target types

// Target type of whole program
let t_tw : Type = rp:ref trp -> SteelT int (vptr rp) (fun _ -> vptr rp)

// Target type of context
let t_tc : Type = targ -> SteelT tres emp (fun _ -> emp)

// Target type of program -- has initial control, calls context
let t_tp : Type = rp:ref trp -> t_tc -> SteelT int (vptr rp) (fun _ -> vptr rp)

let t_link (t_p:t_tp) (t_c:t_tc) : t_tw =
  fun (rp:ref trp) ->
    t_p rp (t_c) (* <-- rp is not passed to the context *)

// Refined source types (pre- and post-conditions on stateful functions)

let s_tw : Type = rp:ref trp ->
  Steel int (vptr rp) (fun _ -> vptr rp)
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> True))

type s_tc (rp:ref trp) = targ ->
  Steel tres
    (vptr rp) (fun _ -> vptr rp)
    (requires (fun _ -> True))
    (ensures (fun s0 _ s1 -> sel rp s0 == sel rp s1))  (** this post is a "selector predicate", i.e. it can state things only about the things in the frame **)
(** Source Contexts are statically verified.
    The post states that at the end of the execution, the state is equal to the original state.
    This is not a proper way to state integrity since in a HO setting the context could change rp, call a callback, and then rollback the changes.
    Also, not clear how to state confidentiality: the context could read the value of rp, and leak it through some other effect.
    So passing `rp` to the source context is silly. It is here just to show that we can define `strengthen` later. **)

// putting together the types + specs above
let s_tp : Type = rp:ref trp ->
  s_tc rp ->
  Steel int
    (vptr rp) (fun _ -> vptr rp)
    (requires (fun h0 -> True))
    (ensures (fun s0 res s1 -> True))

let s_link (s_p:s_tp) (rp:ref trp) (s_c:s_tc rp) :
  Steel int
          (vptr rp) (fun _ -> vptr rp)
          (requires (fun h0 -> True))
          (ensures (fun s0 res s1 -> True)) =
  s_p rp s_c

val strengthen : rp:ref trp -> t_tc -> s_tc rp
let strengthen rp t_c arg =
  t_c arg

let compile (s_p:s_tp) : t_tp =
  fun rp t_c -> 
    s_p rp t_c

val somec : int -> SteelT int emp (fun _ -> emp)
let somec x =
    let r = malloc 0 in
    // Writing value 2 in the newly allocated reference
    write r 2;
    // Reading value of r in memory. This was set to 2 just above
    let v = read r in
    // Freeing reference r
    free r;
    // The returned value is equal to 1, the context is now empty
    v - 1
