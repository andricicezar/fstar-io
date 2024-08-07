module SimpleStateModifies

open FStar.Ghost
open FStar.Tactics

open FStar.Ref

open FStar.ST

assume val trp : Type0  // Type of the reference of the program (not shared)
assume val init_rp : trp
assume val fp_rp : ref trp -> heap -> GTot (Set.set nat)
assume val trs : Type0  // Type of the reference *shared* between program and context
                        // <- for now let's assume this is not refined
                        // (assumed for all the types here, since they are used in target)
assume val fp_rs : ref trs -> heap -> GTot (Set.set nat)
assume val init_rs : trs
assume val targ : Type0 // Type not allowed to contain references,
                        // since otherwise the program can share `rp` to the context.
assume val tres : Type0


// This separation invariant used for both program and context
let sep (rp:ref trp) (rs:ref trs) (h:heap) : Type0 = // TODO: does this have to depend on the heap?
  Set.disjoint (fp_rp rp h) (fp_rs rs h)

// Simple target types

// Target type of whole program (now includes sep as precondition)
let t_tw : Type = rp:ref trp -> rs:ref trs -> ST int (fun h0 -> sep rp rs h0) (fun _ _ _ -> True)

// Target type of context
type t_tc' (rs:ref trs) = targ -> ST tres (fun _ -> True) (fun h0 _ h1 -> 
  modifies (fp_rs rs h0) h0 h1 /\
  equal_dom h0 h1)
type t_tc = rs:ref trs -> t_tc' rs

// Target type of program -- has initial control, calls context
type t_tp = rp:ref trp -> rs:ref trs -> t_tc' rs -> ST int (fun h0 -> sep rp rs h0) (fun _ _ _ -> True)

val t_link : t_tp -> t_tc -> t_tw
let t_link t_p t_c rp rs =
    t_p rp rs (t_c rs) (* <-- rp is not passed to the context *)

// Refined source types (pre- and post-conditions on stateful functions)

assume val post_prog : ref trp -> ref trs -> heap -> int -> heap -> Type0
// <- user defined and proved statically about the partial program

type s_tw = rp:ref trp -> rs:ref trs ->
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
type s_tc' (rs:ref trs) = arg:targ ->
  ST tres (requires (fun h0 -> pre_ctx rs arg h0))
          (ensures (fun h0 res h1 ->
            (* TODO: add back `sep rp rs h1`, which also needs erased rp -> *)
            modifies (fp_rs rs h0) h0 h1 /\
            equal_dom h0 h1 /\
            post_ctx rs arg h0 res h1)) 

type s_tc = rs:ref trs -> s_tc' rs

// putting together the types + specs above
type s_tp = rp:ref trp -> rs:ref trs ->s_tc' rs ->
  ST int (requires (fun h0 -> sep rp rs h0))
        (ensures (fun h0 res h1 -> post_prog rp rs h0 res h1))

val s_link : s_tp -> s_tc -> s_tw
let s_link (s_p:s_tp) (s_c:s_tc) (rp:ref trp) (rs:ref trs) :
  ST int (requires (fun h0 -> sep rp rs h0))
         (ensures (fun h0 res h1 -> post_prog rp rs h0 res h1)) =
  s_p rp rs (s_c rs)

val strengthen : rp:ref trp -> rs:(ref trs) -> t_tc' rs ->  ST (s_tc' rs) 
  (requires (fun h -> sep rp rs h)) (ensures (fun h0 r h1 -> sep rp rs h1))
let strengthen rp rs t_c arg :
  ST tres (requires (fun h0 -> pre_ctx rs arg h0))
          (ensures (fun h0 res h1 ->
            modifies (fp_rs rs h0) h0 h1 /\
            equal_dom h0 h1 /\
            post_ctx rs arg h0 res h1)) =
  let (| _, ck |) = ck_post_ctx rs arg in
  let res = t_c arg in
  let h = gst_get () in
  (* assert (sep rp rs h); -- doesn't hold now once sep ... rs h depends on h *)
  if ck res
  then res
  else admit() // TODO: signal error :) 

val compile : s_tp -> t_tp
let compile (s_p:s_tp) rp rs t_c =
    let s_c = strengthen rp rs t_c in
    s_p rp rs s_c

// Cezar: I suppose the initial separation will come from linking, where one
// allocates the two references. However, this involves adding a pre-condition to t_tp.

// refined t_tp
let t_rtp : Type = rp:ref trp -> rs:ref trs -> (targ -> St tres) ->
  ST int (requires (fun h0 -> sep rp rs h0))
         (ensures (fun _ _ _ -> True))

val t_alloc_and_link : t_rtp -> t_tc -> unit -> St int
let t_alloc_and_link t_p t_c () : St int =
  let rp : ref trp = alloc init_rp in
  let rs : ref trs = alloc init_rs in
  let h = gst_get () in
  assume (sep rp rs h);
  t_p rp rs (t_c rs)

// Example 1: rp: ref ref int, rs: ref int
val ctx : rs:ref int -> unit -> ST unit (requires (fun _ -> True)) 
                                        (ensures (fun h0 _ h1 -> modifies (only rs) h0 h1)) 
let ctx rs () = rs := !rs + 1

// Define separation operator
val sep': ref (ref int) -> ref int -> heap -> Type0
let sep' rp rs h =
  let fp_rp = ((only rp) `Set.union` (only (sel h rp))) in 
  let fp_rs = only rs in
  (h `contains` rp /\ h `contains` (sel h rp)) /\
  (h `contains` rs) /\
  Set.disjoint fp_rp fp_rs

val progr: rp: ref (ref int) -> rs: ref int -> 
          (unit -> ST unit (requires (fun _ -> True)) 
                            (ensures (fun h0 _ h1 -> 
                            modifies (only rs) h0 h1)))  -> 
           ST int (requires (fun h0 -> sep' rp rs h0))
                  (ensures (fun _ _ _ -> True))
                  
let progr rp rs f = 
  // rp := rs;
  f ();
  let h1 = gst_get () in
  // recall rp; recall rs;
  // let x = sel h1 rp in 
    // recall x;
  assert (Set.disjoint ((only rp)) (only rs));
  assert (Set.disjoint (only (sel h1 rp)) (only rs));
  !(!rp)

module TS = FStar.TSet

val modifies_preserves_sep (rp: ref (ref int)) (rs: ref int) (h0 h1: heap): 
  Lemma
    (requires (sep' rp rs h0 /\ modifies (only rs) h0 h1))
    (ensures (sep' rp rs h1))
let modifies_preserves_sep rp rs h0 h1 = ()

val whole: unit -> St int
let whole () =
  let rp : ref (ref int) = alloc (alloc 0) in
  let rs : ref int = alloc 1 in  
  progr rp rs (ctx rs)

// let test () : St unit = 
//   let x = whole () in
//   assert (x == 2) by (norm [delta_only [`%whole;`%progr;`%ctx];zeta;iota]; dump "h")

// val ctx': 

// Example 2: rs: ref ref int, rp: ref int
val sep'': ref int -> ref (ref int) -> heap -> Type0
let sep'' rp rs h =
  let fp_rs = ((only rs) `Set.union` (only (sel h rs))) in 
  let fp_rp = only rp in
  (h `contains` rs /\ h `contains` (sel h rs)) /\
  (h `contains` rp) /\
  Set.disjoint fp_rp fp_rs

val modifies_preserves_sep'' (rs: ref (ref int)) (rp: ref int) (h0 h1: heap): 
  Lemma
    (requires (
      let fp_rs_h1 = ((only rs) `Set.union` (only (sel h1 rs))) in 
      let fp_rs_h0 = ((only rs) `Set.union` (only (sel h0 rs))) in 
      (sep'' rp rs h0 /\ modifies fp_rs_h0 h0 h1) /\
      equal_dom h0 h1 /\
      (h1 `contains` (sel h1 rs))
    ))
    (ensures (sep'' rp rs h1))
  let modifies_preserves_sep'' rs rp h0 h1 =
   ()

val progr'': rp: ref int -> rs: ref (ref int) -> 
          (unit -> ST unit (requires (fun h0 ->  (h0 `contains` rs /\ h0 `contains` (sel h0 rs)))) 
                            (ensures (fun h0 _ h1 -> 
                            sep'' rp rs h1 /\
                            modifies ((only rs) `Set.union` (only (sel h0 rs))) h0 h1 /\
                            equal_dom h0 h1 /\ 
                            (h1 `contains` rs /\ h1 `contains` (sel h1 rs))
                            )))  -> 
           ST unit (requires (fun h0 -> sep'' rp rs h0))
                  (ensures (fun _ _ h1 -> sep'' rp rs h1))
                  
let progr'' rp rs f = 
  f ();
  let h1 = gst_get () in
  assume ((ref int) =!= int);
  let fp_rs = ((only rs) `Set.union` (only (sel h1 rs))) in 
  let fp_rp = only rp in
  // assert (sel h1 rs =!= rp);
  assert (Set.disjoint fp_rp fp_rs);
  ()

let ctx'' (rs:ref (ref int)) () : 
  ST unit 
    (requires (fun h0 -> h0 `contains` rs /\ h0 `contains` (sel h0 rs))) 
    (ensures (fun h0 _ h1 -> 
      let fp_rs_h1 = ((only rs) `Set.union` (only (sel h1 rs))) in 
      let fp_rs_h0 = ((only rs) `Set.union` (only (sel h0 rs))) in 
      modifies fp_rs_h0 h0 h1 /\
      equal_dom h0 h1 /\
      (h1 `contains` rs) /\
      (h1 `contains` (sel h1 rs)))) =
  let rs' = !rs in
  
  let v = !rs' + 1 in
  let h0 = gst_get () in
  write rs' v;
  let h1 = gst_get () in
  
  assume ((ref int) =!= int);
  lemma_distinct_addrs_distinct_types #(ref int) #int h0 rs rs';
  assert (!{sel h0 rs} `Set.disjoint` !{rs});
  assert (equal_dom h0 h1);
  lemma_modifies_and_equal_dom_sel_diff_addr !{sel h0 rs} h0 h1 rs;
  assert (sel h0 rs == sel h1 rs);
  assert (h0 `contains` (sel h0 rs));
  lemma_upd_contains h0 rs' v;


  assert (h1 `contains` (sel h1 rs))
