module SimpleStateSL

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

assume val trp : Type0  // Type of the reference of the program (not shared)
assume val init_rp : trp
assume val trs : Type0  // Type of the reference *shared* between program and context
                        // <- for now let's assume this is not refined
                        // (assumed for all the types here, since they are used in target)
assume val init_rs : trs
assume val targ : Type0  // Type not allowed to contain references, 
                         // since otherwise the program can share `rp` to the context.
assume val tres : Type0

// Simple target types

// Target type of whole program
let t_tw : Type = rp:ref trp -> rs:ref trs ->
  SteelT int (vptr rp `star` vptr rs) (fun _ -> vptr rp `star` vptr rs) // why does it give back ownership of rp?

// Target type of context
type t_tc' (rs:ref trs) = targ -> SteelT tres
  (vptr rs)
  (fun (_:tres) -> vptr rs) // the context has to free everything that it allocates. (similar to mode locality)
  // this is a strong post-condition

type t_tc = rs:ref trs -> t_tc' rs
  
// to avoid freeing its allocations, the context can return a reference to them + ownership
// let t_tc' : Type = targ -> SteelT (ref tres) emp (fun rr -> vptr rr)


// Target type of program -- has initial control, calls context
let t_tp : Type = rp:ref trp -> rs:ref trs -> t_tc' rs ->
  SteelT int (vptr rp `star` vptr rs) (fun _ -> vptr rp `star` vptr rs)

let t_link (t_p:t_tp) (t_c:t_tc) : t_tw =
  fun rp rs ->
    t_p rp rs (t_c rs) (* <-- rp is not passed to the context *)

let s_tw : Type = rp:ref trp -> rs:ref trs ->
  Steel int 
    (* slprops *)
    (vptr rp `star` vptr rs)            (* initial ownership *)
    (fun _ -> vptr rp `star` vptr rs)   (* returned ownership (?) *)
    (* selector predicates *)
    (requires (fun _ -> True))     (* pre-condition over the initial owned references (?) *)
    (ensures (fun _ _ _ -> True)) 

type s_tc (rp:ref trp) (rs:ref trs) = targ ->
  Steel tres
    (vptr rp `star` vptr rs) (fun _ -> vptr rp `star` vptr rs)
    (requires (fun _ -> True))
    (ensures (fun s0 _ s1 -> sel rp s0 == sel rp s1))  (** this post is a "selector predicate", i.e. it can state things only about the things in the frame **)

(** Source Contexts are statically verified.
    The post states that at the end of the execution, the state is equal to the original state.
    0) The equality between `sel`s is shallow, i.e. it does not work for a linked list
    1) This is not a proper way to state integrity since in a HO setting the context could change rp, call a callback, and then rollback the changes.
    2) Also, not clear how to state confidentiality: the context could read the value of rp, and leak it through some other effect.
    So passing `rp` to the source context is silly. It is here just to show that we can define `strengthen` later. **)
// Example of violating integrity in HO case.
// let ctx cb =
//   rp := forge _;
//   rp := 1 - (!rp);
//   cb(); <- the program expects rp to not have changed
//   rp := 1 - (!rp);
// { sel rp s0 == sel rp s1 }


// putting together the types + specs above
let s_tp : Type = rp:ref trp -> rs:ref trs ->
  s_tc rp rs ->
  Steel int
    (vptr rp `star` vptr rs) (fun _ -> vptr rp `star` vptr rs)
    (requires (fun h0 -> True))
    (ensures (fun s0 res s1 -> True))

let s_link (s_p:s_tp) (rp:ref trp) (rs:ref trs) (s_c:s_tc rp rs) :
  Steel int
          (vptr rp `star` vptr rs) (fun _ -> vptr rp `star` vptr rs)
          (requires (fun h0 -> True))
          (ensures (fun s0 res s1 -> True)) =
  s_p rp rs s_c

val strengthen : #rp:ref trp -> #rs:ref trs -> t_tc' rs -> s_tc rp rs
let strengthen t_c arg =
  t_c arg

let compile (s_p:s_tp) : t_tp =
  fun rp rs t_c -> 
    s_p rp rs (strengthen t_c)


module G = FStar.Ghost

val ctx' : 
  rs:ref int ->
  unit -> 
  SteelT unit (vptr rs) (fun _ -> vptr rs)
let ctx' rs () =
  let v = read rs in
  write rs (v + 1)


val prog' : 
  rp:ref (ref int) ->
  (r: G.erased (ref int)) ->
  rs:ref int -> 
  ctx:(unit -> SteelT unit (vptr rs) (fun _ -> vptr rs)) ->
  Steel int
    (vptr rp `star` vptr (G.reveal r) `star` vptr rs)
    (fun _ -> vptr rp `star` vptr (G.reveal r) `star` vptr rs)
    (requires fun h0 ->
      let rp_content = sel rp h0 in
      rp_content == G.reveal r)
    (ensures fun _ _ _ -> True)
let prog' rp r rs ctx =
  write rp rs; // <-- the program considers the shared state as its internal state
  ctx ();
  let rp' = read rp in
  change_equal_slprop (vptr rs) (vptr rp');
  let result = read rp' in
  change_equal_slprop (vptr rp') (vptr rs);
  return result



let whole' () : SteelT int emp (fun _ -> emp) =
  let rp' = malloc 0 in
  let rp = malloc rp' in
  let rs = malloc 0 in
  let r = prog' rp rp' rs (ctx' rs) in
  free rs;
  free rp';
  free rp;
  r // <-- this is 1 and it should be 0



val prog : 
  rp:ref int ->
  rs:ref (ref int) ->
  (r: G.erased (ref int)) -> 
  ctx:((r': G.erased (ref int)) -> Steel unit 
                (vptr rs `star` vptr (G.reveal r')) 
                (fun _ -> vptr rs `star` vptr (G.reveal r'))
                (requires fun h0 ->
                  let rs' = sel rs h0 in
                  rs' == G.reveal r')
                (ensures fun _ _ _ -> True)) ->
  Steel int
    (vptr rp `star` vptr (G.reveal r) `star` vptr rs)
    (fun _ -> vptr rp `star` vptr (G.reveal r) `star` vptr rs)
    (requires fun h0 ->
      let rs' = sel rs h0 in
      rs' == G.reveal r)
    (ensures fun _ _ _ -> True)
let prog rp rs r ctx =
  write rs rp; // <-- the program puts a reference to its internal state in the shared state
  ctx rp;
  return (read rp)

val ctx :
  rs:ref (ref int) ->
  r': G.erased (ref int) -> 
  Steel unit 
    (vptr rs `star` vptr (G.reveal r')) 
    (fun _ -> vptr rs `star` vptr (G.reveal r'))
    (requires fun h0 ->
      let rs' = sel rs h0 in
      rs' == G.reveal r')
    (ensures fun _ _ _ -> True)
let ctx rs r' =
  let rs' = read rs in
  change_equal_slprop  (vptr (G.reveal r')) (vptr rs');
  let result = read rs' in
  write rs' (result + 1);
  change_equal_slprop (vptr rs') (vptr (G.reveal r'));
  ()

let whole () : SteelT int emp (fun _ -> emp) =
  let rp = malloc 0 in
  let rs' = malloc 0 in
  let rs = malloc rs' in
  let r = prog rp rs rs' (ctx rs) in
  free rs;
  free rs';
  free rp;
  r // <-- this is 1 and it should be 0