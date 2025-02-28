module LinkedList

(* With `open FStar.Ref` and just using ref below we get *)
(* Inductive type `list` does not satisfy the strict positivity condition *)

(* However, the `mref` type in `FStar.Monotonic.Heap` is defined to
   be strictly positive, which makes the following code work: *)

open FStar.Monotonic.Heap
open FStar.Heap

noeq type linked (a:Type0) : Type0 =
  | Nil
  | Cons of a * ref (linked a)

open FStar.HyperStack.ST
(* -- not marked strictly_positive
  m_rref r (linked_list r a)
    (Heap.trivial_preorder (linked_list r a))
*)

assume val rref (r:erid) ([@@@ strictly_positive] a:Type0) : Type0

noeq type linked_list (r:erid) (a:Type0) : Type0 =
  | Nil0
  | Cons0 of a * rref r (linked_list r a)

(* module TS = FStar.TSet *)

(* noeq type linked_list2 (footprint:tset nat) (a:Type0) : Type0 = *)
(*   | Nil2 *)
(*   | Cons2 of a * r:(ref (linked_list2 (footprint `minus` addr_of r) a)){addr_of r `TS.mem` footprint} *)
