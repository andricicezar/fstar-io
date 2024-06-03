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

